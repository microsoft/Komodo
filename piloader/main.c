#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define assert(expression) \
    do { if(!(expression)) { \
        console_printf("Assertion failed: " _PDCLIB_symbol2string(expression)\
                         ", function ", __func__,                         \
                         ", file " __FILE__ \
                         ", line " _PDCLIB_symbol2string( __LINE__ ) \
                         "." _PDCLIB_endl ); \
        while(1);                          \
      } \
    } while(0)

#include "serial.h"
#include "console.h"
#include "atags.h"
#include "rng.h"
#include <komodo/armpte.h>
#include <komodo/memregions.h>

#define ROUND_UP(N, S) ((((N) + (S) - 1) / (S)) * (S))

#define ARM_SCTLR_M     0x1 /* MMU enable */
#define ARM_SCTLR_V     0x2000 /* vectors base (high vs VBAR) */
#define ARM_SCTLR_VE    0x1000000 /* interrupt vectors enable */
#define ARM_SCTLR_TRE   (1UL << 28) /* TEX remap enable */
#define ARM_SCTLR_AFE   (1UL << 29) /* access flag enable -- simplified PTEs */

#define ARM_SCR_NS      0x01 // non-secure bit

// defined in linker script
extern char monitor_image_start, monitor_image_data, monitor_image_bss,
    monitor_image_end;
// defined in monitor image
extern char monitor_stack_base, _monitor_vectors, _secure_vectors,
    g_monitor_physbase, g_secure_physbase, g_rngbase;

void park_secondary_cores(void);
void leave_secure_world(void);

static inline uint8_t mycoreid(void)
{
    uint32_t val;
    __asm("mrc p15, 0, %0, c0, c0, 5" : "=r" (val));
    return val & 0xff;
}

extern void print_hex(uint32_t val);

static void secure_world_init(uintptr_t ptbase, uintptr_t vbar, uintptr_t mvbar,
                              uintptr_t mon_sp)
{
    uint32_t reg;

    __asm volatile("mrc p15, 0, %0, c2, c0, 0" : "=r" (reg));
    console_printf("Initial secure TTBR0: %lx\n", reg);
    __asm volatile("mrc p15, 0, %0, c2, c0, 1" : "=r" (reg));
    console_printf("Initial secure TTBR1: %lx\n", reg);

    /* setup secure-world page tables */

    /* load the same page table base into both TTBR0 and TTBR1
     * TTBR0 will change in the monitor's context switching code */
    assert((ptbase & 0x3fff) == 0);
    uintptr_t ttbr = ptbase | 0x4a; // PT walker uses cache
    __asm volatile("mcr p15, 0, %0, c2, c0, 0" :: "r" (ttbr));
    __asm volatile("mcr p15, 0, %0, c2, c0, 1" :: "r" (ttbr));
    console_printf("Final secure TTBR0/1: %lx\n", ttbr);

    /* setup TTBCR for a 1G/3G address split, and enable both TTBR0 and TTBR1
     * ref: B3.5.4 Selecting between TTBR0 and TTBR1, Short-descriptor
     * translation table format and B4.1.153 TTBCR, Translation Table
     * Base Control Register, VMSA */
    __asm volatile("mcr p15, 0, %0, c2, c0, 2" :: "r" (2));

    /* set domain 0 to manager access (??) */
    __asm volatile("mcr p15, 0, %0, c3, c0, 0" :: "r" (3));

    /* ensure that CONTEXTIDR (containing the current ASID) is set to 0 */
    __asm volatile("mcr p15, 0, %0, c13, c0, 1" :: "r" (0));

    /* flush stuff */
    __asm volatile("dsb");
    __asm volatile("isb");
    __asm volatile("mcr p15, 0, r0, c8, c7, 0"); // TLBIALL
    __asm volatile ("isb");
    __asm volatile("mcr p15, 0, r0, c7, c5, 0"); // ICIALLU
    __asm volatile ("dsb");
    __asm volatile ("isb");

    /* enable the MMU in the system control register
     * (this should be ok, since we have a 1:1 map for low RAM) */
    __asm volatile("mrc p15, 0, %0, c1, c0, 0" : "=r" (reg));
    console_printf("initial secure SCTLR: %lx\n", reg);
    reg |= ARM_SCTLR_M | ARM_SCTLR_AFE;
    // while we're here, ensure that there's no funny business with the VBAR
    reg &= ~(ARM_SCTLR_V | ARM_SCTLR_VE | ARM_SCTLR_TRE);
    __asm volatile("mcr p15, 0, %0, c1, c0, 0" : : "r" (reg));
    console_printf("Final secure SCTLR: %lx\n", reg);

    /* setup secure VBAR and MVBAR */
    console_printf("Final secure VBAR: %lx; MVBAR: %lx\n", vbar, mvbar);
    __asm volatile("mcr p15, 0, %0, c12, c0, 0" :: "r" (vbar));
    __asm volatile("mcr p15, 0, %0, c12, c0, 1" :: "r" (mvbar));

    /* update monitor-mode's banked SP value for use in later SMCs */
    /* FIXME: this causes an undefined instruction exception on
       qemu, which doesn't seem to enable the virtualization
       extension on its cortex-a15 model (as it should!)  */
    __asm volatile("msr sp_mon, %0" :: "r" (mon_sp));

    /* flush again */
    __asm volatile("isb");
}

static volatile bool global_barrier;
static uintptr_t g_ptbase, g_vbar, g_mvbar;

static void __attribute__((noreturn)) secondary_main(uint8_t coreid)
{
    while (!global_barrier) __asm volatile("yield");

    // TODO: compute per-core monitor stack pointer
    secure_world_init(g_ptbase, g_vbar, g_mvbar, 0xffffffff /* TODO */);

    leave_secure_world();

    park_secondary_cores();
    
    /* TODO */
    while (1) {}
}

static void map_section(armpte_short_l1 *l1pt, uintptr_t vaddr, uintptr_t paddr,
                        bool nocache)
{
    uintptr_t idx = vaddr >> ARM_L1_SECTION_BITS;

    l1pt[idx].raw = (armpte_short_l1) {
        .section = {
            .type = 1,
            .b = 1, // shareable device / write-back, write-allocate
            .c = nocache ? 0 : 1, // shareable device / write-back, write-allocate
            .xn = 0,
            .domain = 0,
            .ap0 = 1, // access flag = 1 (already accessed)
            .ap1 = 0, // system
            .tex = nocache ? 0 : 1, // cacheable, write-back, write-allocate
            .ap2 = 0,
            .s = 1, // shareable
            .ng = 0, // global (ASID doesn't apply)
            .ns = 1, // non-secure-world PA
            .secbase = paddr >> ARM_L1_SECTION_BITS,
        }
    }.raw;
}

static void map_l2_pages(armpte_short_l2 *l2pt, uintptr_t vaddr, uintptr_t paddr,
                         size_t bytes, bool exec, bool nocache)
{
    assert((bytes & 0xfff) == 0);
    for (uintptr_t idx = (vaddr >> 12) & 0xff; bytes > 0; idx++) {
        //console_printf("map PA %lx at index %lx\n", paddr, idx);
        l2pt[idx].raw = (armpte_short_l2) {
            .smallpage = {
                .xn = exec ? 0 : 1,
                .type = 1,
                .b = 1, // shareable device / write-back, write-allocate
                .c = nocache ? 0 : 1, // shareable device / write-back, write-allocate
                .ap0 = 1, // access flag = 1 (already accessed)
                .ap1 = 0, // system
                .tex = nocache ? 0 : 1, // cacheable, write-back, write-allocate
                .ap2 = exec ? 1 : 0,
                .s = 1, // shareable
                .ng = 0, // global (ASID doesn't apply)
                .base = paddr >> 12
            }
        }.raw;
        bytes -= 0x1000;
        paddr += 0x1000;
        assert(idx != 255);
    }
}

#if 0
static uintptr_t smc(uintptr_t arg0, uintptr_t arg1, uintptr_t arg2, uintptr_t arg3)
{
    register uintptr_t r0 __asm("r0") = arg0;
    register uintptr_t r1 __asm("r1") = arg1;
    register uintptr_t r2 __asm("r2") = arg2;
    register uintptr_t r3 __asm("r3") = arg3;

    __asm("smc #0"
          : "+r" (r0), "+r" (r1), "+r" (r2), "+r" (r3)
          : "0" (r0), "1" (r1), "2" (r2), "3" (r3)
          );

    return r0;
}
#endif

void __attribute__((noreturn)) main(void)
{
    uint8_t coreid = mycoreid();
    if (coreid != 0) {
        secondary_main(coreid);
    }

    serial_init();
    serial_putc('H');
    console_puts("ello world\n");

    uintptr_t reg;
    __asm("mrs %0, cpsr" : "=r" (reg));
    console_printf("Initial CPSR: %lx\n", reg);
    __asm("mrc p15, 0, %0, c1, c1, 0" : "=r" (reg));
    console_printf("Initial SCR: %lx\n", reg);

    /* dump ATAGS, and reserve some high RAM for monitor etc. */
    atags_init((void *)0x100);
    atags_dump();

    /* we need to reserve enough memory for the monitor image, plus
     * alignment up to a 16kB boundary, plus the L1 page table (16kB
     * in size), plus the L2 table (only 1kB in size, but we make it
     * 4kB for page-alignment of the overall allocation)
     */

    uintptr_t monitor_physbase, ptbase;
    size_t monitor_image_bytes = &monitor_image_bss - &monitor_image_start;
    size_t monitor_mem_bytes = &monitor_image_end - &monitor_image_start;
    size_t monitor_mem_reserve = ROUND_UP(monitor_mem_bytes, ARM_L1_PTABLE_BYTES);
    
    monitor_physbase = atags_reserve_physmem(monitor_mem_reserve // image size
                                             + ARM_L1_PTABLE_BYTES // L1 ptable
                                             + KOM_PAGE_SIZE // L2 ptable
                                             + ARM_L1_PTABLE_BYTES // alignment padding
                                             + KOM_SECURE_RESERVE); // secure mem
    
    /* copy the monitor image into place */
    console_printf("Copying monitor to %lx (BSS at %lx)\n", monitor_physbase, monitor_physbase + monitor_image_bytes);
    memcpy((void *)monitor_physbase, &monitor_image_start, monitor_image_bytes);
    memset((char *)monitor_physbase + monitor_image_bytes, 0,
           monitor_mem_bytes - monitor_image_bytes);

    console_puts("Constructing page tables\n");

    /* L1 page table must be 16kB-aligned */
    ptbase = ROUND_UP(monitor_physbase + monitor_mem_bytes, ARM_L1_PTABLE_BYTES);

    armpte_short_l1 *l1pt = (void *)ptbase;
    armpte_short_l2 *l2pt = (void *)(ptbase + ARM_L1_PTABLE_BYTES);

    memset(l1pt, 0, ARM_L1_PTABLE_BYTES);
    memset(l2pt, 0, KOM_PAGE_SIZE);

    /* secure phys base must be 16kB-aligned for the same reason  as l1 alignment */
    uintptr_t secure_physbase = ROUND_UP((uintptr_t)l2pt + KOM_PAGE_SIZE, ARM_L1_PTABLE_BYTES);

    console_printf("L1 %p L2 %p\n", l1pt, l2pt);

    /* direct-map first 1MB of RAM and UART registers using section mappings
     * (will become inaccessible when the monitor switches TTBR0) */
    map_section(l1pt, 0, 0, false);
    map_section(l1pt, 0x3f100000, 0x3f100000, true); // RNG base
    map_section(l1pt, 0x3f200000, 0x3f200000, true); // UART base

    /* direct-map phys memory in the 2-4G region for the monitor to use */
    for (uintptr_t off = 0; off < KOM_DIRECTMAP_SIZE; off += ARM_L1_SECTION_SIZE) {
        map_section(l1pt, KOM_DIRECTMAP_VBASE + off, off, false);
    }

    /* install a second-level page table for the monitor image */
    l1pt[KOM_MON_VBASE >> 20].raw = (armpte_short_l1){
        .pagetable = {
            .type = 1,
            .pxn = 0,
            .ns = 1, // non-secure world PA
            .ptbase = ((uintptr_t)l2pt) >> 10,
        }
    }.raw;

    // text and rodata
    size_t monitor_executable_size = &monitor_image_data - &monitor_image_start;
    console_printf("mapping monitor executable at %lx-%lx\n",
                   KOM_MON_VBASE, KOM_MON_VBASE + monitor_executable_size);
    map_l2_pages(l2pt, KOM_MON_VBASE, monitor_physbase,
                 monitor_executable_size, true, false);

    // data and bss
    size_t monitor_mapped_size = ROUND_UP(monitor_mem_bytes, 0x1000);
    size_t monitor_rw_size = monitor_mapped_size - monitor_executable_size;
    console_printf("mapping monitor RW at %lx-%lx\n",
                   KOM_MON_VBASE + monitor_executable_size,
                   KOM_MON_VBASE + monitor_mapped_size);
    map_l2_pages(l2pt, KOM_MON_VBASE + monitor_executable_size,
                 monitor_physbase + monitor_executable_size,
                 monitor_rw_size, false, false);

    // RNG device regs
    uintptr_t rngvbase = KOM_MON_VBASE + monitor_mapped_size;
    console_printf("mapping RNG page %lx\n", rngvbase);
    map_l2_pages(l2pt, rngvbase, 0x3f104000, 0x1000, false, true);

    uintptr_t monitor_stack
        = &monitor_stack_base - &monitor_image_start + KOM_MON_VBASE;

    g_ptbase = ptbase;
    assert(&_monitor_vectors == &monitor_image_start);
    g_mvbar = &_monitor_vectors - &monitor_image_start + KOM_MON_VBASE;
    g_vbar = &_secure_vectors - &monitor_image_start + KOM_MON_VBASE;

    //print_hex(0x4237);
    //console_printf(" <-- Print_hex test\n"),

    secure_world_init(g_ptbase, g_vbar, g_mvbar, monitor_stack);

    console_printf("RNG init...\n");
    rng_init();
    
    /* init the monitor by setting up the secure physbase */
    uintptr_t *monitor_monitor_physbase
        = (uintptr_t *)(&g_monitor_physbase - &monitor_image_start + KOM_MON_VBASE);
    console_printf("passing monitor_physbase %lx to monitor (&%p)\n",
                   monitor_physbase, monitor_monitor_physbase);
    *monitor_monitor_physbase = monitor_physbase;
    uintptr_t *monitor_secure_physbase
        = (uintptr_t *)(&g_secure_physbase - &monitor_image_start + KOM_MON_VBASE);
    console_printf("passing secure_physbase %lx to monitor (&%p)\n",
                   secure_physbase, monitor_secure_physbase);
    *monitor_secure_physbase = secure_physbase;
    uintptr_t *monitor_rngbase
        = (uintptr_t *)(&g_rngbase - &monitor_image_start + KOM_MON_VBASE);
    console_printf("passing RNG vbase %lx to monitor (&%p)\n",
                   rngvbase, monitor_rngbase);
    *monitor_rngbase = rngvbase;

    __asm volatile("" : : : "memory");

    // this call will return in non-secure world (where MMUs are still off)
    leave_secure_world();

    __asm volatile("mrc p15, 0, %0, c2, c0, 0" : "=r" (reg));
    console_printf("Final !secure TTBR0: %lx\n", reg);
    __asm volatile("mrc p15, 0, %0, c2, c0, 1" : "=r" (reg));
    console_printf("Final !secure TTBR1: %lx\n", reg);
    __asm volatile("mrc p15, 0, %0, c1, c0, 0" : "=r" (reg));
    console_printf("Final !secure SCTLR: %lx\n", reg);
    __asm volatile("mrc p15, 0, %0, c12, c0, 0" : "=r" (reg));
    console_printf("Final !secure VBAR: %lx\n", reg);

    __asm volatile("mrs %0, cpsr" : "=r" (reg));
    console_printf("Final CPSR: %lx\n", reg);

    global_barrier = true;

    console_printf("entering kernel...\n");
    typedef void kernel_entry(uintptr_t zero, uintptr_t boardid, void *atags);
    ((kernel_entry *)0x8000)(0, 0xc43, (void *)0x100);

    while (1) {}
}

void data_abort_handler(void)
{
    uintptr_t dfar, dfsr;

    serial_putc('&');
    console_puts("\nData abort!\n");

    __asm("mrc p15, 0, %0, c5, c0, 0" : "=r" (dfsr));
    __asm("mrc p15, 0, %0, c6, c0, 0" : "=r" (dfar));

    console_printf ("DFAR %lx DFSR %lx\n", dfar, dfsr);

    while (1) {}
}
