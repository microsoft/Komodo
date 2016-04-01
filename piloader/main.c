#include <stdint.h>
#include <stdio.h>

#include "serial.h"
#include "console.h"

#define ARM_SCTLR_C     0x4 /* cache enable */
#define ARM_SCTLR_I     0x1000 /* icache enable */
#define ARM_ACR_SMP     0x40 /* SMP */
#define ARM_SCR_AW      0x20
#define ARM_SCR_FW      0x10
#define ARM_SCR_NS      0x01
#define RASPI_TIMER_FREQ 19200000

typedef union {
    struct {
        uint32_t type:2; // 0x0
        uint32_t ignored:30;
    } invalid;
    struct {
        uint32_t type:2; // 0x1
        uint32_t pxn:1;
        uint32_t ns:1;
        uint32_t sbz:1;
        uint32_t domain:4;
        uint32_t impl:1;
        uint32_t ptbase:22;
    } pagetable;
    struct {
        uint32_t pxn:1;
        uint32_t type:1; // 0x1
        uint32_t b:1;
        uint32_t c:1;
        uint32_t xn:1;
        uint32_t domain:4;
        uint32_t impl:1;
        uint32_t ap01:2;
        uint32_t tex02:3;
        uint32_t ap2:1;
        uint32_t s:1;
        uint32_t ng:1;
        uint32_t mbz:1; // 0
        uint32_t ns:1;
        uint32_t secbase:12;
    } section;
    uint32_t raw;
} armpte_short_l1;

typedef union {
    struct {
        uint32_t type:2; // 0x0
        uint32_t ignored:30;
    } invalid;
    struct {
        uint32_t type:2; // 0x1;
        uint32_t b:1;
        uint32_t c:1;
        uint32_t ap01:2;
        uint32_t sbz:3;
        uint32_t ap2:1;
        uint32_t s:1;
        uint32_t ng:1;
        uint32_t tex02:3;
        uint32_t xn:1;
        uint32_t base:16;
    } largepage;
    struct {
        uint32_t xn:1;
        uint32_t type:1; // 0x1;
        uint32_t b:1;
        uint32_t c:1;
        uint32_t ap01:2;
        uint32_t tex02:3;
        uint32_t ap2:1;
        uint32_t s:1;
        uint32_t ng:1;
        uint32_t base:20;
    } smallpage;
    uint32_t raw;
} armpte_short_l2;

static armpte_short_l1 *pagetable_l1[4096] __attribute__((aligned(4096)));
static armpte_short_l2 *pagetable_l2[256] __attribute__((aligned(1024)));

static void paging_init(void)
{
    /* setup our level 1 page table */
    armpte_short_l1 l1pte = {
        .pagetable = {
            .type = 0,
            .pxn = 0,
            .ns = 0, // secure world PA
            .sbz = 0,
            .domain = 0,
            .impl = 0,
            .ptbase = ((uintptr_t)&pagetable_l2) >> 10,
        }
    };

    pagetable_l1[0].raw = l1pte.raw;

    /* setup a 1MB direct map in our (single) level 2 page table */
    armpte_short_l2 l2pte = {
        .smallpage = {
            .xn = 0,
            .type = 1,
            .b = 0,
            .c = 0,
            .ap01 = 1, //rw PL1 only
            .tex02 = 0,
            .ap2 = 0,
            .s = 0,
            .ng = 0, //?
        }
    };
    for (uintptr_t i = 0; i < 256; i++) {
        l2pte.smallpage.base = i << 12;
        pagetable_l2[i].raw = l2pte.raw;
    }

    /* TODO: init control regs */
    /* TODO: map UART */
}

static void secure_init(void)
{
    uint32_t val;

    __asm("mrc p15, 0, %0, c1, c1, 0" : "=r" (val));
    console_printf("Initial SCR: 0x%lx\n", val);
}

void __attribute__((noreturn)) main(void)
{
    serial_init();
    console_puts("Hello world\n");

    paging_init();
    secure_init();
    while (1) {}
}
