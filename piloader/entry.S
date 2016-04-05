#define ARM_SCTLR_C     0x4 /* cache enable */
#define ARM_SCTLR_I     0x1000 /* icache enable */
#define ARM_SCTLR_V     0x2000 /* vectors base (high vs VBAR) */
#define ARM_SCTLR_VE    0x1000000 /* interrupt vectors enable */
#define ARM_ACR_SMP     0x40 /* SMP */

#define ARM_SCR_NET     0x40 // no early termination
#define ARM_SCR_AW      0x20 // A bit writable
#define ARM_SCR_FW      0x10 // F bit writable
#define ARM_SCR_EA      0x08 // external abort handler
#define ARM_SCR_FIQ     0x04 // FIQ handler monitor mode
#define ARM_SCR_IRQ     0x02 // IRQ handler monitor mode
#define ARM_SCR_NS      0x01 // non-secure bit

#define RASPI_TIMER_FREQ 19200000

#define NCORES          4
#define STACK_SHIFT     12 // 4kB stack per-core
#define STACK_SIZE      (1<<STACK_SHIFT)

        /* Vector table */
        .section entry, "ax"
        .align 5
        b       _loader_start /* reset */
1:      b       1b      /* undef */
1:      b       1b      /* svc */
1:      b       1b      /* prefetch_abort */
1:      b       1b      /* data_abort */
1:      b       1b      /* reserved */
1:      b       1b      /* irq */
1:      b       1b      /* fiq */

        .section .text
        .global _loader_start
_loader_start: /* Start of day reset entry (all cores) */
        /* Enable dcache and icache bits in system control register */
        mrc     p15, 0, r0, c1, c0, 0
        orr     r0, r0, #ARM_SCTLR_C
        orr     r0, r0, #ARM_SCTLR_I
        mcr     p15, 0, r0, c1, c0, 0

        /* Enable cache coherence (SMP bit) in auxiliary control register */
        mrc     p15, 0, r0, c1, c0, 1
        orr     r0, r0, #(ARM_ACR_SMP)
        mcr     p15, 0, r0, c1, c0, 1

        /* Set timer frequency, and enable it */
        ldr     r0, =1
        mcr     p15, 0, r0, c14, c3, 1  // CNTV_CTL=1
        ldr     r0, =RASPI_TIMER_FREQ
        mcr     p15, 0, r0, c14, c0, 0  // CNTFRQ

        /* Setup NSACR: all copros accessible to non-secure world
         * TODO: sanity-check this */
        ldr     r0, =0x63fff
        mcr     p15, 0, r0, c1, c1, 2

        /* retrieve core ID */
	mrc     p15, 0, r0, c0, c0, 5   // get core ID
	ubfx    r0, r0, #0, #2          // extract LSB

        /* r1 = SCR */
        mrc     p15, 0, r1, c1, c1, 0   // read SCR

        /* clear SCR bits nET, EA, FIQ, IRQ */
        bic     r1, r1, #(ARM_SCR_NET|ARM_SCR_EA|ARM_SCR_FIQ|ARM_SCR_IRQ)

        /* set SCR bits AW, FW */
        orr     r1, r1, #(ARM_SCR_AW|ARM_SCR_FW)

#if 0
        /* set SCR bit NS (non-secure) on non-primary cores only */
	cmp     r0, #0                  // if zero, we're the primary core
	beq     1f
        orr     r1, r1, #ARM_SCR_NS
#endif

1:      /* write SCR */
        mcr     p15, 0, r1, c1, c1, 0

#if 0   /* park secondary cores */
	cmp     r0, #0                  // if zero, we're the primary core
	bne     park_secondary_cores
#endif

        /* enter C loader */
        add     r0, #1
        ldr     sp, =loader_stacks
        add     sp, r0, lsl #STACK_SHIFT
        b       main

#if 0 /* blink LED -- handy to debug early boot issues */
blinky: ldr     r0, =0x3F200000 // gpio base
        // select GPIO register set
        ldr     r1, [r0, #0x10]
        orr     r1, #0x200000
        str     r1, [r0, #0x10]
        // clear LED bit
        mov     r1, #0x8000
1:      str     r1, [r0, #0x2c]
        // delay
        mov     r2, #0xf00000
2:      subs    r2, r2, #1
        bne     2b
        // set LED bit
        str     r1, [r0, #0x20]
        // delay
        mov     r2, #0xf00000
2:      subs    r2, r2, #1
        bne     2b
        // loop
        b       1b
#endif

        .global park_secondary_cores
park_secondary_cores: /* park caller, waiting for a jump address in mailbox 3 */
        /* retrieve core ID */
	mrc     p15, 0, r0, c0, c0, 5   // get core ID
	ubfx    r0, r0, #0, #2          // extract LSB

        ldr	r1, =0x400000CC	        // mailbox 3 read/clear base
1:      yield
        ldr	r3, [r1, r0, lsl #4]    // read mailbox for our core
	cmp	r3, #0                  // spin while zero
	beq	1b
        str	r3, [r1, r0, lsl #4]    // clear mailbox
        bx      r3                      // jump


        .section .bss
        .align 3 // 8-byte alignment
        .lcomm loader_stacks, (STACK_SIZE * NCORES)
