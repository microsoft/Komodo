#define NCORES          4
#define STACK_SHIFT     14 // 16kB stack per-core
#define STACK_SIZE      (1<<STACK_SHIFT)

        /* Vector table */
        .section vectors, "ax"
        .global _monitor_vectors

        .align 5
_monitor_vectors:
1:      b       1b      /* reset */
1:      b       1b      /* undef */
        b       _smchandler
1:      b       blinky  /* prefetch_abort */
1:      b       blinky  /* data_abort */
1:      b       1b      /* reserved */
1:      b       1b      /* irq */
1:      b       1b      /* fiq */


        .section .text
_smchandler:
        /* call C, stacking r4 (used as a parameter) */
        push    {lr}
        push    {r4}
        bl      smchandler
        /* XXX: restore r4 as demanded by ARM's SMC calling convention,
         * even though it was used a parameter and this makes no sense */
        pop     {r4}
        pop     {lr}

        /* scrub secrets from registers */
        mov     r1, #0
        mov     r2, #0
        mov     r3, #0

        /* XXX: ARM's SMC calling convention (document DEN0028A) wants
	 * us to preserve this register, but it is volatile
	 * (intra-procedure call scratch) in all ABIs used on both sides
	 * of the call so this makes no sense! */
        mov     ip, #0

        /* return from monitor mode */
        movs    pc,  lr


#if 1 /* blink LED -- handy to debug early boot issues */
blinky: ldr     r0, =0x3F200000 // gpio base
        // select GPIO register set
        ldr     r1, [r0, #0x10]
        orr     r1, #0x200000
        str     r1, [r0, #0x10]
        // clear LED bit
        mov     r1, #0x8000
1:      str     r1, [r0, #0x2c]
        // delay
        mov     r2, #0x600000
2:      subs    r2, r2, #1
        bne     2b
        // set LED bit
        str     r1, [r0, #0x20]
        // delay
        mov     r2, #0x600000
2:      subs    r2, r2, #1
        bne     2b
        // loop
        b       1b
#endif

        .section .bss
        .align 3 // 8-byte alignment
        // monitor stack, XXX: assuming only one core
        .global monitor_stack_base
monitor_stack_limit:
        .skip STACK_SIZE
monitor_stack_base:
