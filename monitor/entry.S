#define NCORES          4
#define STACK_SHIFT     14 // 16kB stack per-core
#define STACK_SIZE      (1<<STACK_SHIFT)

#define CPSRM_MONITOR   0x16 // value of CPSR.M for Monitor mode

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
        .global _monitor_start

        .macro getstackaddr tmp, result
        /* compute stack address in \result for a C call, trashing \temp */
	mrc     p15, 0, \tmp, c0, c0, 5 // tmp = core ID
	ubfx    \tmp, \tmp, #0, #2      // extract LSB
        add     \tmp, #1                // tmp = core + 1
        ldr     \result, =smc_stacks    // result = base of stack region
        add     \result, \tmp, lsl #STACK_SHIFT // result += ip * stacksize
        .endm


_monitor_start: /* start of day entry, invoked by the loader in secure SVC mode */
        /* compute monitor stack in r3 */
        getstackaddr ip, r3

        /* update monitor-mode's banked SP value for use in later SMCs */
        /* FIXME: this causes an undefined instruction exception on
	qemu, which doesn't seem to enable the virtualization
	extension on its cortex-a15 model (as it should!)  */
        msr     sp_mon, r3

        /* update monitor-mode's banked LR and SPSR so that we can return to the caller in non-secure world */
        msr     lr_mon, lr
        mrs     r3, cpsr
        msr     spsr_mon, r3

        /* save our current stack (the loader's) in r3 */
        mov     r3, sp

        /* switch to monitor mode (also to its stack) */
        cps     #CPSRM_MONITOR

        /* call C, preserving LR and R3 (the loader's stack) */
        push    {r3,lr}
        bl      monitor_start
        pop     {r3,lr}

        /* set NS bit, so we leave secure world when returning */
        mrc     p15, 0, r0, c1, c1, 0
        orr     r0, #1 // SCR.NS=1
        mcr     p15, 0, r0, c1, c1, 0
        isb // FIXME: is this needed?

        /* copy the loader's stack pointer to the banked SP register */
        msr     sp_svc, r3

        /* scrub volatile registers */
        mov     r0, #0
        mov     r1, #0
        mov     r2, #0
        mov     r3, #0
        mov     ip, #0        

        /* return to caller (in normal-world supervisor mode) */
        movs    pc, lr

_smchandler:
        /* call C */
        push    {lr}
        bl      smchandler
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
        .lcomm smc_stacks, (STACK_SIZE * NCORES)
