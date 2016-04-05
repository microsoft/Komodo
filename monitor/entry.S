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
1:      b       1b      /* prefetch_abort */
1:      b       1b      /* data_abort */
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


_monitor_start: /* start of day entry, invoked only by the loader */
        /* compute stack and switch to it */
        getstackaddr ip, r4
        stmdb   r4!, {sp,lr}
        mov     sp, r4

        /* call C */
        bl      monitor_start

        /* return to caller */
        ldm     sp, {sp,lr}
1:      bx      lr


_smchandler:
        /* TODO: figure out calling convention, and which registers to pass/save */
       
        /* call C */
        getstackaddr ip, r4
        stmdb   r4!, {sp,lr}
        bl      smchandler

        /* TODO: scrub secrets from registers */

        /* return from monitor mode */
        ldm     sp, {sp,lr}
        movs    pc,  lr


        .section .bss
        .align 3 // 8-byte alignment
        .lcomm smc_stacks, (STACK_SIZE * NCORES)
