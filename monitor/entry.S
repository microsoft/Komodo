#define NCORES          4
#define STACK_SHIFT     14 // 16kB stack per-core
#define STACK_SIZE      (1<<STACK_SHIFT)

#define CPSRM_MONITOR   0x16 // value of CPSR.M for Monitor mode

        /* Vector table */
        .section vectors, "ax"
        .global _monitor_vectors, _secure_vectors

        .align 5
_monitor_vectors: /* MVBAR points here */
1:      b       1b      /* reset */
1:      b       1b      /* undef */
        b       _smc
        b       blinky  /* prefetch_abort */
        b       blinky  /* data_abort */
1:      b       1b      /* reserved */
        b       _irq    /* irq */
        b       _fiq    /* fiq */

        .align 5
_secure_vectors: /* Secure-world VBAR points here */
1:      b       1b      /* reset */
1:      b       1b      /* undef */
        b       _svc
        b       _abort  /* prefetch_abort */
        b       _abort  /* data_abort */
1:      b       1b      /* reserved */
1:      b       1b      /* irq */
1:      b       1b      /* fiq */

        .section .text

        .macro save_user_context
        /* save full context in dispatcher */
        push    {lr}       // free up lr
        ldr     lr, =g_cur_dispatcher
        ldr     lr, [lr]
        stmia   lr, {r0-r12} // r0-r12
        mrs     r0, sp_usr   // SP
        mrs     r1, lr_usr // LR
        pop     {r2} // PC (was stacked LR)
        mrs     r3, spsr // CPSR
        stmia   lr, {r0-r3}
        .endm

_smc:
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

_irq:   /* IRQ exception, taken from secure user-mode to secure monitor-mode */
        sub     lr, lr, #4 // adjust LR to point to next instruction to be executed
        save_user_context

        /* remember that we have a pending interrupt for normal world */
        ldr     r0, =g_pending_irq
        mov     r1, #1
        strb    r1, [r0]

        /* TODO: return to SMC dispatch path */
        pop     {lr}
        bx      lr

_fiq:   /* FIQ exception, taken from secure user-mode to secure monitor-mode */
        sub     lr, lr, #4 // adjust LR to point to next instruction to be executed
        save_user_context

        /* remember that we have a pending interrupt for normal world */
        ldr     r0, =g_pending_fiq
        mov     r1, #1
        strb    r1, [r0]

        /* TODO: return to SMC dispatch path */
        pop     {lr}
        bx      lr

_abort: /* Data abort, only taken from secure user-mode */
        /* TODO */
        b       _abort

_svc: /* Supervisor call, only taken from secure user-mode */
        /* TODO */
        b       _svc

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
