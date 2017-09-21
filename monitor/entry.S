#define NCORES          4
#define STACK_SHIFT     14 // 16kB stack per-core
#define STACK_SIZE      (1<<STACK_SHIFT)

#define CPSRM_USR       0x10
#define CPSRM_FIQ       0x11
#define CPSRM_IRQ       0x12
#define CPSRM_SVC       0x13
#define CPSRM_MONITOR   0x16
#define CPSRM_ABORT     0x17
#define CPSRM_UND       0x1b
#define CPSR_F          0x40
#define CPSR_I          0x80
        
#define ARM_SCR_FIQ     0x04 // FIQ handler monitor mode
#define ARM_SCR_IRQ     0x02 // IRQ handler monitor mode
#define ARM_SCR_NS      0x01 // non-secure bit

#define ARM_SCTLR_V     0x2000 /* SCTLR vectors bit (1 = hivecs) */

#define KOM_ERR_SUCCESS         0
#define KOM_ERR_INTERRUPTED     9
#define KOM_ERR_FAULT           10

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
        b       _abort  /* undef */
        b       _svc
        b       _abort  /* prefetch_abort */
        b       _abort  /* data_abort */
1:      b       1b      /* reserved */
1:      b       1b      /* irq */
1:      b       1b      /* fiq */

        .section .text

        .lcomm g_pending_irq, 4
        .lcomm g_pending_fiq, 4

        .macro save_user_context
        /* save full context in cur_dispatcher, trashing LR and R0-R3 in the process */
        push    {lr}       // free up lr
        ldr     lr, =g_cur_dispatcher
        ldr     lr, [lr]
        stmia   lr!, {r0-r12} // r0-r12
        mrs     r0, sp_usr   // SP
        mrs     r1, lr_usr // LR
        pop     {r2} // PC (was stacked LR)
        mrs     r3, spsr // CPSR
        stmia   lr!, {r0-r3}
        .endm

        .macro enter_secure_world tmpreg
        mrc     p15, 0, \tmpreg, c1, c1, 0

        /* clear NS bit, so we stay in secure world when returning */
        bic     \tmpreg, \tmpreg, #ARM_SCR_NS

        /* set FIQ and IRQ bits so that we take these directly to monitor mode */
        orr     \tmpreg, \tmpreg, #(ARM_SCR_FIQ|ARM_SCR_IRQ)

        mcr     p15, 0, \tmpreg, c1, c1, 0
        isb
        .endm

        .macro leave_secure_world tmpreg
        mrc     p15, 0, \tmpreg, c1, c1, 0

        /* set NS bit */
        orr     \tmpreg, \tmpreg, #ARM_SCR_NS

        /* clear FIQ and IRQ bits so that we take these in normal world */
        bic     \tmpreg, \tmpreg, #(ARM_SCR_FIQ|ARM_SCR_IRQ)

        mcr     p15, 0, \tmpreg, c1, c1, 0
        isb
        .endm

        .macro get_vector_base dstreg
        /* check SCTLR.V (hivecs bit) */
        mrc     p15, 0, \dstreg, c1, c0, 0
        ands    \dstreg, \dstreg, #ARM_SCTLR_V
        /* load value assuming hivecs is on (0xffff0000) */
        movw    \dstreg, #0
        movt    \dstreg, #0xffff
        bne     9f
        /* no hivecs: read VBAR */
        mrc     p15, 0, \dstreg, c12, c0, 0
9:
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

        /* check for a pending FIQ */
        ldr     r2, =g_pending_fiq
        ldr     r3, [r2]
        cmp     r3, #0
        beq     1f

        /* deliver a FIQ instead of returning directly! */
        /* clear pending flag */
        mov     r3, #0
        str     r3, [r2]

        /* update target PSR to FIQ mode, with IRQ and FIQ both masked */
        mrs     r2, spsr
        msr     spsr_fiq, r2
        lsr     r2, #5
        lsl     r2, #5
        orr     r2, r2, #(CPSR_F|CPSR_I|CPSRM_FIQ)
        msr     spsr, r2

        /* update target LR for current return address */
        add     lr, lr, #4      // +4 for ARM IRQ shenanigans
        // FIXME: is this adjustment correct for thumb mode?
        msr     lr_fiq, lr

        /* compute return address */
        get_vector_base lr
        add     lr, #(7*4)
        b       2f

1:      /* check for a pending IRQ */
        ldr     r2, =g_pending_irq
        ldr     r3, [r2]
        cmp     r3, #0
        beq     2f

        /* deliver an IRQ instead of returning directly! */
        /* clear pending flag */
        mov     r3, #0
        str     r3, [r2]

        /* update target PSR to IRQ mode, with IRQ masked */
        mrs     r2, spsr
        msr     spsr_irq, r2
        lsr     r2, #5
        lsl     r2, #5
        orr     r2, r2, #(CPSRM_IRQ|CPSR_I)
        msr     spsr, r2

        /* update target LR for current return address */
        add     lr, lr, #4      // +4 for ARM IRQ shenanigans
        msr     lr_irq, lr

        /* compute return address */
        get_vector_base lr
        add     lr, #(6*4)


2:      /* scrub secrets from volatile (non-return) registers */
        mov     r2, #0
        mov     r3, #0

        /* XXX: ARM's SMC calling convention (document DEN0028A) wants
	 * us to preserve this register, but it is volatile
	 * (intra-procedure call scratch) in all ABIs used on both sides
	 * of the call so this makes no sense! */
        mov     ip, #0

        /* return from monitor mode */
        movs    pc,  lr


_irq:   /* IRQ exception, taken from secure user-mode or supervisor/abort/undef mode to monitor-mode */
        /* free up r0-r1 as local temps */
        push    {r0,r1} // push to monitor stack
        
        /* remember that we have a pending IRQ for normal world */
        mov     r0, #1
        ldr     r1, =g_pending_irq
        str     r0, [r1]

        /* branch to common path below */
        b       irqfiq_common
        
_fiq:   /* FIQ exception, taken from secure user-mode or supervisor/abort/undef mode to monitor-mode */
         /* free up r0-r1 as local temps */
        push    {r0,r1} // push to monitor stack
        
        /* remember that we have a pending FIQ for normal world */
        mov     r0, #1
        ldr     r1, =g_pending_fiq
        str     r0, [r1]

        /* fall through */
irqfiq_common:
        sub     lr, lr, #4 // adjust LR to point to next instruction to be executed
       
        /* Figure out if we took this in user mode; if not (i.e., we were in
	 * some other exception handler), then we just need to record the
	 * fact that an interrupt was pending, and go back to handling it! */
        mrs     r0, spsr
        and     r0, r0, #0x1f
        cmp     r0, #CPSRM_USR

        /* restore r0-r1 regardless; we must either save them below, or keep them unmodified */
        pop     {r0,r1}

        beq     1f

        /* We were (early) in another exception handler. We just return to it */
        movs    pc, lr

1:      /* we came from user mode. save context, and continue into the monitor */
        save_user_context

        //leave_secure_world r1

        /* return to SMC dispatch path */
        mov     r0, #KOM_ERR_INTERRUPTED
        mov     r1, #0
        b       dispatch_return

_abort: /* Data abort or undefined instruction, only taken from secure user-mode */

        /* enter monitor mode and disable all interrupts. Prior to this
	 * instruction, we might still take an IRQ or FIQ while in abort/undef mode :( */
        cpsid  iaf, #CPSRM_MONITOR

        //leave_secure_world r1

        mov     r0, #KOM_ERR_FAULT
        mov     r1, #0
        b       dispatch_return

_svc: /* Supervisor call, only taken from secure user-mode */

        /* enter monitor mode and disable all interrupts. Prior to this
	 * instruction, we might still take a FIQ while in supervisor mode :( */
        cpsid  iaf, #CPSRM_MONITOR

        /* XXX: that the only supervisor call we can take (for now) is an exit from secure user mode */
        //leave_secure_world r1

        /* return to SMC dispatch path */
        //mov     r1, r0 // return value from call
        mov     r0, #KOM_ERR_SUCCESS
        b       dispatch_return

        .global dispatch
        /* kom_multival_t dispatch(struct kom_dispatcher *dispatcher) */
dispatch:
        /* save non-volatile registers on monitor's stack */
        push    {r4-r11,lr}
        /* also save SPSR, because we'll need it to return to normal world */
        mrs     r4, spsr
        push    {r4}

        //enter_secure_world r4

        /* load complete context from dispatcher
         * future optimisation: only load arg regs and zero the rest on a fresh dispatch (not resume) */
        ldr     r1, [r0, #(13*4)] // SP
        msr     sp_usr, r1
        ldr     r1, [r0, #(14*4)] // LR
        msr     lr_usr, r1
        ldr     lr, [r0, #(15*4)] // PC
        ldr     r1, [r0, #(16*4)] // PSR
        msr     spsr, r1 // PSR
        ldmia   r0, {r0-r12} // r0-r12

        /* return from monitor mode to secure user mode */
        movs    pc, lr

dispatch_return:
        /* restore SPSR */
        pop     {r4}
        msr     spsr, r4
        /* restore non-volatiles */
        pop     {r4-r11,lr}
        bx      lr


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
