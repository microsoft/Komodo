        .section .text

        /* Monitor vector table (MVBAR points here) */
        .align 5
reset:
        b reset
undef:
        b undef
svc:
        b secure_monitor
prefetch_abort:
        b prefetch_abort
data_abort:
        b data_abort
reserved:
        b reserved
irq:
        b irq
fiq:
        b fiq

secure_monitor:
        /* TODO: figure out calling convention, and which registers to pass/save */
        ldr     sp, =stack_top
        blx     smc_handler

        /* TODO: scrub secrets from registers */

        /* return from monitor mode */
        movs    pc,  lr


        .section .bss
        .align 3 // 8-byte alignment
stack:
        .skip 0x2000
stack_top:
