        .section .text
        .global _start

        /* Vector table */
_start:
        b reset
undef:
        b undef
svc:
        b svc
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


reset: /* Start of day reset entry */
        /* retrieve core ID */
	mrc     p15, 0, r0, c0, c0, 5   // get core ID
	ubfx    r0, r0, #0, #2          // extract LSB
	cmp     r0, #0                  // if zero, we're the primary
	beq     2f

        /* block forever if core != 0 */
1:      wfi
        yield
        b       1b

2:      ldr     sp, =stack_top
        b       main


        .section .bss
        .align 3 // 8-byte alignment
stack_end:
        .skip 0x4000
stack_top:
