        .section .text
        .global _start

_start:
        ldr     sp, =stack_top
        b       main

        .section .bss
        .align 3 // 8-byte alignment
stack_end:
        .skip 0x4000
stack_top:
