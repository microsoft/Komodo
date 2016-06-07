OUTPUT_FORMAT("elf32-littlearm")
OUTPUT_ARCH("arm")

/*ENTRY(_monitor_vectors)*/

SECTIONS {
        .text 0x40000000 :
        {
                *(vectors);
                *(.text);
                *(.rodata*);
        }

        . = ALIGN(4k);
        .data . :
        {
                *(.data);
        }

        .bss . :
        {
                *(.bss);
        }
}
