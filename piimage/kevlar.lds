OUTPUT_FORMAT("elf32-littlearm")
OUTPUT_ARCH("arm")
ENTRY(_start)

SECTIONS {
        /* loader entry point (and vector table) must start at address 0 */
        loader.entry 0 :
        {
                */piloader.elf(entry);
                ASSERT ((. < 0x100), "Error: entry is too big to fit before ATAGs");
        }

        atags_start = 0x100;
        
        /* now skip forward, hopefully leaving enough space for atags */
        . = 0x400;
        loader.text . :
        {
                */piloader.elf(.text);
        }

        loader.rodata . :
        {
                */piloader.elf(.rodata);
        }

        loader.data . :
        {
                */piloader.elf(.data);
        }

        loader.bss . :
        {
                */piloader.elf(.bss);
        }

        /* place the unmodified kernel image at 0x8000 */
        kernel_blob :
        {
                ASSERT ((. < 0x8000), "Error: loader is too big to fit below kernel");
                . = 0x8000;
                */kernelblob.elf(*);
        }

        /* monitor image is immediately after the kernel, aligned to 4k */
        . = ALIGN(4k);
        monitor_start = .;
        monitor.text . :
        {
                */monitor.elf(.text);
        }

        monitor.rodata . :
        {
                */monitor.elf(.rodata);
        }

        monitor.data . :
        {
                */monitor.elf(.data);
        }

        monitor.bss . :
        {
                */monitor.elf(.bss);
        }
        monitor_end = .;

        /DISCARD/ :
        {
                *(.ARM.exidx);
                *(.ARM.attributes);
        }
}
