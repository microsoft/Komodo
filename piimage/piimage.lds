OUTPUT_FORMAT("elf32-littlearm")
OUTPUT_ARCH("arm")
ENTRY(_loader_start)

SECTIONS {
        /* loader entry point (and vector table) must start at address 0 */
        loader.entry 0 :
        {
                */piloader.elf(entry);
                ASSERT ((. < 0x100), "Error: entry is too big to fit before ATAGs");
        }

        /* atags_start = 0x100; */

        /* now skip forward, hopefully leaving enough space for atags */
        . = 0x400;
        loader . :
        {
                */piloader.elf(.text);
                */piloader.elf(.rodata*);
                */piloader.elf(.data);
                */piloader.elf(.bss);
                ASSERT((. < 0x8000), "Error: loader is too big to fit below kernel");
        }

        /* place the unmodified kernel image at 0x8000 */
        kernel_blob 0x8000 :
        {
                */kernelblob.elf(*);
        }

        /* monitor image is immediately after the kernel, aligned to 4k */
        . = ALIGN(4k);
        monitor_image_start = .;
        monitor.text :
        {
                */monitor.elf(vectors);
                */monitor.elf(.text);
                */monitor.elf(.rodata*);
        }

        . = ALIGN(4k);
        monitor_image_data = .;
        monitor.data . :
        {
                */monitor.elf(.data);
        }

        /* TODO: figure out how to avoid including all the zero-bytes
         * of the monitor BSS in the loaded image */
        monitor_image_bss = .;
        monitor.bss . :
        {
                */monitor.elf(.bss);
        }
        monitor_image_end = .;

        /DISCARD/ :
        {
                *(.ARM.exidx);
                *(.ARM.attributes);
        }
}
