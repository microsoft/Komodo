#include "serial.h"

void __attribute__((noreturn))
main(void)
{
    serial_init();
    serial_puts("Hello world\n");
    while (1) {}
}
