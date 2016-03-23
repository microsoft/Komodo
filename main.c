#include <stdint.h>
#include <stdio.h>

#include "serial.h"

static void secure_init(void)
{
    uint32_t val;
    char buf[128];

    __asm volatile("mrc p15, 0, %0, c1, c1, 0" : "=r" (val));
    sprintf(buf, "Initial SCR: 0x%lx\n", val);
    serial_puts(buf);
}

void __attribute__((noreturn)) main(void)
{
    serial_init();
    serial_puts("Hello world\n");

    secure_init();
    while (1) {}
}
