#include <stdint.h>
#include <stdio.h>

#include "serial.h"

#define ARM_SCR_C       0x4 /* cache enable */
#define ARM_SCR_I       0x1000 /* icache enable */
#define ARM_ACR_SMP     0x40 /* SMP */

#define RASPI_TIMER_FREQ 19200000

static void cpu_init(void)
{
    uint32_t reg;

    /* Enable dcache and icache bits in system control register */
    __asm volatile("mrc p15, 0, %0, c1, c0, 0" : "=r" (reg));
    reg |= ARM_SCR_C | ARM_SCR_I;
    __asm volatile("mcr p15, 0, %0, c1, c0, 0" : : "r" (reg));

    /* Enable cache coherence (SMP bit) in auxiliary control register */
    __asm volatile("mrc p15, 0, %0, c1, c0, 1" : "=r" (reg));
    reg |= ARM_ACR_SMP;
    __asm volatile("mcr p15, 0, %0, c1, c0, 1" : : "r" (reg));

    /* Set timer frequency */
    reg = RASPI_TIMER_FREQ;
    __asm volatile("mcr p15, 0, %0, c14, c0, 0" : : "r" (reg));
}

static void secure_init(void)
{
    uint32_t val;
    char buf[128];

    __asm("mrc p15, 0, %0, c1, c1, 0" : "=r" (val));
    sprintf(buf, "Initial SCR: 0x%lx\n", val);
    serial_puts(buf);
}

void __attribute__((noreturn)) main(void)
{
    cpu_init();
    serial_init();
    serial_puts("Hello world\n");

    secure_init();
    while (1) {}
}
