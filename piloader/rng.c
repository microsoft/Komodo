#include <stdint.h>
#include "serial.h"
#include "console.h"
#include "rng.h"

#define RNG_BASE        0x3f104000
#define RNG_CTRL        0x0
#define RNG_STATUS      0x4
#define RNG_DATA        0x8

static void write_reg_u32(void *addr, uint32_t val)
{
    *(volatile uint32_t *)addr = val;
}

static uint32_t read_reg_u32(void *addr)
{
    return *(volatile uint32_t *)addr;
}

static void rng_reg_write(uint32_t reg, uint32_t val)
{
    write_reg_u32((void *)(RNG_BASE + reg), val);
}

static uint32_t rng_reg_read(uint32_t reg)
{
    return read_reg_u32((void *)(RNG_BASE + reg));
}

void rng_init(void)
{
    uint32_t val;

    val = rng_reg_read(RNG_CTRL);
    console_printf("RNG ctrl: %x\n", val);

    if (val & 0x1) { // if enabled
        rng_reg_write(RNG_CTRL, 0); // disable
    }

    rng_reg_write(RNG_STATUS, 0x40000); // warmup count
    rng_reg_write(RNG_CTRL, 1); // enable

    // test the RNG by making sure we can read a word
    console_printf("RNG wait for test word\n");
    while (rng_reg_read(RNG_STATUS) >> 24 == 0) {}
    val = rng_reg_read(RNG_DATA);

    console_printf("RNG test: %x\n", val);
}
