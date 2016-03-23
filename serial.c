#include <stdint.h>
#include "serial.h"

#define UART0_BASE      0x3f201000
#define PL011_DR        0x00
#define PL011_FR        0x18
#define PL011_IBRD      0x24
#define PL011_FBRD      0x28

#define PL011_LCRH      0x2c
#define PL011_CR        0x30
#define PL011_IMSC      0x38

#define FR_TXFE         0x80
#define FR_RXFF         0x40
#define FR_TXFF         0x20
#define FR_RXFE         0x10
#define FR_BUSY         0x08

#define LCRH_WLEN_8BIT  0x60
#define LCRH_FEN        0x10

#define CR_CTSEN        0x8000
#define CR_RTSEN        0x4000
#define CR_RXE          0x0200
#define CR_TXE          0x0100
#define CR_UARTEN       0x0001

/* UART clock rate. This must match init_uart_clock in
 * config.txt. This is the value used by the Windows image, but maybe
 * not the default. */
#define PI2_UART_CLOCK  16000000 // 16MHz
#define CONFIG_BAUDRATE 912600 // (again, just matching Windows)

static void write_reg_u32(void *addr, uint32_t val)
{
    *(volatile uint32_t *)addr = val;
}

static uint32_t read_reg_u32(void *addr)
{
    return *(volatile uint32_t *)addr;
}

static void uart0_reg_write(uint32_t reg, uint32_t val)
{
    write_reg_u32((void *)(UART0_BASE + reg), val);
}

static uint32_t uart0_reg_read(uint32_t reg)
{
    return read_reg_u32((void *)(UART0_BASE + reg));
}

void serial_init(void)
{
    // disable the uart
    uart0_reg_write(PL011_CR, 0);

    // wait for end of transmission
    while ((uart0_reg_read(PL011_FR) & FR_BUSY) != 0);

    // flush fifos
    uart0_reg_write(PL011_LCRH, 0);

    // disable interrupts
    uart0_reg_write(PL011_IMSC, 0);

    // reprogram baud rate
    uint32_t baud_divisor = PI2_UART_CLOCK * 4 / CONFIG_BAUDRATE;
    uart0_reg_write(PL011_IBRD, baud_divisor >> 6);
    uart0_reg_write(PL011_FBRD, baud_divisor & 0x3f);

    // enable fifos
    uart0_reg_write(PL011_LCRH, LCRH_WLEN_8BIT | LCRH_FEN);

    // reprogram control register
    uart0_reg_write(PL011_CR, CR_RXE | CR_TXE);

    // re-enable uart
    uart0_reg_write(PL011_CR, CR_RXE | CR_TXE | CR_UARTEN);
}

void serial_putc(char c)
{
    // busy-wait while TX FIFO is full
    while ((uart0_reg_read(PL011_FR) & FR_TXFF) != 0);

    // send character
    uart0_reg_write(PL011_DR, c);
}

void serial_puts(const char *s)
{
    for (char c = *s; c != '\0'; c = *++s) {
        if (c == '\n') {
            serial_putc('\r');
        }
        serial_putc(c);
    }
}
