#include <stdio.h>
#include <stdarg.h>

#include "serial.h"
#include "console.h"

void console_puts(const char *s)
{
    for (char c = *s; c != '\0'; c = *++s) {
        if (c == '\n') {
            serial_putc('\r');
        }
        serial_putc(c);
    }
}

int console_printf(const char *format, ...)
{
    va_list ap;
    char buf[128];
    int i;

    va_start(ap, format);
    i = vsnprintf(buf, sizeof(buf), format, ap);
    va_end(ap);

    buf[sizeof(buf)-1] = '\0';
    console_puts(buf);

    return i;
}
