PDCLIB_OBJS = \
    pdclib/functions/ctype/isalnum.o \
    pdclib/functions/ctype/isalpha.o \
    pdclib/functions/ctype/isblank.o \
    pdclib/functions/ctype/iscntrl.o \
    pdclib/functions/ctype/isdigit.o \
    pdclib/functions/ctype/isgraph.o \
    pdclib/functions/ctype/islower.o \
    pdclib/functions/ctype/isprint.o \
    pdclib/functions/ctype/ispunct.o \
    pdclib/functions/ctype/isspace.o \
    pdclib/functions/ctype/isupper.o \
    pdclib/functions/ctype/isxdigit.o \
    pdclib/functions/ctype/tolower.o \
    pdclib/functions/ctype/toupper.o \
    pdclib/functions/errno/errno.o \
    pdclib/functions/inttypes/imaxabs.o \
    pdclib/functions/inttypes/imaxdiv.o \
    pdclib/functions/inttypes/strtoimax.o \
    pdclib/functions/inttypes/strtoumax.o \
    pdclib/functions/stdio/clearerr.o \
    pdclib/functions/stdio/fclose.o \
    pdclib/functions/stdio/feof.o \
    pdclib/functions/stdio/ferror.o \
    pdclib/functions/stdio/fflush.o \
    pdclib/functions/stdio/fgetc.o \
    pdclib/functions/stdio/fgetpos.o \
    pdclib/functions/stdio/fgets.o \
    pdclib/functions/stdio/flockfile.o \
    pdclib/functions/stdio/fopen.o \
    pdclib/functions/stdio/fprintf.o \
    pdclib/functions/stdio/fputc.o \
    pdclib/functions/stdio/fputs.o \
    pdclib/functions/stdio/fread.o \
    pdclib/functions/stdio/freopen.o \
    pdclib/functions/stdio/fscanf.o \
    pdclib/functions/stdio/fseek.o \
    pdclib/functions/stdio/fsetpos.o \
    pdclib/functions/stdio/ftell.o \
    pdclib/functions/stdio/ftrylockfile.o \
    pdclib/functions/stdio/funlockfile.o \
    pdclib/functions/stdio/fwrite.o \
    pdclib/functions/stdio/getc.o \
    pdclib/functions/stdio/getchar.o \
    pdclib/functions/stdio/gets.o \
    pdclib/functions/stdio/perror.o \
    pdclib/functions/stdio/printf.o \
    pdclib/functions/stdio/putc.o \
    pdclib/functions/stdio/putchar.o \
    pdclib/functions/stdio/puts.o \
    pdclib/functions/stdio/rename.o \
    pdclib/functions/stdio/rewind.o \
    pdclib/functions/stdio/scanf.o \
    pdclib/functions/stdio/setbuf.o \
    pdclib/functions/stdio/setvbuf.o \
    pdclib/functions/stdio/snprintf.o \
    pdclib/functions/stdio/sprintf.o \
    pdclib/functions/stdio/sscanf.o \
    pdclib/functions/stdio/tmpnam.o \
    pdclib/functions/stdio/ungetc.o \
    pdclib/functions/stdio/vfprintf.o \
    pdclib/functions/stdio/vfscanf.o \
    pdclib/functions/stdio/vprintf.o \
    pdclib/functions/stdio/vscanf.o \
    pdclib/functions/stdio/vsnprintf.o \
    pdclib/functions/stdio/vsprintf.o \
    pdclib/functions/stdio/vsscanf.o \
    pdclib/functions/stdio/_cbprintf.o \
    pdclib/functions/stdio/_PDCLIB_filemode.o \
    pdclib/functions/stdio/_PDCLIB_fillbuffer.o \
    pdclib/functions/stdio/_PDCLIB_flushbuffer.o \
    pdclib/functions/stdio/_PDCLIB_ftell64.o \
    pdclib/functions/stdio/_PDCLIB_fvopen.o \
    pdclib/functions/stdio/_PDCLIB_prepread.o \
    pdclib/functions/stdio/_PDCLIB_prepwrite.o \
    pdclib/functions/stdio/_PDCLIB_print.o \
    pdclib/functions/stdio/_PDCLIB_scan.o \
    pdclib/functions/stdio/_PDCLIB_seek.o \
    pdclib/functions/stdio/_vcbprintf.o \
    pdclib/functions/stdlib/abort.o \
    pdclib/functions/stdlib/abs.o \
    pdclib/functions/stdlib/atexit.o \
    pdclib/functions/stdlib/atoi.o \
    pdclib/functions/stdlib/atol.o \
    pdclib/functions/stdlib/atoll.o \
    pdclib/functions/stdlib/at_quick_exit.o \
    pdclib/functions/stdlib/bsearch.o \
    pdclib/functions/stdlib/div.o \
    pdclib/functions/stdlib/exit.o \
    pdclib/functions/stdlib/labs.o \
    pdclib/functions/stdlib/ldiv.o \
    pdclib/functions/stdlib/llabs.o \
    pdclib/functions/stdlib/lldiv.o \
    pdclib/functions/stdlib/quick_exit.o \
    pdclib/functions/stdlib/strtol.o \
    pdclib/functions/stdlib/strtoll.o \
    pdclib/functions/stdlib/strtoul.o \
    pdclib/functions/stdlib/strtoull.o \
    pdclib/functions/stdlib/_Exit.o \
    pdclib/functions/string/memchr.o \
    pdclib/functions/string/memcmp.o \
    pdclib/functions/string/memcpy.o \
    pdclib/functions/string/memmove.o \
    pdclib/functions/string/memset.o \
    pdclib/functions/string/strcat.o \
    pdclib/functions/string/strchr.o \
    pdclib/functions/string/strcmp.o \
    pdclib/functions/string/strcoll.o \
    pdclib/functions/string/strcpy.o \
    pdclib/functions/string/strcspn.o \
    pdclib/functions/string/strdup.o \
    pdclib/functions/string/strerror.o \
    pdclib/functions/string/strlcat.o \
    pdclib/functions/string/strlcpy.o \
    pdclib/functions/string/strlen.o \
    pdclib/functions/string/strncat.o \
    pdclib/functions/string/strncmp.o \
    pdclib/functions/string/strncpy.o \
    pdclib/functions/string/strndup.o \
    pdclib/functions/string/strnlen.o \
    pdclib/functions/string/strpbrk.o \
    pdclib/functions/string/strrchr.o \
    pdclib/functions/string/strspn.o \
    pdclib/functions/string/strstr.o \
    pdclib/functions/string/strtok.o \
    pdclib/functions/string/strxfrm.o \
    pdclib/functions/uchar/c16rtomb.o \
    pdclib/functions/uchar/c32rtomb.o \
    pdclib/functions/uchar/mbrtoc16.o \
    pdclib/functions/uchar/mbrtoc32.o \
    pdclib/functions/uchar/_PDCLIB_c16slen.o \
    pdclib/functions/uchar/_PDCLIB_c32slen.o \
    pdclib/functions/uchar/_PDCLIB_c32srtombs.o \
    pdclib/functions/uchar/_PDCLIB_mbsrtoc32s.o \
    pdclib/functions/wchar/mbrtowc.o \
    pdclib/functions/wchar/mbsinit.o \
    pdclib/functions/wchar/wcrtomb.o \
    pdclib/functions/wchar/wcscat.o \
    pdclib/functions/wchar/wcschr.o \
    pdclib/functions/wchar/wcscmp.o \
    pdclib/functions/wchar/wcscoll.o \
    pdclib/functions/wchar/wcscpy.o \
    pdclib/functions/wchar/wcscspn.o \
    pdclib/functions/wchar/wcslen.o \
    pdclib/functions/wchar/wcsncat.o \
    pdclib/functions/wchar/wcsncmp.o \
    pdclib/functions/wchar/wcsncpy.o \
    pdclib/functions/wchar/wcspbrk.o \
    pdclib/functions/wchar/wcsrchr.o \
    pdclib/functions/wchar/wcsspn.o \
    pdclib/functions/wchar/wcsstr.o \
    pdclib/functions/wchar/wcstok.o \
    pdclib/functions/wchar/wcsxfrm.o \
    pdclib/functions/wchar/wmemchr.o \
    pdclib/functions/wchar/wmemcmp.o \
    pdclib/functions/wchar/wmemcpy.o \
    pdclib/functions/wchar/wmemmove.o \
    pdclib/functions/wctype/iswalnum.o \
    pdclib/functions/wctype/iswalpha.o \
    pdclib/functions/wctype/iswblank.o \
    pdclib/functions/wctype/iswcntrl.o \
    pdclib/functions/wctype/iswctype.o \
    pdclib/functions/wctype/iswdigit.o \
    pdclib/functions/wctype/iswgraph.o \
    pdclib/functions/wctype/iswlower.o \
    pdclib/functions/wctype/iswprint.o \
    pdclib/functions/wctype/iswpunct.o \
    pdclib/functions/wctype/iswspace.o \
    pdclib/functions/wctype/iswupper.o \
    pdclib/functions/wctype/iswxdigit.o \
    pdclib/functions/wctype/towctrans.o \
    pdclib/functions/wctype/towlower.o \
    pdclib/functions/wctype/towupper.o \
    pdclib/functions/wctype/wctrans.o \
    pdclib/functions/wctype/wctype.o \
    pdclib/functions/_PDCLIB/assert.o \
    pdclib/functions/_PDCLIB/stdarg.o \
    pdclib/functions/_PDCLIB/_PDCLIB_ascii.o \
    pdclib/functions/_PDCLIB/_PDCLIB_atomax.o \
    pdclib/functions/_PDCLIB/_PDCLIB_closeall.o \
    pdclib/functions/_PDCLIB/_PDCLIB_digits.o \
    pdclib/functions/_PDCLIB/_PDCLIB_initclocale.o \
    pdclib/functions/_PDCLIB/_PDCLIB_latin1.o \
    pdclib/functions/_PDCLIB/_PDCLIB_seed.o \
    pdclib/functions/_PDCLIB/_PDCLIB_strtox_main.o \
    pdclib/functions/_PDCLIB/_PDCLIB_strtox_prelim.o \
    pdclib/functions/_PDCLIB/_PDCLIB_utf8.o \
    pdclib/platform/_PDCLIB/stdinit.o \
    pdclib/platform/_PDCLIB/_PDCLIB_fileops.o \
#    pdclib/functions/stdlib/qsort.o \
#    pdclib/functions/stdlib/rand.o \
#    pdclib/functions/stdlib/srand.o \
#    pdclib/functions/locale/freelocale.o \
#    pdclib/functions/locale/localeconv.o \
#    pdclib/functions/locale/setlocale.o \
#    pdclib/functions/locale/uselocale.o \
#    pdclib/functions/locale/_PDCLIB_mb_cur_max.o \
#    pdclib/functions/locale/_PDCLIB_unicodedata.o \
#    pdclib/functions/signal/raise.o \
#    pdclib/functions/signal/signal.o \
#    pdclib/functions/time/clock.o \
#    pdclib/functions/time/time.o \
#    pdclib/functions/time/timespec_get.o \
#    pdclib/functions/_dlmalloc/dlmalloc.o \
#    pdclib/platform/nothread/call_once.o \
#    pdclib/platform/nothread/cnd_init.o \
#    pdclib/platform/nothread/cnd_signal.o \
#    pdclib/platform/nothread/cnd_wait.o \
#    pdclib/platform/nothread/mtx_destroy.o \
#    pdclib/platform/nothread/mtx_init.o \
#    pdclib/platform/nothread/mtx_lock.o \
#    pdclib/platform/nothread/mtx_timedlock.o \
#    pdclib/platform/nothread/mtx_trylock.o \
#    pdclib/platform/nothread/mtx_unlock.o \
#    pdclib/platform/nothread/thrd_yield.o \
#    pdclib/platform/nothread/tss_create.o \
#    pdclib/platform/nothread/tss_delete.o \
#    pdclib/platform/nothread/tss_get.o \
#    pdclib/platform/nothread/tss_set.o \
#    pdclib/platform/stdio/remove.o \
#    pdclib/platform/stdio/tmpfile.o \
#    pdclib/platform/stdlib/getenv.o \
#    pdclib/platform/stdlib/system.o \
#    pdclib/platform/_PDCLIB/allocpages.o \
#    pdclib/platform/_PDCLIB/freepages.o \
#    pdclib/platform/_PDCLIB/rename.o \
#    pdclib/platform/_PDCLIB/_PDCLIB_Exit.o \
#    pdclib/platform/_PDCLIB/_PDCLIB_open.o

pdclib.a: $(PDCLIB_OBJS)
	$(AR) rcs $@ $^

clean::
	$(RM) $(PDCLIB_OBJS)
	$(RM) pdclib.a
