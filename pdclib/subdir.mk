PDCLIB_OBJS = \
    $(dir)/functions/ctype/isalnum.o \
    $(dir)/functions/ctype/isalpha.o \
    $(dir)/functions/ctype/isblank.o \
    $(dir)/functions/ctype/iscntrl.o \
    $(dir)/functions/ctype/isdigit.o \
    $(dir)/functions/ctype/isgraph.o \
    $(dir)/functions/ctype/islower.o \
    $(dir)/functions/ctype/isprint.o \
    $(dir)/functions/ctype/ispunct.o \
    $(dir)/functions/ctype/isspace.o \
    $(dir)/functions/ctype/isupper.o \
    $(dir)/functions/ctype/isxdigit.o \
    $(dir)/functions/ctype/tolower.o \
    $(dir)/functions/ctype/toupper.o \
    $(dir)/functions/errno/errno.o \
    $(dir)/functions/inttypes/imaxabs.o \
    $(dir)/functions/inttypes/imaxdiv.o \
    $(dir)/functions/inttypes/strtoimax.o \
    $(dir)/functions/inttypes/strtoumax.o \
    $(dir)/functions/stdio/clearerr.o \
    $(dir)/functions/stdio/fclose.o \
    $(dir)/functions/stdio/feof.o \
    $(dir)/functions/stdio/ferror.o \
    $(dir)/functions/stdio/fflush.o \
    $(dir)/functions/stdio/fgetc.o \
    $(dir)/functions/stdio/fgetpos.o \
    $(dir)/functions/stdio/fgets.o \
    $(dir)/functions/stdio/flockfile.o \
    $(dir)/functions/stdio/fopen.o \
    $(dir)/functions/stdio/fprintf.o \
    $(dir)/functions/stdio/fputc.o \
    $(dir)/functions/stdio/fputs.o \
    $(dir)/functions/stdio/fread.o \
    $(dir)/functions/stdio/freopen.o \
    $(dir)/functions/stdio/fscanf.o \
    $(dir)/functions/stdio/fseek.o \
    $(dir)/functions/stdio/fsetpos.o \
    $(dir)/functions/stdio/ftell.o \
    $(dir)/functions/stdio/ftrylockfile.o \
    $(dir)/functions/stdio/funlockfile.o \
    $(dir)/functions/stdio/fwrite.o \
    $(dir)/functions/stdio/getc.o \
    $(dir)/functions/stdio/getchar.o \
    $(dir)/functions/stdio/gets.o \
    $(dir)/functions/stdio/perror.o \
    $(dir)/functions/stdio/printf.o \
    $(dir)/functions/stdio/putc.o \
    $(dir)/functions/stdio/putchar.o \
    $(dir)/functions/stdio/puts.o \
    $(dir)/functions/stdio/rename.o \
    $(dir)/functions/stdio/rewind.o \
    $(dir)/functions/stdio/scanf.o \
    $(dir)/functions/stdio/setbuf.o \
    $(dir)/functions/stdio/setvbuf.o \
    $(dir)/functions/stdio/snprintf.o \
    $(dir)/functions/stdio/sprintf.o \
    $(dir)/functions/stdio/sscanf.o \
    $(dir)/functions/stdio/tmpnam.o \
    $(dir)/functions/stdio/ungetc.o \
    $(dir)/functions/stdio/vfprintf.o \
    $(dir)/functions/stdio/vfscanf.o \
    $(dir)/functions/stdio/vprintf.o \
    $(dir)/functions/stdio/vscanf.o \
    $(dir)/functions/stdio/vsnprintf.o \
    $(dir)/functions/stdio/vsprintf.o \
    $(dir)/functions/stdio/vsscanf.o \
    $(dir)/functions/stdio/_cbprintf.o \
    $(dir)/functions/stdio/_PDCLIB_filemode.o \
    $(dir)/functions/stdio/_PDCLIB_fillbuffer.o \
    $(dir)/functions/stdio/_PDCLIB_flushbuffer.o \
    $(dir)/functions/stdio/_PDCLIB_ftell64.o \
    $(dir)/functions/stdio/_PDCLIB_fvopen.o \
    $(dir)/functions/stdio/_PDCLIB_prepread.o \
    $(dir)/functions/stdio/_PDCLIB_prepwrite.o \
    $(dir)/functions/stdio/_PDCLIB_print.o \
    $(dir)/functions/stdio/_PDCLIB_scan.o \
    $(dir)/functions/stdio/_PDCLIB_seek.o \
    $(dir)/functions/stdio/_vcbprintf.o \
    $(dir)/functions/stdlib/abort.o \
    $(dir)/functions/stdlib/abs.o \
    $(dir)/functions/stdlib/atexit.o \
    $(dir)/functions/stdlib/atoi.o \
    $(dir)/functions/stdlib/atol.o \
    $(dir)/functions/stdlib/atoll.o \
    $(dir)/functions/stdlib/at_quick_exit.o \
    $(dir)/functions/stdlib/bsearch.o \
    $(dir)/functions/stdlib/div.o \
    $(dir)/functions/stdlib/exit.o \
    $(dir)/functions/stdlib/labs.o \
    $(dir)/functions/stdlib/ldiv.o \
    $(dir)/functions/stdlib/llabs.o \
    $(dir)/functions/stdlib/lldiv.o \
    $(dir)/functions/stdlib/quick_exit.o \
    $(dir)/functions/stdlib/strtol.o \
    $(dir)/functions/stdlib/strtoll.o \
    $(dir)/functions/stdlib/strtoul.o \
    $(dir)/functions/stdlib/strtoull.o \
    $(dir)/functions/stdlib/_Exit.o \
    $(dir)/functions/string/memchr.o \
    $(dir)/functions/string/memcmp.o \
    $(dir)/functions/string/memcpy.o \
    $(dir)/functions/string/memmove.o \
    $(dir)/functions/string/memset.o \
    $(dir)/functions/string/strcat.o \
    $(dir)/functions/string/strchr.o \
    $(dir)/functions/string/strcmp.o \
    $(dir)/functions/string/strcoll.o \
    $(dir)/functions/string/strcpy.o \
    $(dir)/functions/string/strcspn.o \
    $(dir)/functions/string/strdup.o \
    $(dir)/functions/string/strerror.o \
    $(dir)/functions/string/strlcat.o \
    $(dir)/functions/string/strlcpy.o \
    $(dir)/functions/string/strlen.o \
    $(dir)/functions/string/strncat.o \
    $(dir)/functions/string/strncmp.o \
    $(dir)/functions/string/strncpy.o \
    $(dir)/functions/string/strndup.o \
    $(dir)/functions/string/strnlen.o \
    $(dir)/functions/string/strpbrk.o \
    $(dir)/functions/string/strrchr.o \
    $(dir)/functions/string/strspn.o \
    $(dir)/functions/string/strstr.o \
    $(dir)/functions/string/strtok.o \
    $(dir)/functions/string/strxfrm.o \
    $(dir)/functions/uchar/c16rtomb.o \
    $(dir)/functions/uchar/c32rtomb.o \
    $(dir)/functions/uchar/mbrtoc16.o \
    $(dir)/functions/uchar/mbrtoc32.o \
    $(dir)/functions/uchar/_PDCLIB_c16slen.o \
    $(dir)/functions/uchar/_PDCLIB_c32slen.o \
    $(dir)/functions/uchar/_PDCLIB_c32srtombs.o \
    $(dir)/functions/uchar/_PDCLIB_mbsrtoc32s.o \
    $(dir)/functions/wchar/mbrtowc.o \
    $(dir)/functions/wchar/mbsinit.o \
    $(dir)/functions/wchar/wcrtomb.o \
    $(dir)/functions/wchar/wcscat.o \
    $(dir)/functions/wchar/wcschr.o \
    $(dir)/functions/wchar/wcscmp.o \
    $(dir)/functions/wchar/wcscoll.o \
    $(dir)/functions/wchar/wcscpy.o \
    $(dir)/functions/wchar/wcscspn.o \
    $(dir)/functions/wchar/wcslen.o \
    $(dir)/functions/wchar/wcsncat.o \
    $(dir)/functions/wchar/wcsncmp.o \
    $(dir)/functions/wchar/wcsncpy.o \
    $(dir)/functions/wchar/wcspbrk.o \
    $(dir)/functions/wchar/wcsrchr.o \
    $(dir)/functions/wchar/wcsspn.o \
    $(dir)/functions/wchar/wcsstr.o \
    $(dir)/functions/wchar/wcstok.o \
    $(dir)/functions/wchar/wcsxfrm.o \
    $(dir)/functions/wchar/wmemchr.o \
    $(dir)/functions/wchar/wmemcmp.o \
    $(dir)/functions/wchar/wmemcpy.o \
    $(dir)/functions/wchar/wmemmove.o \
    $(dir)/functions/wctype/iswalnum.o \
    $(dir)/functions/wctype/iswalpha.o \
    $(dir)/functions/wctype/iswblank.o \
    $(dir)/functions/wctype/iswcntrl.o \
    $(dir)/functions/wctype/iswctype.o \
    $(dir)/functions/wctype/iswdigit.o \
    $(dir)/functions/wctype/iswgraph.o \
    $(dir)/functions/wctype/iswlower.o \
    $(dir)/functions/wctype/iswprint.o \
    $(dir)/functions/wctype/iswpunct.o \
    $(dir)/functions/wctype/iswspace.o \
    $(dir)/functions/wctype/iswupper.o \
    $(dir)/functions/wctype/iswxdigit.o \
    $(dir)/functions/wctype/towctrans.o \
    $(dir)/functions/wctype/towlower.o \
    $(dir)/functions/wctype/towupper.o \
    $(dir)/functions/wctype/wctrans.o \
    $(dir)/functions/wctype/wctype.o \
    $(dir)/functions/_PDCLIB/assert.o \
    $(dir)/functions/_PDCLIB/stdarg.o \
    $(dir)/functions/_PDCLIB/_PDCLIB_ascii.o \
    $(dir)/functions/_PDCLIB/_PDCLIB_atomax.o \
    $(dir)/functions/_PDCLIB/_PDCLIB_closeall.o \
    $(dir)/functions/_PDCLIB/_PDCLIB_digits.o \
    $(dir)/functions/_PDCLIB/_PDCLIB_initclocale.o \
    $(dir)/functions/_PDCLIB/_PDCLIB_latin1.o \
    $(dir)/functions/_PDCLIB/_PDCLIB_seed.o \
    $(dir)/functions/_PDCLIB/_PDCLIB_strtox_main.o \
    $(dir)/functions/_PDCLIB/_PDCLIB_strtox_prelim.o \
    $(dir)/functions/_PDCLIB/_PDCLIB_utf8.o \
    $(dir)/platform/_PDCLIB/stdinit.o \
    $(dir)/platform/_PDCLIB/_PDCLIB_fileops.o \
#    $(dir)/functions/stdlib/qsort.o \
#    $(dir)/functions/stdlib/rand.o \
#    $(dir)/functions/stdlib/srand.o \
#    $(dir)/functions/locale/freelocale.o \
#    $(dir)/functions/locale/localeconv.o \
#    $(dir)/functions/locale/setlocale.o \
#    $(dir)/functions/locale/uselocale.o \
#    $(dir)/functions/locale/_PDCLIB_mb_cur_max.o \
#    $(dir)/functions/locale/_PDCLIB_unicodedata.o \
#    $(dir)/functions/signal/raise.o \
#    $(dir)/functions/signal/signal.o \
#    $(dir)/functions/time/clock.o \
#    $(dir)/functions/time/time.o \
#    $(dir)/functions/time/timespec_get.o \
#    $(dir)/functions/_dlmalloc/dlmalloc.o \
#    $(dir)/platform/nothread/call_once.o \
#    $(dir)/platform/nothread/cnd_init.o \
#    $(dir)/platform/nothread/cnd_signal.o \
#    $(dir)/platform/nothread/cnd_wait.o \
#    $(dir)/platform/nothread/mtx_destroy.o \
#    $(dir)/platform/nothread/mtx_init.o \
#    $(dir)/platform/nothread/mtx_lock.o \
#    $(dir)/platform/nothread/mtx_timedlock.o \
#    $(dir)/platform/nothread/mtx_trylock.o \
#    $(dir)/platform/nothread/mtx_unlock.o \
#    $(dir)/platform/nothread/thrd_yield.o \
#    $(dir)/platform/nothread/tss_create.o \
#    $(dir)/platform/nothread/tss_delete.o \
#    $(dir)/platform/nothread/tss_get.o \
#    $(dir)/platform/nothread/tss_set.o \
#    $(dir)/platform/stdio/remove.o \
#    $(dir)/platform/stdio/tmpfile.o \
#    $(dir)/platform/stdlib/getenv.o \
#    $(dir)/platform/stdlib/system.o \
#    $(dir)/platform/_PDCLIB/allocpages.o \
#    $(dir)/platform/_PDCLIB/freepages.o \
#    $(dir)/platform/_PDCLIB/rename.o \
#    $(dir)/platform/_PDCLIB/_PDCLIB_Exit.o \
#    $(dir)/platform/_PDCLIB/_PDCLIB_open.o

$(PDCLIB_OBJS): CFLAGS_LOCAL := -I $(dir)/include -D_PDCLIB_EXTENSIONS -D_PDCLIB_SAVE_SPACE

-include $(PDCLIB_OBJS:.o=.d)

$(dir)/pdclib.a: $(PDCLIB_OBJS)
	$(AR) rcs $@ $^

CLEAN := $(CLEAN) $(PDCLIB_OBJS) $(PDCLIB_OBJS:.o=.d) $(dir)/pdclib.a
