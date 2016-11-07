include "ARMprint.dfy"
include "smc_handler.gen.dfy"
include "exception_handlers.gen.dfy"

method printExceptionHandlerReturn()
{
    printInsFixed("B", user_continue_label());
}

method printSMCHandlerReturn()
{
    printInsFixed("MOVS", "pc, lr");
}

method Main()
{
    var n := 0;
    var monitor_vectbl := emptyVecTbl().(svc_smc := Just("smc"));
    var secure_vectbl := emptyVecTbl().(
        undef := Just("abort"),
        svc_smc := Just("svc"),
        prefetch_abort := Just("abort"),
        data_abort := Just("abort"));

    printHeader(); nl();

    print(".section vectors, \"ax\""); nl();
    printVecTbl("_monitor_vectors", monitor_vectbl); nl();
    printVecTbl("_secure_vectors", secure_vectbl); nl();

    nl();
    print(".section .text"); nl();

    n := printFunction("abort", sp_code_abort_handler(), n);
    printExceptionHandlerReturn(); nl();

    n := printFunction("svc", sp_code_svc_handler(), n);
    printExceptionHandlerReturn(); nl();

    n := printFunction("smc", sp_code_smc_handler(), n);
    printSMCHandlerReturn(); nl();

    printBss(KomGlobalDecls());
    printFooter();
}
