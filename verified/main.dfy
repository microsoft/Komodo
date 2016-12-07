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

method printAll()
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

// this is what we assume about the initial state on entry to the SMC handler
predicate InitialState(s:state)
{
    reveal_ValidRegState();

    SaneConstants()
        && ValidState(s) && s.ok
        && mode_of_state(s) == Monitor
        && s.conf.scr.ns == NotSecure
        && s.regs[SP(Monitor)] == StackBase()
        && SaneMem(s.m)
}

method Main()
{
    var smc_handler := sp_code_smc_handler();
    var svc_handler := sp_code_svc_handler();
    var abt_handler := sp_code_abort_handler();

    // prove that the final state for an SMC call is valid
    forall s1:state, p1:PageDb, s2:state
        | InitialState(s1)
        && validPageDb(p1)
        && pageDbCorresponds(s1.m, p1)
        && evalCode(smc_handler, s1, s2)
        && AUCIdef() // XXX
        ensures smchandlerInvariant(s1, s2)
        ensures exists p2:PageDb :: smchandler(s1, p1, s2, p2)
            && validPageDb(p2) && pageDbCorresponds(s2.m, p2)
    {
        var stack_bytes := KOM_STACK_SIZE - WORDSIZE;
        assert StackBytesRemaining(s1, stack_bytes);
        reveal_sp_eval();
        var block := sp_CCons(smc_handler, sp_CNil());
        assert sp_eval(Block(block), s1, s2) by { assert evalBlock(block, s1, s2); }
        var _, _, p2' := sp_lemma_smc_handler(block, s1, s2, stack_bytes, p1);
        assert smchandler(s1, p1, s2, p2');
        assert validPageDb(p2') && pageDbCorresponds(s2.m, p2');
    }
    
    printAll();
}
