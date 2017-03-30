include "ARMprint.dfy"
include "smc_handler.gen.dfy"
include "exception_handlers.gen.dfy"

function method smc_handler():va_code
{
    va_code_smc_handler(OReg(R0), OReg(R1), OReg(R2),
                        OReg(R3), OReg(R4), OReg(R0), OReg(R1))
}

function method svc_handler():va_code  { va_code_svc_handler() }
function method abt_handler():va_code  { va_code_abort_handler(ExAbt) }
function method und_handler():va_code  { va_code_abort_handler(ExUnd) }
function method fiq_handler():va_code  { va_code_interrupt_handler(ExFIQ) }
function method irq_handler():va_code  { va_code_interrupt_handler(ExIRQ) }

method printExceptionHandlerReturn()
{
    printInsFixed("B", user_continue_label());
}

method printInterruptHandlerReturn()
{
    printIns2Op("TST", OSP, OConst(1));
    printInsFixed("BNE", user_continue_label());
    printInsFixed("MOVS", "pc, lr");
}

method printSMCHandlerReturn()
{
    printInsFixed("MOVS", "pc, lr");
}

method printAll()
{
    var n := 0;
    var monitor_vectbl := emptyVecTbl().(
        svc_smc := Just("smc"),
        fiq := Just("fiq"),
        irq := Just("irq"));
    var secure_vectbl := emptyVecTbl().(
        undef := Just("undefined"),
        svc_smc := Just("svc"),
        prefetch_abort := Just("abort"),
        data_abort := Just("abort"));

    printHeader(); nl();

    print(".section vectors, \"ax\""); nl();
    printVecTbl("_monitor_vectors", monitor_vectbl); nl();
    printVecTbl("_secure_vectors", secure_vectbl); nl();

    nl();
    print(".section .text"); nl();

    n := printFunction("abort", abt_handler(), n);
    printExceptionHandlerReturn(); nl();

    n := printFunction("undefined", und_handler(), n);
    printExceptionHandlerReturn(); nl();

    n := printFunction("svc", svc_handler(), n);
    printExceptionHandlerReturn(); nl();

    n := printFunction("smc", smc_handler(), n);
    printSMCHandlerReturn(); nl();

    n := printFunction("fiq", fiq_handler(), n);
    printInterruptHandlerReturn(); nl();

    n := printFunction("irq", irq_handler(), n);
    printInterruptHandlerReturn(); nl();

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
/*
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
        reveal_va_eval();
        var block := va_CCons(smc_handler, va_CNil());
        assert va_eval(Block(block), s1, s2) by { assert evalBlock(block, s1, s2); }
        var _, _, p2' := va_lemma_smc_handler(block, s1, s2,
            OReg(R0), OReg(R1), OReg(R2), OReg(R3), OReg(R4), OReg(R0),
            OReg(R1), stack_bytes, p1);
        assert smchandler(s1, p1, s2, p2');
        assert validPageDb(p2') && pageDbCorresponds(s2.m, p2');
    }
*/
    printAll();
}
