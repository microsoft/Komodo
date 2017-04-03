include "ARMprint.dfy"
include "smc_handler.gen.dfy"
include "exception_handlers.gen.dfy"

function method smc_handler():va_code  { va_code_smc_handler() }
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

method printKSHA256()
{
    print(".type g_k_sha256, %object"); nl();
    print(".align 5"); nl();
    print("g_k_sha256:"); nl();
    print(".word 0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5"); nl();
    print(".word 0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5"); nl();
    print(".word 0xd807aa98,0x12835b01,0x243185be,0x550c7dc3"); nl();
    print(".word 0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174"); nl();
    print(".word 0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc"); nl();
    print(".word 0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da"); nl();
    print(".word 0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7"); nl();
    print(".word 0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967"); nl();
    print(".word 0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13"); nl();
    print(".word 0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85"); nl();
    print(".word 0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3"); nl();
    print(".word 0xd192e819,0xd6990624,0xf40e3585,0x106aa070"); nl();
    print(".word 0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5"); nl();
    print(".word 0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3"); nl();
    print(".word 0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208"); nl();
    print(".word 0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2"); nl();
    print(".size g_k_sha256,.-g_k_sha256"); nl();
    print(".word 0   @ terminator"); nl();
}

// TODO: clean this up (or move it to the loader)
method printStack()
{
    print(".align 3"); nl(); // 8-byte alignment
    print(".global monitor_stack_base"); nl();
    print("monitor_stack_limit:"); nl();
    print(".skip "); print(KOM_STACK_SIZE); nl();
    print("monitor_stack_base:"); nl();
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

    nl(); print(".section .data"); nl();
    printKSHA256(); nl();

    var bssglobals
        := map o | o in KomGlobalDecls() && o != K_SHA256s() :: KomGlobalDecls()[o];
    print(".global g_monitor_physbase, g_secure_physbase"); nl();
    printBss(bssglobals);
    printStack();

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
        && !interrupts_enabled(s)
}

method Main()
{
    // prove that the final state for an SMC call is valid
    forall s1:state, p1:PageDb, s2:state
        | InitialState(s1)
        && validPageDb(p1)
        && pageDbCorresponds(s1.m, p1)
        && evalCode(smc_handler(), s1, s2)
        && AUCIdef() // XXX
        ensures smchandlerInvariant(s1, s2)
        ensures exists p2:PageDb :: smchandler(s1, p1, s2, p2)
            && validPageDb(p2) && pageDbCorresponds(s2.m, p2)
    {
        var stack_bytes := KOM_STACK_SIZE - WORDSIZE;
        assert StackBytesRemaining(s1, stack_bytes);
        reveal_va_eval();
        var block := va_CCons(smc_handler(), va_CNil());
        assert va_eval(Block(block), s1, s2) by { assert evalBlock(block, s1, s2); }
        var _, _, p2' := va_lemma_smc_handler(block, s1, s2, stack_bytes, p1);
        assert smchandler(s1, p1, s2, p2');
        assert validPageDb(p2') && pageDbCorresponds(s2.m, p2');
    }
    printAll();
}
