include "ARMprint.s.dfy"
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

// these are global assumptions
predicate GlobalAssumptions()
{
    SaneConstants()
        && UsermodeContinuationPreconditionDef()
        && UsermodeContinuationInvariantDef()
        && InterruptContinuationPreconditionDef()
        && InterruptContinuationInvariantDef()
}

// this is what we assume about the initial state on entry to the SMC handler
predicate InitialSMCState(s:state)
{
    reveal ValidRegState();
    reveal ValidSRegState();

    ValidState(s) && s.ok
        && SaneMem(s.m)
        && mode_of_state(s) == Monitor
        && s.conf.scr.ns == NotSecure
        && !interrupts_enabled(s)
        && s.regs[SP(Monitor)] == StackBase()
        && decode_psr(s.sregs[spsr(Monitor)]).m != Monitor
}

function exHandler(ex:exception): va_code
{
    match ex
        case ExAbt => abt_handler()
        case ExUnd => und_handler()
        case ExSVC => svc_handler()
        case ExFIQ => fiq_handler()
        case ExIRQ => irq_handler()
}

lemma lemma_KomUserEntryPrecond_AbsPT(s:state, pagedb:PageDb, dispPg:PageNr)
    requires KomUserEntryPrecondition(s, pagedb, dispPg)
    ensures ExtractAbsPageTable(s).Just?
{
    lemma_ptablesmatch(s.m, pagedb, l1pOfDispatcher(pagedb, dispPg));
}

predicate ExceptionStateSideEffects(s:state)
{
    ValidState(s) && mode_of_state(s) != User
    && if s.conf.ex == ExFIQ || s.conf.ex == ExIRQ
        then mode_of_state(s) == Monitor && !interrupts_enabled(s)
    else
        interrupts_enabled(s) &&
        mode_of_state(s) == (match s.conf.ex
            case ExAbt => Abort
            case ExUnd => Undefined
            case ExSVC => Supervisor)
}

lemma lemma_KomUserEntryPrecond_Preserved(s0:state, s2:state, r:state,
                                          pagedb0:PageDb, dispPg:PageNr)
                                          returns (pagedb: PageDb)
    requires KomUserEntryPrecondition(s0, pagedb0, dispPg)
    requires evalUserExecution(s0, s2, r)
    ensures pagedb == updateUserPagesFromState(r, pagedb0, dispPg)
    ensures KomUserEntryPrecondition(r, pagedb, dispPg)
{
    lemma_KomUserEntryPrecond_AbsPT(s0, pagedb0, dispPg);
    lemma_userExecutionModel_validity(s0, s2, r);
    lemma_userExecutionPreservesPrivState(s0, r);
    lemma_userExecutionUpdatesPageDb(pagedb0, s0, r, dispPg);
    lemma_executionPreservesMasks(s0, r);

    pagedb := updateUserPagesFromState(r, pagedb0, dispPg);
    assert l1pOfDispatcher(pagedb, dispPg) == l1pOfDispatcher(pagedb0, dispPg)
        && finalDispatcher(pagedb, dispPg)
        by { reveal updateUserPagesFromState(); }
}

lemma lemma_UserExceptionStateSideEffects(s0:state, s2:state, r:state,
                                          pagedb0:PageDb, dispPg:PageNr)
    requires KomUserEntryPrecondition(s0, pagedb0, dispPg)
    requires evalUserExecution(s0, s2, r)
    ensures ExceptionStateSideEffects(r) && spsr_of_state(r).m == User
    ensures !spsr_of_state(r).f && !spsr_of_state(r).i
{
    lemma_KomUserEntryPrecond_AbsPT(s0, pagedb0, dispPg);
    assert evalEnterUserspace(s0, s2);
    assert mode_of_state(s2) == User;
    assert s2.conf.scr == s0.conf.scr == SCRT(Secure, true, true);
    lemma_evalEnterUserspace_preservesAbsPageTable(s0, s2);
    lemma_userExecutionModel_validity(s0, s2, r);
    lemma_userExecutionPreservesPrivState(s0, r);
    lemma_executionPreservesMasks(s0, r);

    var (s3, expc, ex) := userspaceExecutionFn(s2, OperandContents(s0, OLR));
    assert mode_of_state(s3) == mode_of_state(s2) == User
        && s3.conf.scr == s2.conf.scr
        by { reveal userspaceExecutionFn(); }

    assert evalExceptionTaken(s3, ex, expc, r);
    assert r.conf.ex == ex;
    lemma_evalExceptionTaken_Mode(s3, ex, expc, r);
    assert spsr_of_state(r).m == mode_of_state(s3) == User;
    if ex == ExFIQ || ex == ExIRQ {
        assert mode_of_state(r) == Monitor;
        mode_encodings_are_sane();
        lemma_update_psr(cpsr_of_state(s3), encode_mode(Monitor), true, true);
        assert !interrupts_enabled(r);
    } else {
        assert mode_of_state(r) != Monitor;
        assert ex != ExFIQ;
        assert !s3.conf.cpsr.f by
            { reveal userspaceExecutionFn(); }
        lemma_update_psr(cpsr_of_state(s3),
            encode_mode(mode_of_state(r)), false, true);
        assert !r.conf.cpsr.f;
        assert interrupts_enabled(r);
    }
    assert ExceptionStateSideEffects(r);
}

lemma lemma_PrivExceptionStateSideEffects(s:state, r:state, ex:exception,
                                          pagedb:PageDb, dispPg:PageNr)
    requires KomUserEntryPrecondition(s, pagedb, dispPg)
    requires priv_of_state(s) == PL1 && interrupts_enabled(s)
    requires ex == ExIRQ || ex == ExFIQ
    requires evalExceptionTaken(s, ex, nondet_word(s.conf.nondet, NONDET_PC()), r)
    ensures ExceptionStateSideEffects(r) && spsr_of_state(r).m == mode_of_state(s)
{
    assert r.conf.ex == ex;
    lemma_evalExceptionTaken_Mode(s, ex, nondet_word(s.conf.nondet, NONDET_PC()), r);
    assert spsr_of_state(r).m == mode_of_state(s);
    assert mode_of_state(r) == Monitor;
    mode_encodings_are_sane();
    lemma_update_psr(cpsr_of_state(s), encode_mode(Monitor), true, true);
    assert !interrupts_enabled(r);
}

lemma lemma_evalHandler(s:state, r:state, pagedb:PageDb, dispPg: PageNr)
    requires GlobalAssumptions() && ExceptionStateSideEffects(s)
    requires KomUserEntryPrecondition(s, pagedb, dispPg) && mode_of_state(s) != User
    requires evalCode(exHandler(s.conf.ex), s, r)
    requires spsr_of_state(s).m == User // proofs about PL1 interrupts go elsewhere
    requires !(s.conf.ex == ExIRQ || s.conf.ex == ExFIQ) ==>
        !spsr_of_state(s).f && !spsr_of_state(s).i
    ensures KomExceptionHandlerInvariant(s, pagedb, r, dispPg)
{
    var block := va_CCons(exHandler(s.conf.ex), va_CNil());
    reveal va_eval();
    assert va_eval(Block(block), s, r) by { assert evalBlock(block, s, r); }
    if s.conf.ex == ExIRQ || s.conf.ex == ExFIQ {
        var _, _, p := va_lemma_interrupt_handler(block, s, r, s.conf.ex, pagedb, dispPg);
    } else if s.conf.ex == ExAbt || s.conf.ex == ExUnd {
        var _, _, p := va_lemma_abort_handler(block, s, r, s.conf.ex, pagedb, dispPg);
    } else if s.conf.ex == ExSVC {
        var _, _, p := va_lemma_svc_handler(block, s, r, pagedb, dispPg);
    }
}

lemma lemma_SMCHandlerIsCorrect()
{
    // prove that the SMC handler is correct
    forall s1:state, p1:PageDb, s2:state
        | GlobalAssumptions() && InitialSMCState(s1)
        && validPageDb(p1) && pageDbCorresponds(s1.m, p1)
        && evalCode(smc_handler(), s1, s2)
        ensures exists p2:PageDb :: smchandler(s1, p1, s2, p2)
            && validPageDb(p2) && pageDbCorresponds(s2.m, p2)
    {
        var stack_bytes := KOM_STACK_SIZE - WORDSIZE;
        assert StackBytesRemaining(s1, stack_bytes);
        reveal va_eval();
        var block := va_CCons(smc_handler(), va_CNil());
        assert va_eval(Block(block), s1, s2) by { assert evalBlock(block, s1, s2); }
        var _, _, p2' := va_lemma_smc_handler(block, s1, s2, stack_bytes, p1);
        assert smchandler(s1, p1, s2, p2');
        assert validPageDb(p2') && pageDbCorresponds(s2.m, p2');
    }
}

lemma lemma_ExceptionHandlersAreCorrect()
{
    // prove that whenever we take an exception from user mode, we can run the right
    // handler and it will establish the invariants assumed in the SMC path
    forall s0:state, s1:state, s3:state, r:state
        | GlobalAssumptions() && ValidState(s0) && s0.ok
        && UsermodeContinuationPrecondition(s0)
        && evalUserExecution(s0, s1, s3)
        && evalCode(exHandler(s3.conf.ex), s3, r)
        ensures exists p2, dp :: KomExceptionHandlerInvariant(s3, p2, r, dp)
    {
        var pagedb, dispPg := lemma_UsermodeContinuationPreconditionDef(s0);
        assert KomUserEntryPrecondition(s0, pagedb, dispPg);
        lemma_UserExceptionStateSideEffects(s0, s1, s3, pagedb, dispPg);
        var pagedb' := lemma_KomUserEntryPrecond_Preserved(s0, s1, s3, pagedb, dispPg);
        lemma_evalHandler(s3, r, pagedb', dispPg);
    }

    // prove that interrupts taken from PL1 modes maintain the invariant
    forall s0:state, ex:exception, s1:state, r:state
        | GlobalAssumptions() && ValidState(s0) && s0.ok
        && UsermodeContinuationPrecondition(s0)
        && priv_of_state(s0) == PL1 && interrupts_enabled(s0)
        && (ex == ExFIQ || ex == ExIRQ)
        && evalExceptionTaken(s0, ex, nondet_word(s0.conf.nondet, NONDET_PC()), s1)
        && evalCode(exHandler(ex), s1, r)
        ensures exists p0, dp :: KomInterruptHandlerInvariant(s1, p0, r, dp)
    {
        var pagedb, dispPg := lemma_UsermodeContinuationPreconditionDef(s0);
        lemma_PrivExceptionStateSideEffects(s0, s1, ex, pagedb, dispPg);
        reveal va_eval();
        var block := va_CCons(exHandler(ex), va_CNil());
        assert va_eval(Block(block), s1, r) by { assert evalBlock(block, s1, r); }
        var _, _, p := va_lemma_interrupt_handler(block, s1, r, ex, pagedb, dispPg);
        assert KomInterruptHandlerInvariant(s1, pagedb, r, dispPg);
    }
}

method Main()
{
    printAll();
}
