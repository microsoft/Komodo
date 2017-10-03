include "exhandler_state.s.dfy"

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
        s.conf.cpsr.i && !s.conf.cpsr.f && !s.rng.consumed
        && mode_of_state(s) == (match s.conf.ex
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
        assert !s3.conf.cpsr.f && !s3.rng.consumed by
            { reveal userspaceExecutionFn(); }
        lemma_update_psr(cpsr_of_state(s3),
            encode_mode(mode_of_state(r)), false, true);
        assert !r.conf.cpsr.f && !r.rng.consumed;
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
        var dummy:state :| true;
        var _, _, p := va_lemma_interrupt_handler(block, s, r, s.conf.ex, dummy, pagedb, dispPg);
    } else if s.conf.ex == ExAbt || s.conf.ex == ExUnd {
        var _, _, p := va_lemma_abort_handler(block, s, r, s.conf.ex, pagedb, dispPg);
    } else if s.conf.ex == ExSVC {
        assert s.conf.tlb_consistent;
        var _, _, p := va_lemma_svc_handler(block, s, r, pagedb, dispPg);
    }
}

lemma lemma_SMCHandlerIsCorrect(s1:state, p1:PageDb, s2:state)
    requires GlobalAssumptions() && InitialSMCState(s1)
        && validPageDb(p1) && pageDbCorresponds(s1.m, p1)
        && evalCode(smc_handler(), s1, s2)
    ensures exists p2 :: smchandler(s1, p1, s2, p2)
            && validPageDb(p2) && SaneMem(s2.m) && pageDbCorresponds(s2.m, p2)
{
    var stack_bytes := KOM_STACK_SIZE - WORDSIZE;
    assert StackBytesRemaining(s1, stack_bytes);
    reveal va_eval();
    var block := va_CCons(smc_handler(), va_CNil());
    assert va_eval(Block(block), s1, s2) by { assert evalBlock(block, s1, s2); }
    assert ValidPsrWord(va_get_sreg(spsr(Monitor), s1)) by { reveal ValidSRegState(); }
    var _, _, p2' := va_lemma_smc_handler(block, s1, s2, stack_bytes, p1);
    assert smchandler(s1, p1, s2, p2');
    assert validPageDb(p2') && pageDbCorresponds(s2.m, p2');
}

lemma lemma_UserModeExceptionHandlersAreCorrect(s0:state, s1:state, s3:state, r:state)
    requires GlobalAssumptions() && ValidState(s0) && s0.ok
        && UsermodeContinuationPrecondition(s0)
        && evalUserExecution(s0, s1, s3)
        && evalCode(exHandler(s3.conf.ex), s3, r)
    ensures mode_of_state(s3) != User && SaneMem(s3.m)
    ensures exists p2, dp:PageNr :: validPageDb(p2) && pageDbCorresponds(s3.m, p2)
        && finalDispatcher(p2, dp) && KomExceptionHandlerInvariant(s3, p2, r, dp)
{
    var pagedb, dispPg := lemma_UsermodeContinuationPreconditionDef(s0);
    assert KomUserEntryPrecondition(s0, pagedb, dispPg);
    lemma_UserExceptionStateSideEffects(s0, s1, s3, pagedb, dispPg);
    var pagedb' := lemma_KomUserEntryPrecond_Preserved(s0, s1, s3, pagedb, dispPg);
    lemma_evalHandler(s3, r, pagedb', dispPg);
}

lemma lemma_SVCFIQNestedExceptionIsCorrect(s0:state, s1:state, s2:state, r:state)
    requires GlobalAssumptions() && ValidState(s0) && s0.ok
        && UsermodeContinuationPrecondition(s0)
        && mode_of_state(s0) == User && interrupts_enabled(s0)
        && (exists upc:word :: evalExceptionTaken(s0, ExSVC, upc, s1))
        && evalExceptionTaken(s1, ExFIQ, nondet_word(s1.conf.nondet, NONDET_PC()), s2)
        && evalCode(exHandler(ExFIQ), s2, r)
    ensures mode_of_state(s2) != User && SaneMem(s2.m)
    ensures priv_of_mode(spsr_of_state(s2).m) == PL1
    ensures exists p0, dp:PageNr :: validPageDb(p0) && pageDbCorresponds(s2.m, p0)
        && finalDispatcher(p0, dp) && KomInterruptHandlerInvariant(s2, p0, r, dp)
{
    var pagedb, dispPg := lemma_UsermodeContinuationPreconditionDef(s0);
    lemma_PrivExceptionStateSideEffects(s1, s2, ExFIQ, pagedb, dispPg);
    reveal va_eval();
    var block := va_CCons(exHandler(ExFIQ), va_CNil());
    assert va_eval(Block(block), s2, r) by { assert evalBlock(block, s2, r); }
    var _, _, _ := va_lemma_interrupt_handler(block, s2, r, ExFIQ, s1, pagedb, dispPg);
    assert KomInterruptHandlerInvariant(s2, pagedb, r, dispPg);
}

lemma lemma_PrivModeExceptionHandlersAreCorrect(s0:state, ex:exception, s1:state, r:state)
    requires GlobalAssumptions() && ValidState(s0) && s0.ok
        && UsermodeContinuationPrecondition(s0)
        && priv_of_state(s0) == PL1 && interrupts_enabled(s0)
        && mode_of_state(s0) != Supervisor
        && (ex == ExFIQ || ex == ExIRQ)
        && evalExceptionTaken(s0, ex, nondet_word(s0.conf.nondet, NONDET_PC()), s1)
        && evalCode(exHandler(ex), s1, r)
    ensures mode_of_state(s1) != User && SaneMem(s1.m)
    ensures priv_of_mode(spsr_of_state(s1).m) == PL1
    ensures spsr_of_state(s1).m != Supervisor
    ensures exists p0, dp:PageNr :: KomInterruptHandlerInvariant(s1, p0, r, dp)
{
    var pagedb, dispPg := lemma_UsermodeContinuationPreconditionDef(s0);
    lemma_PrivExceptionStateSideEffects(s0, s1, ex, pagedb, dispPg);
    reveal va_eval();
    var block := va_CCons(exHandler(ex), va_CNil());
    assert va_eval(Block(block), s1, r) by { assert evalBlock(block, s1, r); }
    var dummy:state :| true; // irrelevant
    var _, _, _ := va_lemma_interrupt_handler(block, s1, r, ex, dummy, pagedb, dispPg);
    assert KomInterruptHandlerInvariant(s1, pagedb, r, dispPg);
}
