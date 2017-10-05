include "kom_common.i.dfy"
include "entry.i.dfy"

// for now, we only take interrupts at the beginning of another exception handler
// when the user-entry precondition still holds, so this is simplest...
predicate KomInterruptHandlerPrecondition(s:state)
{
    ValidState(s)
        && exists pagedb, dispPg:PageNr :: KomUserEntryPrecondition(s, pagedb, dispPg)
}

predicate InterruptContinuationPreconditionDefInner()
{
    forall s:state {:trigger InterruptContinuationPrecondition(s)} ::
        ValidState(s) && InterruptContinuationPrecondition(s)
        <==> KomInterruptHandlerPrecondition(s)
}

// XXX: the charade of inner/outer def and lemmas here are workarounds
// for an opaque/reveal bug in dafny
predicate {:opaque} InterruptContinuationPreconditionDef()
{ InterruptContinuationPreconditionDefInner() }

lemma lemma_InterruptContinuationPreconditionDefInner()
    requires InterruptContinuationPreconditionDef()
    ensures InterruptContinuationPreconditionDefInner()
{ reveal InterruptContinuationPreconditionDef(); }

lemma lemma_InterruptContinuationPreconditionDef(s:state)
    returns (pagedb:PageDb, dispPg:PageNr)
    requires InterruptContinuationPreconditionDef()
    requires ValidState(s) && InterruptContinuationPrecondition(s)
    ensures KomUserEntryPrecondition(s, pagedb, dispPg)
{
    lemma_InterruptContinuationPreconditionDefInner();
    pagedb, dispPg :| KomUserEntryPrecondition(s, pagedb, dispPg);
}

lemma lemma_Establish_InterruptContinuationPrecondition(s:state, pagedb:PageDb, dispPg:PageNr)
    requires InterruptContinuationPreconditionDef()
    requires KomUserEntryPrecondition(s, pagedb, dispPg)
    ensures InterruptContinuationPrecondition(s)
{
    lemma_InterruptContinuationPreconditionDefInner();
}

predicate KomInterruptHandlerInvariant(s:state, r:state)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires s.conf.ex == ExFIQ || s.conf.ex == ExIRQ
{
    // this definition tells us nothing about interrupts from user or svc modes,
    // except that they set the low bit of SP
    if spsr_of_state(s).m == User || spsr_of_state(s).m == Supervisor
    then ValidState(r) ==> !evalOBool(r, OCmp(OTstEq, OSP, OConst(1)))
    else ValidState(r) && (s.ok ==> r.ok)
    && SaneStateAfterException(r)
    && ParentStackPreserving(s, r)
    && GlobalsPreservingExcept(s, r, {PendingInterruptOp()})
    && s.conf.ttbr0 == r.conf.ttbr0 && s.conf.scr == r.conf.scr
    && mode_of_state(r) == mode_of_state(s)
    && spsr_of_state(r) == spsr_of_state(s)
    && CoreRegPreservingExcept(s, r, {OLR})
    // see B1.8.3 "Link values saved on exception entry"
    && OperandContents(r, OLR) == TruncateWord(OperandContents(s, OLR) - 4)
    && BankedRegsInvariant(s, r)
    && NonStackMemPreserving(s, r)
    && SaneStack(r)
    && s.conf.nondet == r.conf.nondet
    && s.conf.tlb_consistent == r.conf.tlb_consistent
    && s.rng == r.rng
}

// this lemma justifies the ARMdef-level assumptions
// ("EssentialInterruptContinuationInvariantProperties") about the
// state after the handler returns
lemma lemma_KomInterruptHandlerInvariant_soundness(s:state, r:state)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires s.conf.ex == ExFIQ || s.conf.ex == ExIRQ
    requires priv_of_mode(spsr_of_state(s).m) == PL1 && spsr_of_state(s).m != Supervisor
    requires KomInterruptHandlerInvariant(s, r)
    ensures EssentialInterruptContinuationInvariantProperties(s, r)
{
    var sp := OperandContents(r, OSP);
    assert sp == OperandContents(s, OSP);
    assert WordAligned(sp);
    assert BitsAsWord(1) == 1 && BitsAsWord(2) == 2 by { reveal BitsAsWord(); }
    lemma_BitsAndWordConversions();
    assert BitMod(WordAsBits(sp), 2) == 0
        by { reveal WordAligned(); lemma_BitModEquiv(sp, 2); }
    assert BitwiseAnd(sp, 1) == 0 by { reveal BitAnd(); reveal BitMod(); }
}

predicate {:opaque} InterruptContinuationInvariantDef()
{
    reveal ValidRegState();
    forall s:state, r:state
        | ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
          && (s.conf.ex == ExFIQ || s.conf.ex == ExIRQ)
        :: InterruptContinuationInvariant(s, r)
        ==> KomInterruptHandlerInvariant(s, r)
}

lemma lemma_InterruptContinuationInvariantDef(s:state, r:state)
    requires InterruptContinuationInvariantDef()
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires s.conf.ex == ExFIQ || s.conf.ex == ExIRQ
    requires InterruptContinuationInvariant(s, r)
    ensures KomInterruptHandlerInvariant(s, r)
    //ensures s.conf.nondet == r.conf.nondet
    //ensures s.conf.tlb_consistent == r.conf.tlb_consistent
{
    reveal InterruptContinuationInvariantDef();
}

lemma lemma_PrivInterruptInvariants(s:state, r:state)
    requires InterruptContinuationInvariantDef()
    requires ValidState(s) && SaneMem(s.m) && s.ok
    requires priv_of_state(s) == PL1
    requires (mode_of_state(s) == Supervisor) ==> s.conf.cpsr.i
    requires maybeHandleInterrupt(s, r)
    requires SaneStack(s)
    ensures mode_of_state(r) == mode_of_state(s)
    ensures r.conf.ttbr0 == s.conf.ttbr0 && r.conf.scr == s.conf.scr
    ensures r.conf.tlb_consistent == s.conf.tlb_consistent
    ensures r.rng == s.rng
    ensures ValidState(r) && SaneStack(r)
    ensures StackPreserving(s, r)
    ensures NonStackMemPreserving(s, r)
    ensures GlobalsPreservingExcept(s, r, {PendingInterruptOp()})
    ensures CoreRegPreservingExcept(s, r, {OLR})
    ensures forall m :: m != mode_of_exception(s.conf, ExIRQ)
            && m != mode_of_exception(s.conf, ExFIQ)
            ==> s.regs[LR(m)] == r.regs[LR(m)]
                && s.regs[SP(m)] == r.regs[SP(m)]
    ensures interrupts_enabled(s) ==>
        r.conf.nondet == nondet_int(s.conf.nondet, NONDET_GENERATOR())
    ensures (mode_of_state(s) == Supervisor) ==> !stateTakesFiq(s)
{
    var nondet := nondet_word(s.conf.nondet, NONDET_EX());
    if !interrupts_enabled(s) {
        assert r == takestep(s);
    } else if stateTakesFiq(s) || stateTakesIrq(s) {
        var ex := if nondet == 0 then ExFIQ else ExIRQ;
        var s' := reseed_nondet_state(s);
        assert handleInterrupt(s', ex, r);
        var expc := nondet_word(s'.conf.nondet, NONDET_PC());
        var s1, s2 :| evalExceptionTaken(s', ex, expc, s1)
            && InterruptContinuationInvariant(s1, s2)
            && evalMOVSPCLR(s2, r);
        lemma_evalExceptionTaken_Mode(s', ex, expc, s1);
        lemma_InterruptContinuationInvariantDef(s1, s2);

        if mode_of_state(s) == Supervisor && stateTakesFiq(s) {
            // proof by contradiction that if the handler returned, then we
            // mustn't have taken a FIQ, so we don't need to consider that case
            assert ex == ExFIQ;
            assert InterruptContinuationPrecondition(s');
            assert spsr_of_state(s1).m == Supervisor;
            assert !evalOBool(s2, OCmp(OTstEq, OSP, OConst(1)));
            assert EssentialInterruptContinuationInvariantProperties(s1, s2);
            assert ValidState(s2);
            assert s1.ok;
            assert s2.ok;
            assert evalOBool(s2, OCmp(OTstEq, OSP, OConst(1)));
            assert false;
        }

        forall m | m != mode_of_exception(s'.conf, ex)
            ensures s.regs[LR(m)] == r.regs[LR(m)]
            ensures s.regs[SP(m)] == r.regs[SP(m)]
        {
            calc {
                s.regs[LR(m)];
                s'.regs[LR(m)];
                s1.regs[LR(m)];
                s2.regs[LR(m)];
                r.regs[LR(m)];
            }
            calc {
                s.regs[SP(m)];
                s'.regs[SP(m)];
                s1.regs[SP(m)];
                s2.regs[SP(m)];
                r.regs[SP(m)];
            }
        }
        calc {
            s.regs[SP(Monitor)];
            s'.regs[SP(Monitor)];
            s1.regs[SP(Monitor)];
            { if mode_of_state(s1) == Monitor {
                assert CoreRegPreservingExcept(s1, s2, {OLR});
                assert OperandContents(s1, OSP) == OperandContents(s2, OSP);
            } else {
                assert BankedRegsInvariant(s1, s2);
            } }
            s2.regs[SP(Monitor)];
            r.regs[SP(Monitor)];
        }
        assert r.conf.nondet == s'.conf.nondet;
        assert r.conf.nondet == nondet_int(s.conf.nondet, NONDET_GENERATOR());
    } else {
        assert r == takestep(reseed_nondet_state(s));
        assert r.conf.nondet == nondet_int(s.conf.nondet, NONDET_GENERATOR());
    }
}
