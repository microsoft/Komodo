include "kom_common.i.dfy"
include "entry.i.dfy"

predicate InterruptContinuationPreconditionDefInner()
{
    // for now, we only take interrupts at the beginning of another exception handler
    // when the user-entry precondition still holds, so this is simplest...
    forall s:state {:trigger InterruptContinuationPrecondition(s)} ::
        ValidState(s) && InterruptContinuationPrecondition(s)
        <==> (exists pagedb, dispPg:PageNr :: KomUserEntryPrecondition(s, pagedb, dispPg))
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

function {:opaque} dummyPageDb(): PageDb { imap[] }
function {:opaque} dummyPageNr(): PageNr { 0 }

predicate KomInterruptHandlerInvariant(s:state, sd:PageDb, r:state, dispPg:PageNr)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires s.conf.ex == ExFIQ || s.conf.ex == ExIRQ
    requires (priv_of_mode(spsr_of_state(s).m) == PL0
              || spsr_of_state(s).m == Supervisor) ==> (
        validPageDb(sd) && pageDbCorresponds(s.m, sd)
        && finalDispatcher(sd, dispPg))
{
    ValidState(r) && (s.ok ==> r.ok)
    && SaneStateAfterException(r)
    && ParentStackPreserving(s, r)
    && GlobalsPreservingExcept(s, r, {PendingInterruptOp()})
    && s.conf.ttbr0 == r.conf.ttbr0 && s.conf.scr == r.conf.scr
    && if (priv_of_mode(spsr_of_state(s).m) == PL1
          && spsr_of_state(s).m != Supervisor) then (
        // if interrupted in privileged !SVC mode, we just set the pending flag
        mode_of_state(r) == mode_of_state(s)
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
    ) else if (spsr_of_state(s).m == Supervisor) then (
        exists s':state :: ValidState(s') && evalExceptionTaken(s', ExFIQ, nondet_word(s'.conf.nondet, NONDET_PC()), s)
        && mode_of_state(s') != User && KomExceptionHandlerInvariant(s', sd, r, dispPg)
    ) else (
        KomExceptionHandlerInvariant(s, sd, r, dispPg)
    )
}

// this lemma is trivial, but justifies the soundness of the ARMdef assumptions
// ("EssentialInterruptContinuationInvariantProperties") about the handler
lemma lemma_KomInterruptHandlerInvariant_soundness(s:state, r:state)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires s.conf.ex == ExFIQ || s.conf.ex == ExIRQ
    requires priv_of_mode(spsr_of_state(s).m) == PL1 && spsr_of_state(s).m != Supervisor
    requires KomInterruptHandlerInvariant(s, dummyPageDb(), r, dummyPageNr())
    ensures EssentialInterruptContinuationInvariantProperties(s, r)
{
}

predicate {:opaque} InterruptContinuationInvariantDef()
{
    reveal ValidRegState();
    forall s:state, r:state
        | ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
          && (s.conf.ex == ExFIQ || s.conf.ex == ExIRQ)
          && priv_of_mode(spsr_of_state(s).m) == PL1
          && spsr_of_state(s).m != Supervisor
        :: InterruptContinuationInvariant(s, r)
        ==> KomInterruptHandlerInvariant(s, dummyPageDb(), r, dummyPageNr())
}

lemma lemma_InterruptContinuationInvariantDef(s:state, r:state)
    requires InterruptContinuationInvariantDef()
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires s.conf.ex == ExFIQ || s.conf.ex == ExIRQ
    requires priv_of_mode(spsr_of_state(s).m) == PL1 && spsr_of_state(s).m != Supervisor
    requires InterruptContinuationInvariant(s, r)
    ensures KomInterruptHandlerInvariant(s, dummyPageDb(), r, dummyPageNr())
    ensures s.conf.nondet == r.conf.nondet
    ensures s.conf.tlb_consistent == r.conf.tlb_consistent
{
    reveal InterruptContinuationInvariantDef();
    if priv_of_mode(spsr_of_state(s).m) == PL1 {
        assert s.conf.nondet == r.conf.nondet;
    }
}

lemma lemma_PrivInterruptInvariants(s:state, r:state)
    requires InterruptContinuationInvariantDef()
    requires ValidState(s) && SaneMem(s.m)
    requires priv_of_state(s) == PL1
    requires (mode_of_state(s) == Supervisor) ==> s.conf.cpsr.i && !stateTakesFiq(s)
    requires maybeHandleInterrupt(s, r)
    requires SaneStack(s)
    ensures mode_of_state(r) == mode_of_state(s)
    ensures r.conf.ttbr0 == s.conf.ttbr0 && r.conf.scr == s.conf.scr
    ensures r.conf.tlb_consistent == s.conf.tlb_consistent
    ensures r.rng == s.rng
    ensures SaneStack(r)
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
