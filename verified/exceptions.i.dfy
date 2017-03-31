include "kom_common.i.dfy"
include "entry.i.dfy"

function {:opaque} dummyPageDb(): PageDb { imap[] }
function {:opaque} dummyPageNr(): PageNr { 0 }

predicate KomInterruptHandlerInvariant(s:state, sd:PageDb, r:state, dispPg:PageNr)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires s.conf.ex == ExFIQ || s.conf.ex == ExIRQ
    requires priv_of_mode(spsr_of_state(s).m) == PL0 ==> (
        validPageDb(sd) && pageDbCorresponds(s.m, sd)
        && nonStoppedDispatcher(sd, dispPg))
{
    ValidState(r) && (s.ok ==> r.ok)
    && SaneStateAfterException(r)
    && ParentStackPreserving(s, r)
    && GlobalsPreservingExcept(s, r, {PendingInterruptOp()})
    && s.conf.ttbr0 == r.conf.ttbr0 && s.conf.scr == r.conf.scr
    && if priv_of_mode(spsr_of_state(s).m) == PL1 then (
        // if interrupted in privileged mode, we just set the pending flag
        mode_of_state(r) == mode_of_state(s)
        && spsr_of_state(r) == spsr_of_state(s)
        && CoreRegPreservingExcept(s, r, {OLR})
        // see B1.8.3 "Link values saved on exception entry"
        && OperandContents(r, OLR) == TruncateWord(OperandContents(s, OLR) - 4)
        && BankedRegsInvariant(s, r)
        && NonStackMemPreserving(s, r)
        && SaneStack(r)
    ) else (
        mode_of_state(s) != User
        && KomExceptionHandlerInvariant(s, sd, r, dispPg)
    )
}

// this lemma is trivial, but justifies the soundness of the ARMdef assumptions
// ("EssentialContinuationInvariantProperties") about the handler
lemma lemma_KomInterruptHandlerInvariant_soundness(s:state, r:state)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires s.conf.ex == ExFIQ || s.conf.ex == ExIRQ
    requires priv_of_mode(spsr_of_state(s).m) == PL1
    requires KomInterruptHandlerInvariant(s, dummyPageDb(), r, dummyPageNr())
    ensures EssentialContinuationInvariantProperties(s, r)
{}

predicate {:opaque} InterruptContinuationInvariantDef()
{
    reveal_ValidRegState();
    forall s:state, r:state
        | ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
          && (s.conf.ex == ExFIQ || s.conf.ex == ExIRQ)
          && priv_of_mode(spsr_of_state(s).m) == PL1
        :: InterruptContinuationInvariant(s, r)
        ==> KomInterruptHandlerInvariant(s, dummyPageDb(), r, dummyPageNr())
}

lemma lemma_InterruptContinuationInvariantDef(s:state, r:state)
    requires InterruptContinuationInvariantDef()
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires s.conf.ex == ExFIQ || s.conf.ex == ExIRQ
    requires priv_of_mode(spsr_of_state(s).m) == PL1
    requires InterruptContinuationInvariant(s, r)
    ensures KomInterruptHandlerInvariant(s, dummyPageDb(), r, dummyPageNr())
{
    reveal_InterruptContinuationInvariantDef();
}

lemma lemma_PrivInterruptInvariants(s:state, r:state)
    requires InterruptContinuationInvariantDef()
    requires ValidState(s) && SaneMem(s.m)
    requires priv_of_state(s) == PL1
    requires maybeHandleInterrupt(s, r)
    requires SaneStack(s)
    ensures mode_of_state(r) == mode_of_state(s)
    ensures r.conf.ttbr0 == s.conf.ttbr0 && r.conf.scr == s.conf.scr
    ensures SaneStack(r)
    ensures StackPreserving(s, r)
    ensures NonStackMemPreserving(s, r)
    ensures GlobalsPreservingExcept(s, r, {PendingInterruptOp()})
    ensures CoreRegPreservingExcept(s, r, {OLR})
    ensures forall m :: m != mode_of_exception(s.conf, ExIRQ)
            && m != mode_of_exception(s.conf, ExFIQ)
            ==> s.regs[LR(m)] == r.regs[LR(m)]
{
    var nondet := nondeterministic_word(s, -1);
    if (!s.conf.cpsr.f && nondet == 0) || (!s.conf.cpsr.i && nondet == 1) {
        ghost var ex := if nondet == 0 then ExFIQ else ExIRQ;
        assert handleInterrupt(s, ex, r);
        var s1, s2 :| evalExceptionTaken(s, ex, s1)
            && InterruptContinuationInvariant(s1, s2)
            && evalMOVSPCLR(s2, r);
        lemma_evalExceptionTaken_Mode(s, ex, s1);
        lemma_InterruptContinuationInvariantDef(s1, s2);
        forall m | m != mode_of_exception(s.conf, ex)
            ensures s.regs[LR(m)] == r.regs[LR(m)]
        {
            calc {
                s.regs[LR(m)];
                s1.regs[LR(m)];
                s2.regs[LR(m)];
                r.regs[LR(m)];
            }
        }
        calc {
            s.regs[SP(Monitor)];
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
    } else {
        assert r == takestep(s);
    }
}
