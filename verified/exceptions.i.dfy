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
    && SaneMem(r.m)
    && SaneStack(r)
    && ParentStackPreserving(s, r)
    && GlobalsPreservingExcept(s, r, {PendingInterruptOp()})
    && s.conf.ttbr0 == r.conf.ttbr0 && s.conf.scr == r.conf.scr
    && if priv_of_mode(spsr_of_state(s).m) == PL1 then (
        // if interrupted in privileged mode, we just set the pending flag
        mode_of_state(r) == mode_of_state(s)
        && spsr_of_state(r) == spsr_of_state(s)
        && CoreRegPreservingExcept(s, r, {})
        && BankedRegsInvariant(s, r)
        && NonStackMemPreserving(s, r)
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
