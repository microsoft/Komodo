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
    requires priv_of_mode(spsr_of_state(s).m) == PL0 ==> (
        validPageDb(sd) && pageDbCorresponds(s.m, sd)
        && finalDispatcher(sd, dispPg))
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
                && s.regs[SP(m)] == r.regs[SP(m)]
{
    var nondet := nondet_word(s.conf.nondet, NONDET_EX());
    if !interrupts_enabled(s) {
        assert r == takestep(s);
    } else if (!s.conf.cpsr.f && nondet == 0) || (!s.conf.cpsr.i && nondet == 1) {
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
    } else {
        assert r == takestep(reseed_nondet_state(s));
    }
}

lemma lemma_svc_returning_verify_step0_helper(s:state, pagedb:PageDb, dispPg:PageNr, m1:memstate,
    m2:memstate, user_words:seq<word>, pagedb':PageDb, disp:PageDbEntryTyped, pg:memmap)
    requires SaneState(s);
    requires m1 == s.m;
    requires validPageDb(pagedb)
    requires pageDbCorresponds(m1, pagedb)
    requires validDispatcherPage(pagedb, dispPg)
    requires |user_words| == 8
    requires pagedb' == pagedb[dispPg := pagedb[dispPg].(entry := pagedb[dispPg].entry.(verify_words := user_words))]
    requires disp == pagedb'[dispPg].entry
    requires ValidMemState(m1) && ValidMemState(m2)
    requires pg == extractPage(m2, dispPg)
    requires
        forall i :: ValidMem(i) && !(0 <= i - (page_monvaddr(dispPg) + DISP_CTXT_USER_WORDS) <= 7 * WORDSIZE) ==> MemContents(m1, i) == MemContents(m2, i)
    requires
        forall i :: 0 <= i < 8 ==>
            var a := page_monvaddr(dispPg) + DISP_CTXT_USER_WORDS + i * WORDSIZE;
            MemContents(m2, a) == user_words[i]
    ensures pageDbDispatcherCorresponds(dispPg, disp, pg)
    ensures validDispatcherPage(pagedb', dispPg)
{
    assert pageDbDispatcherCorresponds(dispPg, disp, pg) by
    {
        reveal pageContentsCorresponds();
        reveal pageDbDispatcherCorresponds();
        reveal pageDbDispatcherContextCorresponds();
        reveal pageDbDispatcherVerifyStateCorresponds();

    }

    assert validDispatcherPage(pagedb', dispPg) by
    {
        reveal validPageDb();
        forall n | validPageNr(n) && n != dispPg && pagedb'[n].PageDbEntryTyped? && pagedb'[n].entry.Addrspace?
            ensures validPageDbEntry(pagedb', n)
        {
            assert addrspaceRefs(pagedb, n) == addrspaceRefs(pagedb', n); // set equality
        }
    }
}

lemma lemma_svc_returning_verify_step1_helper(s:state, pagedb:PageDb, dispPg:PageNr, m1:memstate,
    m2:memstate, user_words:seq<word>, pagedb':PageDb, disp:PageDbEntryTyped, pg:memmap)
    requires SaneState(s);
    requires m1 == s.m;
    requires validPageDb(pagedb)
    requires pageDbCorresponds(m1, pagedb)
    requires validDispatcherPage(pagedb, dispPg)
    requires |user_words| == 8
    requires pagedb' == pagedb[dispPg := pagedb[dispPg].(entry := pagedb[dispPg].entry.(verify_measurement := user_words))]
    requires disp == pagedb'[dispPg].entry
    requires ValidMemState(m2)
    requires pg == extractPage(m2, dispPg)
    requires
        forall i :: i in m1.addresses <==> i in m2.addresses
    requires
        forall i :: !(0 <= i - (page_monvaddr(dispPg) + DISP_CTXT_VERIFY_MEASUREMENT ) <= 7 * WORDSIZE) ==>
            i in m1.addresses ==> m1.addresses[i] == m2.addresses[i]
    requires
        forall i :: 0 <= i < 8 ==>
            var a := page_monvaddr(dispPg) + DISP_CTXT_VERIFY_MEASUREMENT + i * WORDSIZE;
            a in m2.addresses && m2.addresses[a] == user_words[i]
    ensures pageDbDispatcherCorresponds(dispPg, disp, pg)
    ensures validDispatcherPage(pagedb', dispPg)
{
    assert pageDbDispatcherCorresponds(dispPg, disp, pg) by
    {
        reveal pageContentsCorresponds();
        reveal pageDbDispatcherCorresponds();
        reveal pageDbDispatcherContextCorresponds();
        reveal pageDbDispatcherVerifyStateCorresponds();
    }

    assert validDispatcherPage(pagedb', dispPg) by
    {
        reveal validPageDb();
        forall n | validPageNr(n) && n != dispPg && pagedb'[n].PageDbEntryTyped? && pagedb'[n].entry.Addrspace?
            ensures validPageDbEntry(pagedb', n)
        {
            assert addrspaceRefs(pagedb, n) == addrspaceRefs(pagedb', n); // set equality
        }
    }
}

