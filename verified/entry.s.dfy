include "ARMdef.s.dfy"
include "pagedb.s.dfy"
include "ptables.s.dfy"
include "svcapi.s.dfy"
include "addrseq.dfy"

// common success/failure checks for enter and resume
function smc_enter_err(d: PageDb, p: word, isresume: bool): word
    requires validPageDb(d)
{
    reveal validPageDb();
    if (!(validPageNr(p) && d[p].PageDbEntryTyped? && d[p].entry.Dispatcher?)) then
        KOM_ERR_INVALID_PAGENO
    else if (var a := d[p].addrspace; d[a].entry.state != FinalState) then
        KOM_ERR_NOT_FINAL
    else if (!isresume && d[p].entry.entered) then
        KOM_ERR_ALREADY_ENTERED
    else if (isresume && !d[p].entry.entered) then
        KOM_ERR_NOT_ENTERED
    else KOM_ERR_SUCCESS
}

function securePageFromPhysAddr(phys:word): PageNr
    requires PageAligned(phys)
    requires SecurePhysBase() <= phys < SecurePhysBase() +
        KOM_SECURE_NPAGES * PAGESIZE // physPageIsSecure(phys/PAGESIZE)
    ensures validPageNr(securePageFromPhysAddr(phys))
{
    (phys - SecurePhysBase()) / PAGESIZE
}

function contentsOfPage(s: state, p: PageNr) : seq<word>
    requires ValidState(s) && SaneConstants()
    ensures |contentsOfPage(s, p)| == PAGESIZE / WORDSIZE
{
    var base := page_monvaddr(p);
    assert |addrRangeSeq(base,base+PAGESIZE)| == PAGESIZE / WORDSIZE;
    addrSeqToContents(addrsInPage(p, base), s.m)
}

function updateUserPageFromState(s:state, d:PageDb, p:PageNr): PageDbEntry
    requires ValidState(s) && validPageDb(d) && SaneConstants()
    requires d[p].PageDbEntryTyped? && d[p].entry.DataPage?
{
    d[p].(entry := d[p].entry.(contents := contentsOfPage(s, p)))
}

function updateUserPagesFromState'(s:state, d:PageDb, dispPg:PageNr): PageDb
    requires ValidState(s) && validPageDb(d) && SaneConstants()
    requires finalDispatcher(d, dispPg)
{
    var l1p := l1pOfDispatcher(d, dispPg);
    imap p:PageNr :: if pageSWrInAddrspace(d, l1p, p)
        then updateUserPageFromState(s, d, p) else d[p]
}

lemma lemma_updateUserPagesFromState_validPageDb(s:state, d:PageDb, dispPg:PageNr)
    requires ValidState(s) && validPageDb(d) && SaneConstants()
    requires finalDispatcher(d, dispPg)
    ensures validPageDb(updateUserPagesFromState'(s, d, dispPg))
{
    var d' := updateUserPagesFromState'(s, d, dispPg);
    assert forall p:PageNr | d[p].PageDbEntryTyped? :: d'[p] ==
        if d[p].entry.DataPage?
        then d[p].(entry := d[p].entry.(contents := d'[p].entry.contents))
        else d[p];
    reveal validPageDb();
    forall (p:PageNr | d[p].PageDbEntryTyped?)
        ensures validPageDbEntryTyped(d', p)
    {
        assert validPageDbEntryTyped(d, p);
        if d[p].entry.DataPage? {
            assert dataPageRefs(d, d[p].addrspace, p)
                == dataPageRefs(d', d'[p].addrspace, p);
        }
        assert addrspaceRefs(d', p) == addrspaceRefs(d, p);
    }
    assert pageDbEntriesValid(d');
}

function {:opaque} updateUserPagesFromState(s:state, d:PageDb, dispPg:PageNr): PageDb
    requires ValidState(s) && validPageDb(d) && SaneConstants()
    requires finalDispatcher(d, dispPg)
    ensures var d' := updateUserPagesFromState(s, d, dispPg);
        validPageDb(d') && finalDispatcher(d', dispPg)
{
    lemma_updateUserPagesFromState_validPageDb(s, d, dispPg);
    updateUserPagesFromState'(s, d, dispPg)
}

predicate validEnclaveExecutionStep'(s1:state, d1:PageDb,
    s4:state, d4:PageDb, rs:state, rd:PageDb, dispPg:PageNr, retToEnclave:bool)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires finalDispatcher(d1, dispPg)
{
    var l1p := l1pOfDispatcher(d1, dispPg);
    assert nonStoppedL1(d1, l1p) by { reveal_validPageDb(); }

    pageTableCorresponds(s1, d1, l1p)
        && dataPagesCorrespond(s1.m, d1)
        && userspaceExecutionAndException(s1, s4)
        && d4 == updateUserPagesFromState(s4, d1, dispPg)
        && validExceptionTransition(s4, rs)
        // if we take an interrupt from the exception state, we don't return to the enclave
        && retToEnclave == (isReturningSvc(s4) && !(stateTakesFiq(s4) || stateTakesIrq(s4)))
        && (if retToEnclave then
            var (retRegs, rd') := svcHandled(s4, d4, dispPg);
            rd == rd' && preEntryReturn(s4, rs, retRegs, rd, dispPg)
          else reveal ValidRegState();
            (rs.regs[R0], rs.regs[R1], rd) == exceptionHandled(s4, d4, dispPg))
}

predicate {:opaque} validEnclaveExecutionStep(s1:state, d1:PageDb,
    rs:state, rd:PageDb, dispPg:PageNr, retToEnclave:bool)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires finalDispatcher(d1, dispPg)
{
    exists s4, d4
        :: validEnclaveExecutionStep'(s1, d1, s4, d4, rs, rd, dispPg,
                                     retToEnclave)
}

predicate {:opaque} validEnclaveExecution(s1:state, d1:PageDb,
    rs:state, rd:PageDb, dispPg:PageNr, steps:nat)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires finalDispatcher(d1, dispPg)
    decreases steps
{
    reveal validEnclaveExecutionStep();
    reveal updateUserPagesFromState();
    var retToEnclave := (steps > 0);
    exists s5, d5 {:trigger validEnclaveExecutionStep(s1, d1, s5, d5, dispPg, retToEnclave)} ::
        validEnclaveExecutionStep(s1, d1, s5, d5, dispPg, retToEnclave)
        && (if retToEnclave then
            validEnclaveExecution(s5, d5, rs, rd, dispPg, steps - 1)
          else
            rs == s5 && rd == d5)
}

predicate smc_enter(s: state, pageDbIn: PageDb, s':state, pageDbOut: PageDb,
                    dispPg: word, arg1: word, arg2: word, arg3: word)
    requires ValidState(s) && validPageDb(pageDbIn) && ValidState(s')
    requires SaneConstants()
{
    reveal ValidRegState();
    var err := smc_enter_err(pageDbIn, dispPg, false);
    if err != KOM_ERR_SUCCESS then
        pageDbOut == pageDbIn && s'.regs[R0] == err && s'.regs[R1] == 0 &&
        InsecureMemInvariant(s, s')
    else
        exists s1, steps:nat :: preEntryEnter(s, s1, pageDbIn, dispPg, arg1, arg2, arg3)
            && validEnclaveExecution(s1, pageDbIn, s', pageDbOut, dispPg, steps)
}

predicate smc_resume(s: state, pageDbIn: PageDb, s':state, pageDbOut: PageDb,
                     dispPg: word)
    requires ValidState(s) && validPageDb(pageDbIn) && ValidState(s')
    requires SaneConstants()
{
    reveal ValidRegState();
    var err := smc_enter_err(pageDbIn, dispPg, true);
    if err != KOM_ERR_SUCCESS then
        pageDbOut == pageDbIn && s'.regs[R0] == err && s'.regs[R1] == 0 &&
            InsecureMemInvariant(s, s')
    else
        exists s1, steps:nat :: preEntryResume(s, s1, pageDbIn, dispPg)
            && validEnclaveExecution(s1, pageDbIn, s', pageDbOut, dispPg, steps)
}

predicate preEntryCommon(s:state, d:PageDb, dispPage:PageNr)
    //requires smc_enter_err(d, dispPage, false) == KOM_ERR_SUCCESS
{
    ValidState(s) && validPageDb(d) && finalDispatcher(d, dispPage)
        && priv_of_state(s) == PL1
        // XXX: we don't really need the impl to set SCR.FIQ and
        // SCR.IRQ, but for the NI proof we need them to be constant,
        // and this is just the simplest way of specifying that
        && s.conf.scr == SCRT(Secure, true, true)
        && s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(d, dispPage))
        && s.conf.tlb_consistent
}

predicate preEntryEnter(s:state,s':state,d:PageDb,
    dispPage:PageNr,a1:word,a2:word,a3:word)
    requires ValidState(s)
    requires validPageDb(d)
    requires smc_enter_err(d, dispPage, false) == KOM_ERR_SUCCESS
    ensures preEntryEnter(s,s',d,dispPage,a1,a2,a3) ==>
        PageAligned(s'.conf.ttbr0.ptbase) &&
        SecurePhysBase() <= s'.conf.ttbr0.ptbase < SecurePhysBase() +
            KOM_SECURE_NPAGES * PAGESIZE
        && nonStoppedL1(d, securePageFromPhysAddr(s'.conf.ttbr0.ptbase))
{
    reveal validPageDb();
    reveal ValidRegState();

    s.conf.nondet == s'.conf.nondet && preEntryCommon(s', d, dispPage)
    && s'.regs[R0] == a1 && s'.regs[R1] == a2 && s'.regs[R2] == a3
    && (forall r | r in (USER_REGS() - {R0, R1, R2}) :: s'.regs[r] == 0)
    && OperandContents(s', OLR) == d[dispPage].entry.entrypoint
    && (reveal ValidSRegState();
        s'.sregs[spsr(mode_of_state(s'))] == encode_mode(User))
    && InsecureMemInvariant(s, s')
}

predicate preEntryResume(s:state, s':state, d:PageDb, dispPage:PageNr)
    requires ValidState(s) && validPageDb(d)
    requires smc_enter_err(d, dispPage, true) == KOM_ERR_SUCCESS
    ensures preEntryResume(s,s',d,dispPage) ==>
        PageAligned(s'.conf.ttbr0.ptbase) &&
        SecurePhysBase() <= s'.conf.ttbr0.ptbase < SecurePhysBase() +
            KOM_SECURE_NPAGES * PAGESIZE
    ensures preEntryResume(s,s',d,dispPage) ==>
        nonStoppedL1(d, securePageFromPhysAddr(s'.conf.ttbr0.ptbase));
{
    reveal validPageDb();
    var disp := d[dispPage].entry;
    var l1p := l1pOfDispatcher(d, dispPage);
    
    s.conf.nondet == s'.conf.nondet && preEntryCommon(s', d, dispPage)
    && (reveal ValidRegState();
        forall r | r in USER_REGS() :: s'.regs[r] == disp.ctxt.regs[r])
    && OperandContents(s', OLR) == disp.ctxt.pc
    && (reveal ValidSRegState();
        s'.sregs[spsr(mode_of_state(s'))] == disp.ctxt.cpsr)
    && InsecureMemInvariant(s, s')
}

predicate preEntryReturnRegsMatch(s:state, retregs:SvcReturnRegs)
    requires ValidState(s)
{
    reveal ValidRegState();
    s.regs[R0] == retregs.0
    && s.regs[R1] == retregs.1
    && s.regs[R2] == retregs.2
    && s.regs[R3] == retregs.3
    && s.regs[R4] == retregs.4
    && s.regs[R5] == retregs.5
    && s.regs[R6] == retregs.6
    && s.regs[R7] == retregs.7
    && s.regs[R8] == retregs.8
}

predicate preEntryReturnPreserved(s1:state, s2:state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal ValidRegState();
    s1.regs[R9] == s2.regs[R9] &&
    s1.regs[R10] == s2.regs[R10] &&
    s1.regs[R11] == s2.regs[R11] &&
    s1.regs[R12] == s2.regs[R12] &&
    s1.regs[LR(User)] == s2.regs[LR(User)] &&
    s1.regs[SP(User)] == s2.regs[SP(User)]
}

predicate preEntryReturn(exs:state, s:state, retregs:SvcReturnRegs, d:PageDb, dispPg:PageNr)
    requires ValidState(exs) && ValidState(s)
{
    reveal ValidRegState();
    preEntryCommon(s, d, dispPg)
    && s.conf.nondet == nondet_int(exs.conf.nondet, NONDET_GENERATOR())
    // returning to same PC
    && OperandContents(s, OLR) == OperandContents(exs, OLR)
    && (reveal ValidSRegState();
        s.sregs[spsr(mode_of_state(s))] == encode_mode(User))
    // R0-R8 return values
    && preEntryReturnRegsMatch(s, retregs)
    // other user regs preserved
    && preEntryReturnPreserved(s, exs)
}

predicate equivStates(s1:state, s2:state)
{
    s1.regs == s2.regs && s1.m == s2.m && s1.sregs == s2.sregs
        && s1.conf == s2.conf && s1.rng == s2.rng && s1.ok == s2.ok
}

predicate userspaceExecutionAndException'(s:state, s1:state, s2:state, r:state)
    requires ValidState(s)
{
    equivStates(s, s1) && evalUserExecution(s1, s2, r)
    && mode_of_state(r) != User // known, but we need a lemma to prove it
}

predicate {:opaque} userspaceExecutionAndException(s:state, r:state)
    requires ValidState(s)
    ensures userspaceExecutionAndException(s, r)
        ==> ValidState(r) && mode_of_state(r) != User
{
    exists s1, s2 :: userspaceExecutionAndException'(s, s1, s2, r)
}

//-----------------------------------------------------------------------------
// Exception Handler Spec
//-----------------------------------------------------------------------------
function exceptionHandled(s:state, d:PageDb, dispPg:PageNr): (word, word, PageDb)
    requires validPageDb(d) && validDispatcherPage(d, dispPg)
    requires ValidState(s) && mode_of_state(s) != User
    ensures var (r0, r1, d') := exceptionHandled(s, d, dispPg);
        wellFormedPageDb(d')
{
    reveal validPageDb();
    reveal ValidRegState();
    if s.conf.ex.ExAbt? || s.conf.ex.ExUnd? || (s.conf.ex.ExSVC? && !isReturningSvc(s)) then (
        // voluntary exit / fault
        var p := dispPg;
        var d' := d[ p := d[p].(entry := d[p].entry.(entered := false))];
        if s.conf.ex.ExSVC? then
            (KOM_ERR_SUCCESS, s.regs[R1], d')
        else
            (KOM_ERR_FAULT, 0, d')
    ) else (
        // model the fact that an SVC _might_ be treated as an opportunity to interrupt execution
        assert s.conf.ex.ExIRQ? || s.conf.ex.ExFIQ? || isReturningSvc(s);
        reveal ValidSRegState();
        var p := dispPg;
        // ARM spec B1.8.3 "Link values saved on exception entry"
        var pc := if s.conf.ex.ExIRQ? || s.conf.ex.ExFIQ? then TruncateWord(OperandContents(s, OLR) - 4) else OperandContents(s, OLR);
        var psr := s.sregs[spsr(mode_of_state(s))];
        var ctxt' := DispatcherContext(user_regs(s.regs), pc, psr);
        var disp' := d[p].entry.(entered:=true, ctxt:=ctxt');
        var d' := d[ p := d[p].(entry := disp') ];
        (KOM_ERR_INTERRUPTED, 0, d')
    )
}

predicate validExceptionTransition(s:state, s':state)
{
    ValidState(s) && ValidState(s')
    && InsecureMemInvariant(s, s')
    && mode_of_state(s') == Monitor
}

predicate WSMemInvariantExceptAddrspaceAtPage(hw:state, hw':state, 
        d:PageDb, l1p:PageNr)
    requires ValidState(hw) && ValidState(hw') && nonStoppedL1(d, l1p)
{
    forall a | ValidMem(a) && address_is_secure(a) && !memSWrInAddrspace(d, l1p, a) ::
        MemContents(hw.m, a) == MemContents(hw'.m, a)
}


// Is the page secure, writeable, and in the L1PT
predicate pageSWrInAddrspace(d:PageDb, l1p:PageNr, p:PageNr)
    requires validPageNr(p) && nonStoppedL1(d, l1p)
{
    reveal validPageDb();
    !hasStoppedAddrspace(d, l1p) && 
    var l1pt := d[l1p].entry.l1pt;
    exists p' :: Just(p') in l1pt && assert validL1PTE(d, p'); pageSWrInL2PT(d[p'].entry.l2pt,p)
}

predicate memSWrInAddrspace(d:PageDb, l1p:PageNr, m: addr)
    requires validL1PTPage(d, l1p) && !hasStoppedAddrspace(d, l1p)
{
    exists p | validPageNr(p) :: pageSWrInAddrspace(d, l1p, p) && addrInPage(m, p)
}

// is the page secure, writeable, and in the L2PT
predicate pageSWrInL2PT(l2pt:seq<L2PTE>, p:PageNr)
{
    exists pte :: pte in l2pt && pte.SecureMapping? && pte.page == p && pte.write
}
