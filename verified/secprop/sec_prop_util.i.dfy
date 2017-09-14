include "sec_prop.s.dfy"
include "../pagedb.s.dfy"
include "../entry.s.dfy"
include "declass.s.dfy"
include "../smcapi.i.dfy"

predicate contentsOk(physPage: word, contents: Maybe<seq<word>>)
{
    (physPage == 0 || physPageIsInsecureRam(physPage) ==> contents.Just?) &&
    (contents.Just? ==> |fromJust(contents)| == PAGESIZE / WORDSIZE)
}

predicate same_ret(s1:state, s2:state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal ValidRegState();
    s1.regs[R0] == s2.regs[R0] &&
    s1.regs[R1] == s2.regs[R1]
}

lemma {:timeLimitMultiplier 2}
lemma_maybeContents_insec_ni(s1: state, s2: state, c1: Maybe<seq<word>>, 
        c2: Maybe<seq<word>>, physPage: word)
    requires ValidState(s1) && ValidState(s2) && SaneConstants()
    requires InsecureMemInvariant(s1, s2)
    requires c1 == maybeContentsOfPhysPage(s1, physPage)
    requires c2 == maybeContentsOfPhysPage(s2, physPage)
    ensures  c1 == c2;
{
    if(physPage == 0) {
        assert c1 == c2;
    } else if( physPageIsInsecureRam(physPage) ) {
        var base := physPage * PAGESIZE + KOM_DIRECTMAP_VBASE;
        forall( a: addr | base <= a < base + PAGESIZE)
            ensures MemContents(s1.m, a) == MemContents(s2.m, a)
        {
            assert physPage * PAGESIZE < MonitorPhysBase();
            assert KOM_DIRECTMAP_VBASE <= a < KOM_DIRECTMAP_VBASE + MonitorPhysBase()
                by { reveal PageAligned(); }
            assert InsecureMemInvariant(s1, s2);
        }
        assert contentsOfPhysPage(s1, physPage)
            == contentsOfPhysPage(s2, physPage) // seq equality
        by {
            reveal addrRangeSeq();
            reveal addrSeqToContents();
        }
        assert c1 == Just(contentsOfPhysPage(s1, physPage));
        assert c2 == Just(contentsOfPhysPage(s2, physPage));
        assert c1 == c2;
    } else {
        assert c1 == c2;
    }
}

lemma lemma_unpack_validEnclaveExecution(s1:state, d1:PageDb,
    rs:state, rd:PageDb, dispPg:PageNr, steps:nat)
    returns (retToEnclave:bool, s5:state, d5:PageDb)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires finalDispatcher(d1, dispPg)
    requires validEnclaveExecution(s1, d1, rs, rd, dispPg, steps)
    ensures retToEnclave == (steps > 0)
    ensures validEnclaveExecutionStep(s1, d1, s5, d5, dispPg, retToEnclave)
    ensures retToEnclave ==> ValidState(s5) && validPageDb(d5)
    ensures retToEnclave ==> finalDispatcher(d5, dispPg)
    ensures retToEnclave ==> validEnclaveExecution(s5, d5, rs, rd, dispPg, steps - 1)
    ensures !retToEnclave ==> rs == s5 && rd == d5
{
    reveal validEnclaveExecution();
    retToEnclave := (steps > 0);
    s5, d5 :|
        validEnclaveExecutionStep(s1, d1, s5, d5, dispPg, retToEnclave)
        && (if retToEnclave then
            validEnclaveExecution(s5, d5, rs, rd, dispPg, steps - 1)
          else
            rs == s5 && rd == d5);
}

lemma lemma_insecure_mem_userspace(
    s12: state, pc1: word, s13: state, expc1: word, ex1: exception,
    s22: state, pc2: word, s23: state, expc2: word, ex2: exception)
    requires validStates({s12, s13, s22, s23})
    requires SaneConstants()
    requires InsecureMemInvariant(s12, s22)
    requires s12.conf.nondet == s22.conf.nondet
    requires mode_of_state(s12) == mode_of_state(s22) == User;
    requires 
        var pt1 := ExtractAbsPageTable(s12);
        var pt2 := ExtractAbsPageTable(s22);
        pt1.Just? && pt2.Just? && pt1 == pt2
    requires userspaceExecutionFn(s12, pc1) == (s13, expc1, ex1)
    requires userspaceExecutionFn(s22, pc2) == (s23, expc2, ex2)
    ensures InsecureMemInvariant(s13, s23)
{
    reveal ValidMemState();
    var pt := ExtractAbsPageTable(s12).v;
    var pages := WritablePagesInTable(pt);

    forall( a | ValidMemForRead(a) && address_is_insecure(a) )
        ensures s13.m.addresses[a] == s23.m.addresses[a]
    {
        var m1 := insecureUserspaceMem(s12, pc1, a);
        var m2 := insecureUserspaceMem(s22, pc2, a);
        lemma_userspace_insecure_addr(s12, pc1, s13, a);
        lemma_userspace_insecure_addr(s22, pc2, s23, a);
        assert s13.m.addresses[a] == m1;
        assert s23.m.addresses[a] == m2;
        if(PageBase(a) in pages) {
            assert m1 == nondet_word(s12.conf.nondet, a);
            assert m2 == nondet_word(s22.conf.nondet, a);
            assert s12.conf.nondet == s22.conf.nondet;
        } else {
        }
    }
}

lemma lemma_allocatePageRefs(d: PageDb, addrspacePage:word, page:word,
    entry: PageDbEntryTyped, d': PageDb, e':word)
    requires validPageDb(d) && validPageDb(d')
    requires isAddrspace(d, addrspacePage)
    requires allocatePageEntryValid(entry)
    requires allocatePage(d, page, addrspacePage, entry) == (d', e')
    requires e' == KOM_ERR_SUCCESS
    ensures  dataPageRefs(d', addrspacePage, page) == {};
{
    lemma_freePageRefs(d, page);
}

lemma contentsDivBlock(physPage: word, contents: Maybe<seq<word>>)
    requires contentsOk(physPage, contents)
    requires contents.Just?
    ensures |fromJust(contents)| % SHA_BLOCKSIZE == 0
{
}

lemma lemma_user_regs_domain(regs:map<ARMReg, word>, hr:map<ARMReg, word>)
    requires ValidRegState(regs)
    requires hr == user_regs(regs)
    ensures  forall r :: r in hr <==> r in USER_REGS()
{
}

lemma eqregs(x: map<ARMReg,word>, y: map<ARMReg,word>)
	requires forall r :: r in x <==> r in y
	requires forall r | r in x :: x[r] == y[r]
	ensures x == y
	{}

lemma only_user_in_user_regs(r:ARMReg, m:mode)
    requires r == LR(m) && m != User
    ensures r !in USER_REGS() {}

lemma lemma_exceptionTakenRegs(s3:state, ex:exception, expc:word, s4:state)
    requires ValidState(s3) && ValidPsrWord(psr_of_exception(s3, ex))
    requires ValidState(s4)
    requires evalExceptionTaken(s3, ex, expc, s4)
    ensures user_regs(s4.regs) == user_regs(s3.regs)
    ensures OperandContents(s4, OLR) == expc
{
    lemma_evalExceptionTaken_Mode(s3, ex, expc, s4);
}


// Range used by InsecureMemInvariant
predicate address_is_insecure(m:addr) 
{
    KOM_DIRECTMAP_VBASE <= m < KOM_DIRECTMAP_VBASE + MonitorPhysBase()
}

predicate spsr_same(s1:state, s2:state)
    requires ValidState(s1) && ValidState(s2)
    requires mode_of_state(s1) != User
    requires mode_of_state(s2) != User
{
    reveal ValidSRegState();
    var spsr1 := spsr(mode_of_state(s1));
    var spsr2 := spsr(mode_of_state(s2));
    s1.sregs[spsr1] == s2.sregs[spsr2]
}

predicate cpsr_same(s1:state, s2:state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal ValidSRegState();
    s1.sregs[cpsr] == s2.sregs[cpsr] &&
    s1.conf.cpsr == s2.conf.cpsr
}

predicate ni_reqs(s1: state, d1: PageDb, s1': state, d1': PageDb,
                  s2: state, d2: PageDb, s2': state, d2': PageDb,
                  atkr: PageNr)
{
    SaneConstants() && do_declassify() &&
    ValidState(s1) && ValidState(s1') && 
    ValidState(s2) && ValidState(s2') &&
    validPageDb(d1) && validPageDb(d1') &&
    validPageDb(d2) && validPageDb(d2') &&
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    valAddrPage(d1', atkr) && valAddrPage(d2', atkr)
}

predicate ni_reqs_(d1: PageDb, d1': PageDb, d2: PageDb, d2': PageDb, atkr: PageNr)
{
    validPageDb(d1) && validPageDb(d1') &&
    validPageDb(d2) && validPageDb(d2') &&
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    valAddrPage(d1', atkr) && valAddrPage(d2', atkr)
}

predicate same_call_args(s1:state, s2: state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal ValidRegState();
    reveal ValidSRegState();
    OperandContents(s1, OReg(R0))  == OperandContents(s2, OReg(R0)) &&
    OperandContents(s1, OReg(R1))  == OperandContents(s2, OReg(R1)) &&
    OperandContents(s1, OReg(R2))  == OperandContents(s2, OReg(R2)) &&
    OperandContents(s1, OReg(R3))  == OperandContents(s2, OReg(R3)) &&
    OperandContents(s1, OReg(R4))  == OperandContents(s2, OReg(R4))
}

predicate entering_obs(d1: PageDb, d2: PageDb, disp: word, atkr: PageNr, is_resume:bool)
    requires validPageDb(d1) && validPageDb(d2)
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
{
    validPageNr(disp) &&
    d1[disp].PageDbEntryTyped? && d1[disp].entry.Dispatcher? &&
    d2[disp].PageDbEntryTyped? && d2[disp].entry.Dispatcher? &&
    d1[disp].addrspace == atkr && d2[disp].addrspace == atkr &&
    finalDispatcher(d1, disp) && finalDispatcher(d2, disp) &&
    smc_enter_err(d1, disp, is_resume) == KOM_ERR_SUCCESS &&
    smc_enter_err(d2, disp, is_resume) == KOM_ERR_SUCCESS
}

predicate obs_entry(d1: PageDb, d2: PageDb, disp: word, atkr: PageNr)
{
    validPageNr(disp) &&
    validPageDb(d1) && validPageDb(d2) &&
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    d1[disp].PageDbEntryTyped? && d1[disp].entry.Dispatcher? &&
    d2[disp].PageDbEntryTyped? && d2[disp].entry.Dispatcher? &&
    finalDispatcher(d1, disp) && finalDispatcher(d2, disp) &&
    d1[disp].addrspace == d2[disp].addrspace == atkr
}

predicate validStates(states:set<state>)
{
    forall s | s in states :: ValidState(s)
}

predicate validPageDbs(pagedbs:set<PageDb>)
{
    forall d | d in pagedbs :: validPageDb(d)
}

function insecureUserspaceMem(s:state, pc:word, a:addr): word
    requires ValidState(s)
    requires ValidMemForRead(a)
    requires !addrIsSecure(a)
    requires ExtractAbsPageTable(s).Just?
{
    var pt := ExtractAbsPageTable(s).v;
    var user_state := user_visible_state(s, pc, pt);
    var pages := WritablePagesInTable(pt);
    if( PageBase(a) in pages ) then nondet_word(s.conf.nondet, a)
    else MemContents(s.m, a)
}

lemma lemma_userspace_insecure_addr(s:state, pc: word, s3: state, a:addr)
    requires validStates({s, s3})
    requires mode_of_state(s) == User
    requires ValidMemForRead(a)
    requires !addrIsSecure(a)
    requires ExtractAbsPageTable(s).Just?
    requires userspaceExecutionFn(s, pc).0 == s3
    ensures  MemContents(s3.m, a) == insecureUserspaceMem(s, pc, a)
{
    var pt := ExtractAbsPageTable(s).v;
    var user_state := user_visible_state(s, pc, pt);
    var pages := WritablePagesInTable(pt);
    var newpsr := nondet_psr(s.conf.nondet, user_state, s.conf.cpsr);
    var hv := havocPages(pages, s, user_state);
    assert s3.m.addresses == hv by
        { reveal userspaceExecutionFn(); }
}
