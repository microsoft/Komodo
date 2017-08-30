include "sec_prop.s.dfy"
include "../pagedb.s.dfy"
include "../entry.s.dfy"
include "os_declass.s.dfy"

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

lemma lemma_maybeContents_insec_ni(s1: state, s2: state, c1: Maybe<seq<word>>, 
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
        forall( a: PageNr | base <= a < base + PAGESIZE)
            ensures s1.m.addresses[a] == s2.m.addresses[a]
        {
        }
        reveal addrRangeSeq();
        reveal addrSeqToContents();
        assert c1 == Just(contentsOfPhysPage(s1, physPage));
        assert c2 == Just(contentsOfPhysPage(s2, physPage));
        assert contentsOfPhysPage(s1, physPage)
            == contentsOfPhysPage(s2, physPage); // seq equality
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

lemma lemma_enc_eqpdb_transitive(d1: PageDb, d2: PageDb, d3: PageDb, atkr: PageNr)
    requires validPageDb(d1) && validPageDb(d2) && validPageDb(d3)
    requires enc_eqpdb(d1, d2, atkr)
    requires enc_eqpdb(d2, d3, atkr)
    ensures  enc_eqpdb(d1, d3, atkr)
{
    reveal enc_eqpdb();
}

lemma lemma_enc_eqpdb_assoc(d1: PageDb, d2: PageDb, atkr: PageNr)
    requires validPageDb(d1) && validPageDb(d2)
    requires enc_eqpdb(d1, d2, atkr)
    ensures enc_eqpdb(d2, d1, atkr)
{
    reveal enc_eqpdb();
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

    forall( a | ValidMem(a) && address_is_insecure(a) )
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

// Range used by InsecureMemInvariant
predicate address_is_insecure(m:addr) 
{
    KOM_DIRECTMAP_VBASE <= m < KOM_DIRECTMAP_VBASE + MonitorPhysBase()
}


//-----------------------------------------------------------------------------
// Enclave NI
//-----------------------------------------------------------------------------

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

predicate entering_atkr(d1: PageDb, d2: PageDb, disp: word, atkr: PageNr, is_resume:bool)
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

//-----------------------------------------------------------------------------
// OS NI
//-----------------------------------------------------------------------------

predicate os_ni_reqs(s1: state, d1: PageDb, s1': state, d1': PageDb,
                     s2: state, d2: PageDb, s2': state, d2': PageDb)
{
    ValidState(s1) && validPageDb(d1) && ValidState(s1') && validPageDb(d1') &&
    ValidState(s2) && validPageDb(d2) && ValidState(s2') && validPageDb(d2') &&
    SaneConstants() && do_declassify()
}

//-----------------------------------------------------------------------------
// Random Stuff
//-----------------------------------------------------------------------------
predicate validStates(states:set<state>)
{
    forall s | s in states :: ValidState(s)
}

predicate validPageDbs(pagedbs:set<PageDb>)
{
    forall d | d in pagedbs :: validPageDb(d)
}
