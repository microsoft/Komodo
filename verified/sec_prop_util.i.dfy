include "sec_prop.s.dfy"
include "pagedb.s.dfy"
include "entry.s.dfy"
include "os_declass.s.dfy"

predicate contentsOk(physPage: word, contents: Maybe<seq<word>>)
{
    (physPage == 0 || physPageIsInsecureRam(physPage) ==> contents.Just?) &&
    (contents.Just? ==> |fromJust(contents)| == PAGESIZE / WORDSIZE)
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
        reveal_addrRangeSeq();
        reveal_addrSeqToContents();
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
    reveal_validEnclaveExecution();
    retToEnclave := (steps > 0);
    s5, d5 :|
        validEnclaveExecutionStep(s1, d1, s5, d5, dispPg, retToEnclave)
        && (if retToEnclave then
            validEnclaveExecution(s5, d5, rs, rd, dispPg, steps - 1)
          else
            rs == s5 && rd == d5);
}


//-----------------------------------------------------------------------------
// Enclave NI
//-----------------------------------------------------------------------------

predicate ni_reqs(s1: state, d1: PageDb, s1': state, d1': PageDb,
                  s2: state, d2: PageDb, s2': state, d2': PageDb,
                  atkr: PageNr)
{
    ValidState(s1) && ValidState(s1') && 
    ValidState(s2) && ValidState(s2') &&
    SaneConstants() &&
    validPageDb(d1) && validPageDb(d1') &&
    validPageDb(d2) && validPageDb(d2') &&
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    (forall n : PageNr :: d1[n].PageDbEntryFree? <==> d2[n].PageDbEntryFree?)
    /*
    SaneState(s1) && validPageDb(d1) && SaneState(s1') && validPageDb(d1') &&
    SaneState(s2) && validPageDb(d2) && SaneState(s2') && validPageDb(d2') &&
    pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s1'.m, d1') &&
    pageDbCorresponds(s2.m, d2) && pageDbCorresponds(s2'.m, d2') &&
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    (forall n : PageNr :: d1[n].PageDbEntryFree? <==> d2[n].PageDbEntryFree?)
    */
}

predicate ni_reqs_(d1: PageDb, d1': PageDb, d2: PageDb, d2': PageDb, atkr: PageNr)
{
    validPageDb(d1) && validPageDb(d1') &&
    validPageDb(d2) && validPageDb(d2') &&
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    // This is a slight weakening of the security property...
    (forall n : PageNr :: d1[n].PageDbEntryFree? <==> d2[n].PageDbEntryFree?)
}

// Note, the proofs seem to go faster if I don't just reference ni_reqs_weak_ 
// in ni_reqs_
predicate ni_reqs_weak_(d1: PageDb, d1': PageDb, d2: PageDb, d2': PageDb, atkr: PageNr)
{
    validPageDb(d1) && validPageDb(d1') &&
    validPageDb(d2) && validPageDb(d2') &&
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
}

predicate same_call_args(s1:state, s2: state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
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
