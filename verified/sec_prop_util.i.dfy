include "sec_prop.s.dfy"
include "pagedb.s.dfy"
include "entry.s.dfy"
include "sec_prop_util.i.dfy"

//-----------------------------------------------------------------------------
// Enclave Confidentiality
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
    nonStoppedDispatcher(d1, disp) && nonStoppedDispatcher(d2, disp) &&
    smc_enter_err(d1, disp, is_resume) == KOM_ERR_SUCCESS &&
    smc_enter_err(d2, disp, is_resume) == KOM_ERR_SUCCESS
}

//-----------------------------------------------------------------------------
// OS Confidentiality
//-----------------------------------------------------------------------------

predicate os_ni_reqs(s1: state, d1: PageDb, s1': state, d1': PageDb,
                     s2: state, d2: PageDb, s2': state, d2': PageDb)
{
    ValidState(s1) && validPageDb(d1) && ValidState(s1') && validPageDb(d1') &&
    ValidState(s2) && validPageDb(d2) && ValidState(s2') && validPageDb(d2') &&
    SaneConstants() //&&
    // pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s1'.m, d1') &&
    // pageDbCorresponds(s2.m, d2) && pageDbCorresponds(s2'.m, d2')
}
