include "smcapi.s.dfy"
include "pagedb.s.dfy"

predicate valDispPage(d: PageDb, n: PageNr)
    requires validPageDb(d)
{
    d[n].PageDbEntryTyped? && d[n].entry.Dispatcher?
}

predicate valAddrPage(d: PageDb, n: PageNr)
    requires validPageDb(d)
{
    d[n].PageDbEntryTyped? && d[n].entry.Addrspace?
}

predicate pgInAddrSpc(d: PageDb, n: PageNr, a: PageNr)
    requires validPageDb(d) && valAddrPage(d, a)
{
    d[n].PageDbEntryTyped? && d[n].addrspace == a
}

predicate usr_regs_equiv(s1:state, s2:state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
    s1.regs[R0]  == s2.regs[R0] &&
    s1.regs[R1]  == s2.regs[R1] &&
    s1.regs[R2]  == s2.regs[R2] &&
    s1.regs[R3]  == s2.regs[R3] &&
    s1.regs[R4]  == s2.regs[R4] &&
    s1.regs[R5]  == s2.regs[R5] &&
    s1.regs[R6]  == s2.regs[R6] &&
    s1.regs[R7]  == s2.regs[R7] &&
    s1.regs[R8]  == s2.regs[R8] &&
    s1.regs[R9]  == s2.regs[R9] &&
    s1.regs[R10] == s2.regs[R10] &&
    s1.regs[R11] == s2.regs[R11] &&
    s1.regs[R12] == s2.regs[R12] &&
    s1.regs[SP(User)] == s2.regs[SP(User)] &&
    s1.regs[LR(User)] == s2.regs[LR(User)]
}

//-----------------------------------------------------------------------------
// Enclaves are NI with other Enclaves 
//-----------------------------------------------------------------------------

// Our equivalent of an enclave number is a dispatcher page.

// Low-equivalence relation that relates two PageDbs that appear equivalent to 
// an attacker that controls an enclave "atkr". 
predicate {:opaque} enc_eqpdb(d1:PageDb, d2: PageDb, atkr:PageNr)
    requires validPageDb(d1) && validPageDb(d2)
{
    d1[atkr].PageDbEntryTyped? <==> d2[atkr].PageDbEntryTyped? &&
    (d1[atkr].PageDbEntryTyped? ==>
    (valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    // The set of pages that belong to the enclave is the same in both 
    // states.
    (forall n : PageNr :: pgInAddrSpc(d1, n, atkr) <==>
        pgInAddrSpc(d2, n, atkr)) &&
    // This together with two concrete states that refine d1, d2 ensure that 
    // the contents of the pages that belong to the enclave are the same in 
    // both states.
    (forall n : PageNr | pgInAddrSpc(d1, n, atkr) ::
        d1[n].entry == d2[n].entry)))
}

//-----------------------------------------------------------------------------
// Confidentiality, Malicious OS
//-----------------------------------------------------------------------------

predicate os_eqentry(e1:PageDbEntryTyped, e2:PageDbEntryTyped)
{
    match e1
        case Addrspace(_,_,_) => e1 == e2
        case L1PTable(_) => e1 == e2
        case L2PTable(_) => e1 == e2
        case Dispatcher(_,_,_) => e2.Dispatcher? &&
            e2.entered == e1.entered && e2.entrypoint == e1.entrypoint
        case DataPage(_) => e2.DataPage?
}

predicate {:opaque} os_eqpdb(d1:PageDb, d2:PageDb)
    requires validPageDb(d1) && validPageDb(d2)
{
    (forall n: PageNr ::
        d1[n].PageDbEntryTyped? <==> d2[n].PageDbEntryTyped?) &&
    (forall n : PageNr | d1[n].PageDbEntryTyped? ::
        os_eqentry(d1[n].entry, d2[n].entry) &&
        d1[n].addrspace == d2[n].addrspace)
}

predicate os_eq(s1: state, d1: PageDb, s2: state, d2: PageDb)
    requires ValidState(s1) && ValidState(s2)
    requires validPageDb(d1) && validPageDb(d2)
{
    reveal_ValidMemState();
    os_regs_equiv(s1, s2) &&
    os_ctrl_eq(s1, s2) &&
    InsecureMemInvariant(s1, s2) &&
    os_eqpdb(d1, d2)
}

predicate os_ctrl_eq(s1: state, s2: state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal_ValidSRegState();
    forall m | m in {Supervisor, Abort, Undefined} ::
        s1.sregs[spsr(m)] == s2.sregs[spsr(m)]

}

predicate os_regs_equiv(s1: state, s2: state)
    requires ValidState(s1) && ValidState(s2)
{
   reveal_ValidRegState();
   reveal_ValidSRegState();
   s1.regs[R0]  == s2.regs[R0] &&
   s1.regs[R1]  == s2.regs[R1] &&
   s1.regs[R2]  == s2.regs[R2] &&
   s1.regs[R3]  == s2.regs[R3] &&
   s1.regs[R4]  == s2.regs[R4] &&
   s1.regs[R5]  == s2.regs[R5] &&
   s1.regs[R6]  == s2.regs[R6] &&
   s1.regs[R7]  == s2.regs[R7] &&
   s1.regs[R8]  == s2.regs[R8] &&
   s1.regs[R9]  == s2.regs[R9] &&
   s1.regs[R10] == s2.regs[R10] &&
   s1.regs[R11] == s2.regs[R11] &&
   s1.regs[R12] == s2.regs[R12] &&
   s1.regs[LR(User)]       == s2.regs[LR(User)] &&
   // s1.regs[LR(FIQ)]        == s2.regs[LR(FIQ)] &&
   // s1.regs[LR(IRQ)]        == s2.regs[LR(IRQ)] &&
   s1.regs[LR(Supervisor)] == s2.regs[LR(Supervisor)] &&
   s1.regs[LR(Abort)]      == s2.regs[LR(Abort)] &&
   s1.regs[LR(Undefined)]  == s2.regs[LR(Undefined)] &&
   s1.regs[SP(User)]       == s2.regs[SP(User)] &&
   s1.regs[SP(FIQ)]        == s2.regs[SP(FIQ)] &&
   s1.regs[SP(IRQ)]        == s2.regs[SP(IRQ)] &&
   s1.regs[SP(Supervisor)] == s2.regs[SP(Supervisor)] &&
   s1.regs[SP(Abort)]      == s2.regs[SP(Abort)] &&
   s1.regs[SP(Undefined)]  == s2.regs[SP(Undefined)]
}
