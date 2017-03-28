include "smcapi.s.dfy"
//include "pagedb.i.dfy"
include "pagedb.s.dfy"
// I need this until we figure out how to extract just the trusted parts
include "ptables.i.dfy"

/* 
 * If I recall correctly these exist / existed elsewhere... dig later
 */
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

predicate regs_equiv(s1:state, s2:state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
    OperandContents(s1, OReg(R0))  == OperandContents(s2, OReg(R0)) &&
    OperandContents(s1, OReg(R1))  == OperandContents(s2, OReg(R1)) &&
    OperandContents(s1, OReg(R2))  == OperandContents(s2, OReg(R2)) &&
    OperandContents(s1, OReg(R3))  == OperandContents(s2, OReg(R3)) &&
    OperandContents(s1, OReg(R4))  == OperandContents(s2, OReg(R4)) &&
    OperandContents(s1, OReg(R5))  == OperandContents(s2, OReg(R5)) &&
    OperandContents(s1, OReg(R6))  == OperandContents(s2, OReg(R6)) &&
    OperandContents(s1, OReg(R7))  == OperandContents(s2, OReg(R7)) &&
    OperandContents(s1, OReg(R8))  == OperandContents(s2, OReg(R8)) &&
    OperandContents(s1, OReg(R9))  == OperandContents(s2, OReg(R9)) &&
    OperandContents(s1, OReg(R10)) == OperandContents(s2, OReg(R10)) &&
    OperandContents(s1, OReg(R11)) == OperandContents(s2, OReg(R11)) &&
    OperandContents(s1, OReg(R12)) == OperandContents(s2, OReg(R12)) &&
    OperandContents(s1, OLR) == OperandContents(s2, OLR) &&
    OperandContents(s1, OSP) == OperandContents(s2, OSP)
}



// TODO somehow this broke... put it back...
// Like WritablePagesInTable but includes pages without the write bit set
/*
function PagesInTable(pt:AbsPTable): set<addr>
    requires WellformedAbsPTable(pt)
    ensures forall m:addr :: m in PagesInTable(pt) ==> PageAligned(m)
{
    (set i, j | 0 <= i < |pt| && pt[i].Just? && 0 <= j < |pt[i].v|
        && pt[i].v[j].Just?
        :: (assert WellformedAbsPTE(pt[i].v[j]);
          pt[i].v[j].v.phys + PhysBase()))
}
*/

//-----------------------------------------------------------------------------
//  Confidentiality, Malicious Enclave
//-----------------------------------------------------------------------------
// A malicious enclave can observe:
// 1. Pages it owns.
// 2. Public pages.
// 3. (A subset of the) registers *only* when the malicious enclave is executing.

// Our equivalent of an enclave number is a dispatcher page.

// Low-equivalence relation that relates two PageDbs that appear equivalent to 
// an attacker that controls an enclave "atkr". 
predicate enc_conf_eqpdb(d1:PageDb, d2: PageDb, atkr:PageNr)
    requires validPageDb(d1) && validPageDb(d2)
{
     valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
     // The set of pages that belong to the enclave is the same in both 
     // states.
     (forall n : PageNr :: pgInAddrSpc(d1, n, atkr) <==>
         pgInAddrSpc(d2, n, atkr)) &&
     // This together with two concrete states that refine d1, d2 ensure that 
     // the contents of the pages that belong to the enclave are the same in 
     // both states.
     (forall n : PageNr | pgInAddrSpc(d1, n, atkr) ::
         d1[n].entry == d2[n].entry)
}

// Low-equivalence relation that relates two concrete states that appear 
// equivalent to an attacker that controls an enclave "atkr". 
// A malicous attacker cannot observe anything when it is not executing

// The plan is to only check low-equivalence of states on entry/exit of 
// the enclave so this only needs to hold then. This equivalence relation need 
// not hold for smc calls other than enter/resume.
predicate enc_conf_eq_entry(s1:state, s2:state, d1:PageDb, d2:PageDb, 
    atkr:PageNr)
    requires SaneState(s1) && SaneState(s2)
    requires validPageDb(d1) && validPageDb(d2)
    requires pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s2.m, d2)
{
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    // valAddrPage(d1, d1[atkr].addrspace) && valAddrPage(d2, d2[atkr].addrspace) &&
    (var l1p := d1[atkr].entry.l1ptnr; // same in both d1, d2 because of eqdb
    nonStoppedL1(d1, l1p) <==> nonStoppedL1(d2, l1p) &&
    nonStoppedL1(d1, l1p) ==>
        (var atkr_pgs := WritablePagesInTable(mkAbsPTable(d1, l1p));
        // The set of pages the enclave can observe is the same
        // Note: I think the following is subsumed by eqdb.
        (WritablePagesInTable(mkAbsPTable(d1, l1p)) == 
            WritablePagesInTable(mkAbsPTable(d2, l1p))) &&
        // The contents of those addresses is the same
        (forall a | a in TheValidAddresses() && a in atkr_pgs ::
            s1.m.addresses[a] == s2.m.addresses[a]))
    ) 
}

// equivalent if enter/resume begin from s1 or s2
predicate enc_start_equiv(s1: state, s2: state)
    requires SaneState(s1) && SaneState(s2)
{
    forall r1:state, r2:state | entryTransition(s1, r1) && entryTransition(s2, r2) ::
        (regs_equiv(r1, r2) && r1.sregs[cpsr] == r2.sregs[cpsr] && 
        OperandContents(s1, OLR) == OperandContents(s2, OLR))
}

//-----------------------------------------------------------------------------
// Confidentiality, Malicious OS
//-----------------------------------------------------------------------------

predicate os_conf_eq(s1: state, s2: state)
    requires SaneState(s1) && SaneState(s2)
{
    reveal_ValidMemState();
    regs_equiv(s1, s2) && os_ctrl_eq(s1, s2) &&
    forall a: addr | addr_insecure(a) :: s1.m.addresses[a] == s2.m.addresses[a]
}

predicate os_ctrl_eq(s1: state, s2: state)
    requires SaneState(s1) && SaneState(s2)
{
    var spsr_ := OSReg(spsr(Supervisor));
    var cpsr_ := OSReg(cpsr);
    OperandContents(s1, spsr_) == OperandContents(s2, spsr_) &&
    OperandContents(s1, cpsr_) == OperandContents(s2, cpsr_)

}

predicate addr_insecure(a: addr)
{
    a in TheValidAddresses() && !address_is_secure(a) &&
        !(StackLimit() <= a < StackBase())
}

//-----------------------------------------------------------------------------
// Integrity, Malicious Enclave
//-----------------------------------------------------------------------------
// These relate states if the parts that the attacker cannot modify are the 
// same in both.
predicate enc_integ_eqpdb(d1:PageDb, d2: PageDb, atkr:PageNr)
    requires validPageDb(d1) && validPageDb(d2)
{
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    (forall n : PageNr :: pgInAddrSpc(d1, n, atkr) <==>
        pgInAddrSpc(d2, n, atkr)) &&
    // The pages outside of the attacker's address space are the same
    (forall n : PageNr | !pgInAddrSpc(d1, n, atkr) :: 
        d1[n].PageDbEntryTyped? <==> d2[n].PageDbEntryTyped?) &&
    (forall n : PageNr | !pgInAddrSpc(d1, n, atkr) && 
        d1[n].PageDbEntryTyped? ::
            d1[n].addrspace == d2[n].addrspace &&
            d1[n].entry == d2[n].entry)
}

predicate enc_integ_eq(s1:state, s2:state, d1:PageDb, d2:PageDb, 
    atkr:PageNr)
    requires SaneState(s1) && SaneState(s2)
    requires validPageDb(d1) && validPageDb(d2)
    requires pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s2.m, d2)
{
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    (var l1p := d1[atkr].entry.l1ptnr; // same in both d1, d2 because of eqdb
    nonStoppedL1(d1, l1p) <==> nonStoppedL1(d2, l1p) &&
    nonStoppedL1(d1, l1p) ==> (
        var atkr_pgs := WritablePagesInTable(mkAbsPTable(d1, l1p));
        // The set of pages the attacker can modify is the same
        (WritablePagesInTable(mkAbsPTable(d1, l1p)) == 
            WritablePagesInTable(mkAbsPTable(d2, l1p))) &&
        // The contents of pages the attacker cannot modify is the same
        (forall a | a in TheValidAddresses() && a !in atkr_pgs::
            s1.m.addresses[a] == s2.m.addresses[a])
    ))
}

