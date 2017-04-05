include "smcapi.s.dfy"
//include "pagedb.i.dfy"
include "pagedb.s.dfy"
// I need this until we figure out how to extract just the trusted parts
// include "ptables.i.dfy"

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
predicate {:opaque} enc_conf_eqpdb(d1:PageDb, d2: PageDb, atkr:PageNr)
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

// This relation is used to describe two states from which attacker entry 
// begins. It isused to set sources of nondeterminism equal so 
// that we can reason about what the attacker observes during execution without 
// needing to prove that this nondeterministic system is deterministic.

// The entry spec can pass around the value bad_enclave to each of the 
// existentially reached states so that we can assume sources of nondeterminism 
// for each state reached after the executions beginning from s1 and s2

predicate enc_conf_eq_entry(s1:state, s2:state, d1:PageDb, d2:PageDb, 
    atkr:PageNr)
    requires ValidState(s1) && ValidState(s2)
    //requires validPageDb(d1) && validPageDb(d2)
    // requires pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s2.m, d2)
{
    s1.nd_private == s2.nd_private &&
    s1.nd_public  == s2.nd_public
}

//-----------------------------------------------------------------------------
// Confidentiality, Malicious OS
//-----------------------------------------------------------------------------

predicate os_conf_eq(s1: state, s2: state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal_ValidMemState();
    s1.nd_public == s2.nd_public && 
    os_regs_equiv(s1, s2) &&
    os_ctrl_eq(s1, s2) // &&
    // InsecureMemInvariant(s1, s2)
}

predicate os_ctrl_eq(s1: state, s2: state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal_ValidSRegState();
    var spsr_f  := spsr(FIQ);
    var spsr_i  := spsr(IRQ);
    var spsr_s  := spsr(Supervisor);
    var spsr_a  := spsr(Abort);
    var spsr_u  := spsr(Undefined);
    var cpsr_   := cpsr;
    s1.sregs[spsr_f] == s2.sregs[spsr_f] &&
    s1.sregs[spsr_i] == s2.sregs[spsr_i] &&
    s1.sregs[spsr_s] == s2.sregs[spsr_s] &&
    s1.sregs[spsr_a] == s2.sregs[spsr_a] &&
    s1.sregs[spsr_u] == s2.sregs[spsr_u] &&
    s1.sregs[cpsr_]  == s2.sregs[cpsr_]

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
   s1.regs[LR(FIQ)]        == s2.regs[LR(FIQ)] &&
   s1.regs[LR(IRQ)]        == s2.regs[LR(IRQ)] &&
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

/*
predicate enc_integ_eq(s1:state, s2:state, d1:PageDb, d2:PageDb, 
    atkr:PageNr)
    requires SaneState(s1) && SaneState(s2)
    requires validPageDb(d1) && validPageDb(d2)
    requires pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s2.m, d2)
{
    s1.public == s2.public &&
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
*/
