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

predicate pgInEnc(d: PageDb, n: PageNr, enc: PageNr)
    requires validPageDb(d) && valDispPage(d, enc)
{
    d[n].PageDbEntryTyped? && (d[n].addrspace == d[enc].addrspace)
}

//-----------------------------------------------------------------------------
// Protect confidentiality of an Enclave from other Enclaves 
//-----------------------------------------------------------------------------
// A malicious enclave can observe:
// 1. Pages it owns.
// 2. Public pages.
// 3. (A subset of the) registers *only* when the malicious enclave is executing.

// Our equivalent of an enclave number is a dispatcher page.

// Low-equivalence relation that relates two PageDbs that appear equivalent to 
// an attacker that controls an enclave "atkr". 
predicate enc_enc_conf_eqpdb(d1:PageDb, d2: PageDb, atkr:PageNr)
    requires validPageDb(d1) && validPageDb(d2)
    requires valDispPage(d1, atkr)
{
    var atkr_asp := d1[atkr].addrspace;
    // The disp page is the same in both states
    valDispPage(d2, atkr) &&
    d1[atkr].addrspace == d2[atkr].addrspace &&
    // The addrspace is an addrspace page in both states
    valAddrPage(d1, atkr_asp) && valAddrPage(d2, atkr_asp) &&
    // The set of pages that belong to the enclave is the same in both 
    // states.
    (forall n : PageNr :: pgInAddrSpc(d1, n, atkr_asp) <==>
        pgInAddrSpc(d2, n, atkr_asp)) &&
    // This together with two concrete states that refine d1, d2 ensure that 
    // the contents of the pages that belong to the enclave are the same in 
    // both states.
    (forall n : PageNr | pgInAddrSpc(d1, n, atkr_asp) ::
        d1[n].entry == d2[n].entry)
}

// Low-equivalence relation that relates two concrete states that appear 
// equivalent to an attacker that controls an enclave "atkr". 
// A malicous attacker cannot observe anything when it is not executing (but it 
// can always observe whether or not it is executing).
//
// The plan is to only check low-equivalence of states on entry/exit of 
// the enclave so this only needs to hold then. This equivalence relation need 
// not hold for smc calls other than enter/resume.
predicate enc_enc_conf_eq(s1:state, s2:state, d1:PageDb, d2:PageDb, 
    atkr:PageNr)
    requires SaneState(s1) && SaneState(s2)
    requires validPageDb(d1) && validPageDb(d2)
    requires pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s2.m, d2)
    requires valDispPage(d1, atkr)
    requires valAddrPage(d1, d1[atkr].addrspace)
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
{
    var atkr_asp := d1[atkr].addrspace;
    var l1p := d1[atkr_asp].entry.l1ptnr; // same in both d1, d2 because of eqdb
    regs_usr_equiv(s1, s2) &&
    configs_usr_equiv(s1, s2) &&
    nonStoppedL1(d1, l1p) <==> nonStoppedL1(d2, l1p) &&
    nonStoppedL1(d1, l1p) ==>
        (PagesInTable(mkAbsPTable(d1, l1p)) == 
            PagesInTable(mkAbsPTable(d2, l1p)))

}

predicate regs_usr_equiv(s1:state, s2:state)
    requires SaneState(s1) && SaneState(s2)
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
    // This contains the PC on both entry and exit from the enclave.
    OperandContents(s1, OLR) == OperandContents(s2, OLR)
}

predicate configs_usr_equiv(s1:state, s2: state)
    requires SaneState(s1) && SaneState(s2)
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
    // Using s.conf to determine whether or not the CPSR is equivalent would be 
    // insufficient here because a user process can read the value of the 
    // CPSR but the Config only models parts of the CPSR.
    OperandContents(s1, OSReg(cpsr)) == OperandContents(s2, OSReg(cpsr))
}

// Like WritablePagesInTable but includes pages without the write bit set

function PagesInTable(pt:AbsPTable): set<addr>
    requires WellformedAbsPTable(pt)
    ensures forall m:addr :: m in WritablePagesInTable(pt) ==> PageAligned(m)
{
    (set i, j | 0 <= i < |pt| && pt[i].Just? && 0 <= j < |pt[i].v|
        && pt[i].v[j].Just?
        :: (assert WellformedAbsPTE(pt[i].v[j]);
          pt[i].v[j].v.phys + PhysBase()))
}
