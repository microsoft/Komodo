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

// Low-equivalence relation that relates two PageDbs that appear equivalent to 
// an attacker that controls an enclave in addrspace "atkr". 
predicate enc_enc_conf_eqpdb(d1:PageDb, d2: PageDb, atkr:PageNr)
    requires validPageDb(d1) && validPageDb(d2)
    requires valDispPage(d1, atkr)
{
    var atkr_asp := d1[atkr].addrspace;
    valDispPage(d2, atkr) &&
    d1[atkr].addrspace == d2[atkr].addrspace &&
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    (forall n : PageNr :: pgInAddrSpc(d1, n, atkr) <==>
        pgInAddrSpc(d2, n, atkr)) &&
    (forall n : PageNr | pgInAddrSpc(d1, n, atkr) ::
        d2[n].PageDbEntryTyped? && d1[n].entry == d2[n].entry)
}

// Low-equivalence relation that relates two concrete states that appear 
// equivalent to an attacker that controls an enclave in adddrspace "atkr". 
// A malicous attacker cannot observe anything when it is not executing (but it 
// can always observe whether or not it is executing).
//
// The plan is to only check low-equivalence of states on entry/exit of 
// the enclave so this only needs to hold then.
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
    regs_usr_equiv(s1.regs, s2.regs) &&
    configs_usr_equiv(s1.conf, s2.conf) &&
    nonStoppedL1(d1, l1p) ==>
        (PagesInTable(mkAbsPTable(d1, l1p)) == 
            PagesInTable(mkAbsPTable(d2, l1p)))

}

predicate regs_usr_equiv(r1:map<ARMReg,word>, r2:map<ARMReg,word>)
    requires ValidRegState(r1) && ValidRegState(r2)
{
    reveal_ValidRegState();
    r1[R0]  == r2[R0] &&
    r1[R1]  == r2[R1] &&
    r1[R2]  == r2[R2] &&
    r1[R3]  == r2[R3] &&
    r1[R4]  == r2[R4] &&
    r1[R5]  == r2[R5] &&
    r1[R6]  == r2[R6] &&
    r1[R7]  == r2[R7] &&
    r1[R8]  == r2[R8] &&
    r1[R9]  == r2[R9] &&
    r1[R10] == r2[R10] &&
    r1[R11] == r2[R11] &&
    r1[R12] == r2[R12] &&
    r1[SP(User)] == r2[SP(User)] &&
    r1[LR(User)] == r2[LR(User)]
}

predicate configs_usr_equiv(c1:config, c2:config)
{
    // AFAIK nothing is visible in usermode
    true
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
