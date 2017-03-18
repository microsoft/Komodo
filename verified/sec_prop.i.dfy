include "smcapi.s.dfy"
include "pagedb.i.dfy"
include "ptables.i.dfy"

/* 
 * If I recall correctly these exist / existed elsewhere... dig later
 */
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

// I am not sure if we have a well-defined notion of an "enclave number" aside 
// from an addrspace page, so I am using addrspace pages as an enclave number 
// in this file.

// Should be true if the enclave in addrspace a is currently executing.
// I'm not sure if we have a better way of testing whether or not an enclave is 
// currently executing.
predicate isEncExecuting(s:state, d:pagedb, a:PageNr)
    requires SaneState(s) && validPageDb(d) && pageDbCorresponds(s, d)
    requires valAddrPage(d, a)
{
    s.conf.ttbr0.ptbase == page_paddr(l1p)
}

//-----------------------------------------------------------------------------
// Protect confidentiality of an Enclave from other Enclaves 
//-----------------------------------------------------------------------------
// A malicious enclave can observe:
// 1. Pages it owns.
// 2. Public pages.
// 3. Registers *only* when the malicious enclave is executing.

// Low-equivalence relation that relates two PageDbs that appear equivalent to 
// an attacker that controls an enclave in addrspace "atkr". 
predicate enc_enc_conf_eqpdb(d1:pagedb, d2: pagedb, atkr:PageNr)
    requires validPageDb(d1) && validPageDb(d2)
    requires valAddrPage(d1, atkr)
{
    valAddrPage(d2, atkr) &&
    (forall n : PageNr :: pgInAddrSpc(d1, n, atkr) <==>
        pgInAddrSpc(d2, n, atkr)) &&
    (forall n : PageNr | pgInAddrSpc(d1, n, atkr) ::
        d2[n].PageDbEntryTyped? && d1[n].entry == d2[n].entry)
}

// Low-equivalence relation that relates two concrete states that appear 
// equivalent to an attacker that controls an enclave in adddrspace "atkr". 
// A malicous attacker cannot observe anything when it is not executing (but it 
// can always observe whether or not it is executing).
predicate enc_enc_conf_eq(s1:state, s2:state, d1:pagedb, d2:pagedb, 
    atkr:PageNr)
    requires SaneState(s1) && SaneState(s2)
    requires validPageDb(d1) && validPageDb(d2)
    requires pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s2.m, d2)
    requires valAddrPage(d1, atkr)
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
{
    var l1p := d1[atkr].entry.l1ptnr // same in both d1, d2 because of precond
    (isEncExecuting(s1, d1, atkr) <==> isEncExecuting(s2, d2, atkr)) &&
    (isEncExecuting(s1, d1, atkr) ==>
        s1.regs == s2.regs &&
        s1.sregs == s2.sregs &&
        PagsInTable(mkAbsPTable(d1, l1p)) == 
            PagsInTable(mkAbsPTable(d2, l1p))
    )

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
