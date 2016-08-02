include "kev_common.s.dfy"
include "ARMdef.dfy"
include "pagedb.s.dfy"
include "pagedb.i.dfy"
include "smcapi.s.dfy"
include "smcfunctional.i.dfy"

predicate entryState(s:state, d:PageDb)
{
    reveal_validPageDb();
    ValidState(s) && SaneMem(s.m) && validPageDb(d) &&
    (validPageDbImpliesClosedRefs(d); pageDbCorresponds(s.m, d)) &&
    validL1PTPage(d, s.conf.l1p) && !stoppedAddrspace(d, s.conf.l1p)
}

// All memory addresses except the ones in the active l1 page table
// have their contents preserved
predicate MemInvariantExceptAddrspace(s:state, s':state, d:PageDb)
    requires entryState(s, d)
{
    ValidState(s') && AlwaysInvariant(s, s') &&
    forall i :: i in s.m.addresses && !memInAddrspace(d, s.conf.l1p, i) ==>
        s.m.addresses[i] == s'.m.addresses[i]
}

predicate pageInAddrspace(d:PageDb, l1p:PageNr, p:PageNr)
	requires validPageNr(p) && validL1PTPage(d, l1p)
    requires (validPageDbImpliesWellFormed(d); !stoppedAddrspace(d, l1p))
{
    reveal_validPageDb();
    !stoppedAddrspace(d, l1p) && 
    var l1pt := d[l1p].entry.l1pt;
    l1p == p || Just(p) in l1pt ||
    exists p' :: Just(p') in l1pt && pageInL2PT(d[p'].entry.l2pt,p)
}

predicate memInAddrspace(d:PageDb, l1p:PageNr, m: mem)
    requires validL1PTPage(d, l1p)
    requires (validPageDbImpliesWellFormed(d); !stoppedAddrspace(d, l1p))
{
    exists p :: validPageNr(p) && pageInAddrspace(d, l1p, p) && addrInPage(m, p)
}

predicate pageInL2PT(l2pt:seq<L2PTE>, p:PageNr)
{
    exists l2pte :: l2pte in l2pt && (match l2pte
        case NoMapping => false
        case SecureMapping(p', w, e) => w && p' == p
        case InsecureMapping(p') => p' == p)
}

//-----------------------------------------------------------------------------
// Assumptions about user mode execution of the addrspace
//-----------------------------------------------------------------------------
function {:axiom} addrspaceHavoc(s:state, d:PageDb) : state
    requires entryState(s, d)
    ensures var s' := addrspaceHavoc(s, d);
        MemInvariantExceptAddrspace(s, s', d) && SaneMem(s'.m) &&
        s'.conf == s.conf

function {:axiom} addrspaceReturn(s:state, d:PageDb) : state
    requires entryState(s, d)
    ensures 
        addrspaceReturn(s, d) == svc(s)   ||
        addrspaceReturn(s, d) == irq(s)   ||
        addrspaceReturn(s, d) == fiq(s)   ||
        addrspaceReturn(s, d) == abort(s)


//-----------------------------------------------------------------------------
// Addrspace entry / return path
//-----------------------------------------------------------------------------

function entry(s:state, disp: PageNr, a1: int, a2: int, a3: int, d:PageDb) : state
    requires entryState(s, d)
    // TODO requires pageDbCorresponds
{
    var s1 := enterDispatchFunctional(s, disp, a1, a2, a3, d);
    assume false; // TODO need premium enterDispatchFunctional
    var s2 := addrspaceHavoc(s1, d);
    var s3 := addrspaceReturn(s2, d);
    s3
}

//-----------------------------------------------------------------------------
// Safety poperties of the monitor/addrspace boundary
//-----------------------------------------------------------------------------

// The pages owned by other addrspaces are preserved
predicate {:opaque} addrspaceContentsPreservedExcept(s:state, s':state, disp:PageNr, d: PageDb)
    requires entryState(s, d)
    requires validDispatcherPage(d, disp)
{
    reveal_validPageDb();
    var a := d[disp].addrspace;
    ValidState(s') && AlwaysInvariant(s, s') &&
    forall a' :: validAddrspacePage(d, a') && a' != a && !stoppedAddrspace(d, a') ==>
        (var l1' := d[a'].entry.l1ptnr;
        forall m :: memInAddrspace(d, l1', m) ==>
            s.m.addresses[m] == s'.m.addresses[m])
}

// // Probaby needed to prove next lemma
// lemma addrspaceHavocPreservesPageDb(s:state, d:PageDb)
//     requires entryState(s, d)
//     ensures var s' := addrspaceHavoc(s, d);
//         (validPageDbImpliesClosedRefs(d); pageDbCorresponds(s'.m, d))
// {
//     //TODO PROVEME
// 	assume false;
// }
// 
// lemma addrspaceExecutePreservesPageDb(s:state, d:PageDb)
//     requires entryState(s, d)
//     ensures var s' := addrspaceExecute(s, d, a);
//         (validPageDbImpliesClosedRefs(d); pageDbCorresponds(s'.m, d))
// {
//     //TODO PROVEME
// 	assume false;
// }


lemma entryPreservesOtherAddrspaces(s:state, disp:PageNr, a1:int, a2:int, a3:int, d:PageDb)
    requires entryState(s, d)
    ensures  validDispatcherPage(d, disp)
    ensures  var s' := entry(s, disp, a1, a2, a3, d);
        addrspaceContentsPreservedExcept(s, s', disp, d)
{
    //TODO prove 
    assume false;
}


//-----------------------------------------------------------------------------
// Liveness Properties of the monitor/addrspace bondary
//-----------------------------------------------------------------------------

// args of smc_enter reach r0-r3 ?

// The sequence enter -> execute -> return -> enter -> execute restores the
    // context from the first execute?

