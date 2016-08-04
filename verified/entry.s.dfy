include "kev_common.s.dfy"
include "ARMdef.dfy"
include "pagedb.s.dfy"
include "smcapi.s.dfy"
include "pagedb.i.dfy"

predicate entryState(s:state, d:PageDb)
{
    reveal_validPageDb();
    ValidState(s) && SaneMem(s.m) && validPageDb(d) &&
    (validPageDbImpliesClosedRefs(d); pageDbCorresponds(s.m, d)) &&
    validL1PTPage(d, s.conf.l1p) && !stoppedAddrspace(d, s.conf.l1p) &&
    s.conf.m == User && s.conf.ns == Secure
}

predicate validEntryTransition(s:state,s':state,d:PageDb,d':PageDb,
    dispPage:PageNr,a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) 
    requires ValidState(s) && SaneMem(s.m) && validPageDb(d)
    requires (validPageDbImpliesClosedRefs(d); pageDbCorresponds(s.m, d))
    requires smc_enter(d, dispPage, a1, a2, a3).1 == KEV_ERR_SUCCESS()
{
    //reveal_validConfig();
    reveal_validPageDb();
    reveal_ValidConfig();
	var addrspace := d[d[dispPage].addrspace].entry;
    s'.conf.m  == User && s'.conf.ns == Secure && s'.conf.l1p == addrspace.l1ptnr &&
    OSymbol("g_cur_dispatcher") in s'.m.globals &&
    s'.m.globals[OSymbol("g_cur_dispatcher")] == [dispPage] &&
    entryState(s', d') &&
    d' == d && pageDbCorresponds(s'.m, d')
}

predicate validReturnTransition(s:state,s':state,d:PageDb,d':PageDb, isResume:bool)
{
    // The following specifies that this is the return path after execution
        // q is the state immediately upon entry.
        // r is the state just before calling the exception handler.
    (exists q, r :: entryState(q, d) && userspaceExecution(q, r, d) &&
        exception(r, s, d, d', isResume)) &&

    // leave secure world
    s'.conf.ns == NotSecure &&

    entryState(s', d')
}

predicate svc(s:state,s':state,d:PageDb,d':PageDb, isResume:bool) 
{
    // TODO disable interrupts (cpsid is called in impl)
    entryState(s, d) && entryState(s', d') && s'.conf.m == Monitor &&
    s'.regs[R0] == KEV_ERR_SUCCESS() &&

    // Set entered to false if this is a resume
    (var dispPage := s.m.globals[OSymbol("g_cur_dispatcher")][0];
    var a := d[ dispPage ].addrspace;
    validDispatcherPage(d', dispPage) &&
    d'[dispPage].addrspace == d[dispPage].addrspace &&
    d'[dispPage].entry.entered == !isResume)
}

predicate irqfiq(s:state,s':state,d:PageDb,d':PageDb, isResume:bool)
{
    
    entryState(s, d) && entryState(s', d') && s'.conf.m == Monitor &&
    s'.regs[R0] == KEV_ERR_INTERRUPTED() &&
    
    // Set entered to true and save context if this is not a resume 
    (var dispPage := s.m.globals[OSymbol("g_cur_dispatcher")][0];
    var a := d[ dispPage ].addrspace;
    var disp := d[dispPage].entry;
    validDispatcherPage(d', dispPage) &&
    d'[dispPage].addrspace == d[dispPage].addrspace &&
    d'[dispPage].entry.entered == !isResume &&
    d'[dispPage].entry.ctxt == s.regs) &&

    // Interrupts can be taken from other modes, but the interrupt should
    // only re-enter monitor mode when taken from user mode.
    // This spec is intended to be used with an irq/fiq handler that
    // calls separate procedures for the from-user and not-from-user case.
    // Only the from-user case satisfies this predicate.
    s.conf.spsr[s.conf.m] == User
    
}

predicate abort(s:state,s':state,d:PageDb,d':PageDb, isResume:bool)
{
    // TODO disable interrupts (cpsid is called in impl)
    entryState(s, d) && entryState(s', d') && s'.conf.m == Monitor &&
    s'.regs[R0] == KEV_ERR_FAULT() &&

    // Set entered to true if this is not a resume 
    (var dispPage := s.m.globals[OSymbol("g_cur_dispatcher")][0];
    var a := d[ dispPage ].addrspace;
    var disp := d[dispPage].entry;
    validDispatcherPage(d', dispPage) &&
    d'[dispPage].addrspace == d[dispPage].addrspace &&
    d'[dispPage].entry.entered == !isResume)
}

//-----------------------------------------------------------------------------
// Userspace Execution
//-----------------------------------------------------------------------------

//The code executing in userspace is possibly malicious. This models its limitations.
predicate userspaceExecution(s:state, s':state, d:PageDb)
{
    entryState(s, d) && WSMemInvariantExceptAddrspace(s, s', d) &&
    entryState(s', d)
}

predicate exception(s:state, s':state, d:PageDb, d':PageDb, isResume:bool)
{
    svc(s,s',d,d',isResume) || irqfiq(s,s',d,d',isResume) || abort(s,s',d,d',isResume)
}

// All writeable and secure memory addresses except the ones in the active l1
// page table have their contents preserved
predicate WSMemInvariantExceptAddrspace(s:state, s':state, d:PageDb)
    requires entryState(s, d)
{
    ValidState(s') && AlwaysInvariant(s, s') &&
    s.m.globals == s'.m.globals &&
    forall i :: i in s.m.addresses && address_is_secure(i) &&
        !memSWrInAddrspace(d, s.conf.l1p, i) ==>
            s.m.addresses[i] == s'.m.addresses[i]
}

// Is the page secure, writeable, and in the L1PT
predicate pageSWrInAddrspace(d:PageDb, l1p:PageNr, p:PageNr)
	requires validPageNr(p) && validL1PTPage(d, l1p)
    requires (validPageDbImpliesWellFormed(d); !stoppedAddrspace(d, l1p))
{
    reveal_validPageDb();
    !stoppedAddrspace(d, l1p) && 
    var l1pt := d[l1p].entry.l1pt;
    l1p == p || Just(p) in l1pt ||
    exists p' :: Just(p') in l1pt && pageSWrInL2PT(d[p'].entry.l2pt,p)
}

predicate memSWrInAddrspace(d:PageDb, l1p:PageNr, m: mem)
    requires validL1PTPage(d, l1p)
    requires (validPageDbImpliesWellFormed(d); !stoppedAddrspace(d, l1p))
{
    exists p :: validPageNr(p) && pageSWrInAddrspace(d, l1p, p) && addrInPage(m, p)
}

// is the page secure, writeable, and in the L2PT
predicate pageSWrInL2PT(l2pt:seq<L2PTE>, p:PageNr)
{
    exists l2pte :: l2pte in l2pt && (match l2pte
        case NoMapping => false
        case SecureMapping(p', w, e) => w && p' == p
        case InsecureMapping(p') => false)
}


// Copied from old entry.s.dfy
// //-----------------------------------------------------------------------------
// // Safety poperties of the monitor/addrspace boundary
// //-----------------------------------------------------------------------------
// 
// predicate addrspaceOwnershipOfPagesPreserved(d:PageDb, d':PageDb)
//     // requires entryState(s, d) && entryState(s', d')
//     requires validPageDb(d) && validPageDb(d')
// {
//     reveal_validPageDb();
//     forall a :: validAddrspacePage(d, a) ==>
//         validAddrspacePage(d', a) && 
//         (var l1 := d[a].entry.l1ptnr;
//         forall m :: !stoppedAddrspace(d,a) && memSWrInAddrspace(d, l1, m) ==> 
//             d'[a] == d[a] && !stoppedAddrspace(d', a) && memSWrInAddrspace(d', l1, m))
// }
// 
// // The pages owned by other addrspaces are preserved
// predicate addrspaceContentsPreservedExcept(s:state, s':state, d: PageDb, d':PageDb, disp:PageNr)
//     requires entryState(s, d) && entryState(s', d')
//     requires addrspaceOwnershipOfPagesPreserved(d, d')
//     requires valid
// {
//     reveal_validPageDb();
//     var a := d[disp].addrspace;
//     ValidState(s') && AlwaysInvariant(s, s') &&
//     forall a' :: validAddrspacePage(d, a') && a' != a && !stoppedAddrspace(d, a') ==>
//         (var l1' := d[a'].entry.l1ptnr;
//         forall m :: memSWrInAddrspace(d, l1', m) ==>
//             s.m.addresses[m] == s'.m.addresses[m])
// }
