include "kev_common.s.dfy"
include "ARMdef.dfy"
include "pagedb.s.dfy"
include "smcapi.s.dfy"
include "pagedb.i.dfy"
include "abstate.s.dfy"

predicate userEnteredState(s:SysState)
{
    reveal_validPageDb();
    validSysState(s) &&
    validL1PTPage(s.d, s.hw.conf.ttbr0) && !hasStoppedAddrspace(s.d, s.hw.conf.ttbr0) &&
    s.hw.conf.cpsr.m == User && s.hw.conf.scr.ns == Secure
}

predicate validEntryTransitionEnter(s:SysState,s':SysState,
    dispPage:PageNr,a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage, a1, a2, a3).1 == KEV_ERR_SUCCESS()
    // ensures validEntryTransitionEnter(s,s',dispPage,a1,a2,a3) ==> false
{
    reveal_validPageDb();
    reveal_ValidConfig();
	var addrspace := s.d[s.d[dispPage].addrspace].entry;
    
    userEnteredState(s') && s'.d == s.d &&
    s'.hw.conf.cpsr.m  == User && s'.hw.conf.scr.ns == Secure 
        && s'.hw.conf.ttbr0 == addrspace.l1ptnr &&
    
    (reveal_ValidRegState();
    s'.hw.regs[R0] == a1 && s'.hw.regs[R1] == a2 && s'.hw.regs[R2] == a3) &&

    s'.g.g_cur_dispatcher == dispPage &&

    s'.hw.conf.cpsr.m == User &&

    sp_eval(Ins(MOVS_PCLR), s.hw, s'.hw, true) &&
    OperandContents(s.hw, OLR) == s.d[dispPage].entry.entrypoint
}


predicate validEntryTransitionResume(s:SysState, s':SysState, dispPage:PageNr)
    requires validSysState(s)
    requires smc_resume(s.d, dispPage).1 == KEV_ERR_SUCCESS()
    // ensures validEntryTransitionResume(s,s',dispPage) ==> false
{
    //reveal_validConfig();
    reveal_validPageDb();
    reveal_ValidConfig();
	var addrspace := s.d[s.d[dispPage].addrspace].entry;
    var disp := s.d[dispPage].entry;
    
    userEnteredState(s') && s'.d == s.d &&
    s'.hw.conf.cpsr.m  == User && s'.hw.conf.scr.ns == Secure &&
        s'.hw.conf.ttbr0 == addrspace.l1ptnr &&

    s'.g.g_cur_dispatcher == dispPage &&
   
    (reveal_ValidRegState(); 
    s'.hw.regs == disp.ctxt.regs
        [LR(FIQ)        := s.hw.regs[LR(FIQ)]]
        [LR(IRQ)        := s.hw.regs[LR(IRQ)]]
        [LR(Supervisor) := s.hw.regs[LR(Supervisor)]]
        [LR(Abort)      := s.hw.regs[LR(Abort)]]
        [LR(Undefined)  := s.hw.regs[LR(Undefined)]]
        [LR(Monitor)    := s.hw.regs[LR(Monitor)]]
        [SP(FIQ)        := s.hw.regs[SP(FIQ)]]
        [SP(IRQ)        := s.hw.regs[SP(IRQ)]]
        [SP(Supervisor) := s.hw.regs[SP(Supervisor)]]
        [SP(Abort)      := s.hw.regs[SP(Abort)]]
        [SP(Undefined)  := s.hw.regs[SP(Undefined)]]
        [SP(Monitor)    := s.hw.regs[SP(Monitor)]]) &&
    
    (reveal_ValidSRegState();
    s'.hw.sregs[cpsr] == disp.ctxt.cpsr &&
    s'.hw.conf.cpsr == decode_psr(disp.ctxt.cpsr)) &&
    
    sp_eval(Ins(MOVS_PCLR), s.hw, s'.hw, true) &&
    OperandContents(s.hw, OLR) == disp.ctxt.pc
}

predicate eqDisp(s:SysState, s':SysState) { s.g.g_cur_dispatcher == s'.g.g_cur_dispatcher }

predicate {:opaque} validEnter(s:SysState,s':SysState,
    dispPage:PageNr,a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    // ensures validEnter(s,s',dispPage,a1,a2,a3) ==> false
{
    smc_enter(s.d, dispPage, a1, a2, a3).1 != KEV_ERR_SUCCESS() ||
    (exists r :: validEntryTransitionEnter(s,r,dispPage,a1,a2,a3) && exception(r, s'))
}

predicate {:opaque} validResume(s:SysState,s':SysState,dispPage:PageNr)
    requires validSysState(s)
{
    smc_resume(s.d, dispPage).1 != KEV_ERR_SUCCESS() ||
    (exists q, r :: validEntryTransitionResume(s,q,dispPage) && userspaceExecution(q, r) &&
        exception(r, s'))
}

predicate svc(s:SysState,s':SysState) 
    // ensures svc(s,s') ==> false
{
    reveal_ValidRegState();
    // TODO disable interrupts (cpsid is called in impl)
    userEnteredState(s) && userEnteredState(s') &&
    s'.hw.regs[R0] == KEV_ERR_SUCCESS()  &&

    // Set entered to false if this is a resume

    (var dispPage := s.g.g_cur_dispatcher;
    validDispatcherPage(s'.d, dispPage) &&
    s'.d[dispPage].addrspace == s.d[dispPage].addrspace &&
    s'.d[dispPage].entry.entered == false)
}

predicate irqfiq(s:SysState,s':SysState)
    // ensures irqfiq(s,s') ==> false
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
    userEnteredState(s) && userEnteredState(s') && 
    s'.hw.regs[R0] == KEV_ERR_INTERRUPTED() &&
    
    // Set entered to true and save context if this is not a resume 
    // TOOD dont talk about this global
    (var dispPage := s.g.g_cur_dispatcher;

    validDispatcherPage(s'.d, dispPage) &&
    s'.d[dispPage].addrspace == s.d[dispPage].addrspace &&
    s'.d[dispPage].entry.entered == true &&
    s'.d[dispPage].entry.ctxt.regs == s.hw.regs &&
    s'.d[dispPage].entry.ctxt.pc == OperandContents(s.hw, OLR) &&
    s'.d[dispPage].entry.ctxt.cpsr == s.hw.sregs[cpsr])

    // Interrupts can be taken from other modes, but the interrupt should
    // only re-enter monitor mode when taken from user mode.
    // This spec is intended to be used with an irq/fiq handler that
    // calls separate procedures for the from-user and not-from-user case.
    // Only the from-user case satisfies this predicate because s is required
    // to be in user mode by userEnteredState(s)
}

predicate abort(s:SysState,s':SysState)
    // ensures abort(s,s') ==> false
{
    reveal_ValidRegState();
    userEnteredState(s) && userEnteredState(s') &&
    s'.hw.regs[R0] == KEV_ERR_FAULT() &&

    // Set entered to true if this is not a resume 
    (var dispPage := s.g.g_cur_dispatcher;
    validDispatcherPage(s'.d, dispPage) &&
    s'.d[dispPage].addrspace == s.d[dispPage].addrspace &&
    s'.d[dispPage].entry.entered == true)
}

//-----------------------------------------------------------------------------
// Userspace Execution
//-----------------------------------------------------------------------------

//The code executing in userspace is possibly malicious. This models its limitations.
predicate userspaceExecution(s:SysState, s':SysState)
{
    userEnteredState(s) && WSMemInvariantExceptAddrspace(s, s') &&
    userEnteredState(s') && s'.d == s.d
}

function {:axiom} userspaceExecutionF(s:SysState) : SysState
    //requires userEnteredState(s)
    ensures userspaceExecution(s,userspaceExecutionF(s))

predicate exception(s:SysState, s':SysState)
{
    userspaceExecution(s, s') &&
    (svc(s,s') || irqfiq(s,s') || abort(s,s'))
}

function {:axiom} exceptionF(s:SysState) : SysState
    ensures exception(s,exceptionF(s))

// lemma exceptionBorked(s:SysState,s':SysState)
//     ensures exception(s,s') ==> false;
//     {
//     }

// All writeable and secure memory addresses except the ones in the active l1
// page table have their contents preserved
predicate WSMemInvariantExceptAddrspace(s:SysState, s':SysState)
    requires userEnteredState(s)
{
    ValidState(s'.hw) && AlwaysInvariant(s.hw, s'.hw) &&
    s.hw.m.globals == s'.hw.m.globals &&
    forall i :: i in s.hw.m.addresses && address_is_secure(i) &&
        !memSWrInAddrspace(s.d, s.hw.conf.ttbr0, i) ==>
            s.hw.m.addresses[i] == s'.hw.m.addresses[i]
}

// Is the page secure, writeable, and in the L1PT
predicate pageSWrInAddrspace(d:PageDb, l1p:PageNr, p:PageNr)
	requires validPageNr(p) && validL1PTPage(d, l1p)
    requires (validPageDbImpliesWellFormed(d); !hasStoppedAddrspace(d, l1p))
{
    reveal_validPageDb();
    !hasStoppedAddrspace(d, l1p) && 
    var l1pt := d[l1p].entry.l1pt;
    l1p == p || Just(p) in l1pt ||
    exists p' :: Just(p') in l1pt && pageSWrInL2PT(d[p'].entry.l2pt,p)
}

predicate memSWrInAddrspace(d:PageDb, l1p:PageNr, m: mem)
    requires validL1PTPage(d, l1p)
    requires (validPageDbImpliesWellFormed(d); !hasStoppedAddrspace(d, l1p))
{
    exists p :: validPageNr(p) && pageSWrInAddrspace(d, l1p, p) && addrInPage(m, p)
}

// is the page secure, writeable, and in the L2PT
predicate pageSWrInL2PT(l2pt:seq<L2PTE>, p:PageNr)
{
    exists l2pte :: l2pte in l2pt && (match l2pte
        case NoMapping => false
        case SecureMapping(p', w, e) => w && p' == p
        case InsecureMapping(p',w) => false)
}


// Copied from old entry.s.dfy
// //-----------------------------------------------------------------------------
// // Safety poperties of the monitor/addrspace boundary
// //-----------------------------------------------------------------------------
// 
// predicate addrspaceOwnershipOfPagesPreserved(d:PageDb, d':PageDb)
//     // requires userEnteredState(s, d) && userEnteredState(s', d')
//     requires validPageDb(d) && validPageDb(d')
// {
//     reveal_validPageDb();
//     forall a :: validAddrspacePage(d, a) ==>
//         validAddrspacePage(d', a) && 
//         (var l1 := d[a].entry.l1ptnr;
//         forall m :: !hasStoppedAddrspace(d,a) && memSWrInAddrspace(d, l1, m) ==> 
//             d'[a] == d[a] && !hasStoppedAddrspace(d', a) && memSWrInAddrspace(d', l1, m))
// }
// 
// // The pages owned by other addrspaces are preserved
// predicate addrspaceContentsPreservedExcept(s:state, s':state, d: PageDb, d':PageDb, disp:PageNr)
//     requires userEnteredState(s, d) && userEnteredState(s', d')
//     requires addrspaceOwnershipOfPagesPreserved(d, d')
//     requires valid
// {
//     reveal_validPageDb();
//     var a := d[disp].addrspace;
//     ValidState(s') && AlwaysInvariant(s, s') &&
//     forall a' :: validAddrspacePage(d, a') && a' != a && 
//       !hasStoppedAddrspace(d, a') ==>
//         (var l1' := d[a'].entry.l1ptnr;
//         forall m :: memSWrInAddrspace(d, l1', m) ==>
//             s.m.addresses[m] == s'.m.addresses[m])
// }
