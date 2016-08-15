include "kev_common.s.dfy"
include "ARMdef.dfy"
include "pagedb.s.dfy"
include "smcapi.s.dfy"
include "pagedb.i.dfy"
include "abstate.s.dfy"

function l1pOfDispatcher(d:PageDb, p:PageNr) : PageNr
    requires validDispatcherPage(d, p) && !hasStoppedAddrspace(d, p)
    ensures  validL1PTPage(d, l1pOfDispatcher(d, p))
{
    reveal_validPageDb();
    d[d[p].addrspace].entry.l1ptnr
}

// This must hold between all consecutive states on the addsrpace entry/return path.
predicate validERTransition(s:SysState, s':SysState)
{
    reveal_validPageDb();
    validSysState(s) && validSysState(s') &&
    (var sd := s.g.g_cur_dispatcher;
    var sd' := s'.g.g_cur_dispatcher;
    validERTransitionHW(s.hw, s'.hw, s.d) &&
    s.g.g_cur_dispatcher == s'.g.g_cur_dispatcher &&
    validDispatcherPage(s.d, sd) && !hasStoppedAddrspace(s.d, sd) &&
    validL1PTPage(s.d, l1pOfDispatcher(s.d, sd)) && 
    validDispatcherPage(s'.d, sd') && !hasStoppedAddrspace(s'.d, sd) &&
    validL1PTPage(s'.d, l1pOfDispatcher(s'.d, sd')) &&
    l1pOfDispatcher(s.d, s.g.g_cur_dispatcher)  == s.hw.conf.ttbr0 &&
    l1pOfDispatcher(s'.d, s'.g.g_cur_dispatcher) == s'.hw.conf.ttbr0)

}

predicate validERTransitionHW(hw:state, hw':state, d:PageDb)
{
    reveal_validPageDb();
    reveal_ValidConfig();
    ValidState(hw) && ValidState(hw')
    && hw'.conf.ttbr0 == hw.conf.ttbr0 
    && validL1PTPage(d, hw.conf.ttbr0)
    && validL1PTPage(d, hw'.conf.ttbr0)
    && !hasStoppedAddrspace(d, hw.conf.ttbr0)
    && !hasStoppedAddrspace(d, hw'.conf.ttbr0)
}

predicate validEntryTransitionEnter(s:SysState,s':SysState,
    dispPage:PageNr,a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage, a1, a2, a3).1 == KEV_ERR_SUCCESS()
{
    reveal_validPageDb();
    reveal_ValidConfig();
    reveal_ValidRegState();
	//var addrspace := s.d[s.d[dispPage].addrspace].entry;
    var l1p := l1pOfDispatcher(s.d, dispPage);
    
    validSysState(s') && s'.d == s.d &&
    s'.hw.conf.ttbr0 == l1p &&
    s'.hw.conf.cpsr.m  == User && s'.hw.conf.scr.ns == Secure &&
    
    s'.hw.regs[R0] == a1 && s'.hw.regs[R1] == a2 && s'.hw.regs[R2] == a3 &&

    s'.g.g_cur_dispatcher == dispPage &&

    bankedRegsPreservedForMonitor(s.hw, s'.hw) &&
    WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d, l1p) &&

    // ENTER_ADDRSPACE is instruction evaluated on s->s'
    // sp_eval(Ins(MOVS_PCLR), s.hw, s'.hw) &&
    OperandContents(s.hw, OLR) == s.d[dispPage].entry.entrypoint
}

/*
predicate validEntryTransitionResume(s:SysState, s':SysState, dispPage:PageNr)
    requires validSysState(s)
    requires smc_resume(s.d, dispPage).1 == KEV_ERR_SUCCESS()
{
    reveal_validPageDb();
    reveal_ValidConfig();
    var disp := s.d[dispPage].entry;
    
    validSysState(s') && // s'.d == s.d &&
    s'.hw.conf.ttbr0 == l1pOfDispatcher(s.d, dispPage) &&
    s'.hw.conf.cpsr.m  == User && s'.hw.conf.scr.ns == Secure &&

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
    
    bankedRegsPreservedForMonitor(s, s') &&
    WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, d, l1pOfDispatcher(s.d, dispPage)) &&

    sp_eval(Ins(MOVS_PCLR), s.hw, s'.hw) &&
    OperandContents(s.hw, OLR) == disp.ctxt.pc
}
*/

predicate eqDisp(s:SysState, s':SysState) { s.g.g_cur_dispatcher == s'.g.g_cur_dispatcher }

predicate validEnter(s:SysState,s':SysState,
    dispPage:PageNr,a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
{
    // s0 (s)  : State on entry to the monitor
    // s1      : prior to MOVSPCLR that transitions to userspace/a
    // s2      : post MOVS State just before start of userspace execution.
    // s3      : Exceptional where handler must be called
    // s4      : State at start of exception handler
    // s5      : State at start of transition back to smc_handler
    // s6      : State on re-entry to smc_handler
    // s7 (s') : State at the end of the monitor call/
    //
    // s3 == s4 except not in exceptional state in s4
    // s5 == s6 except branch has happened
    
    smc_enter(s.d, dispPage, a1, a2, a3).1 != KEV_ERR_SUCCESS() ||
    (exists s2, s3, s4, s5 :: validSysState(s2) && validSysState(s3)
        && validSysState(s4) && validSysState(s5)
        && validEntryTransitionEnter(s,s2,dispPage,a1,a2,a3)
        && s3.d == s2.d && userspaceExecution(s2.hw, s3.hw, s2.d)
        && s4.d == s3.d && handlerCalled(s3.hw, s4.hw)
        && exceptionHandled(s4, s5)
        && monitorReturn(s5, s'))
}

/*
predicate validResume(s:SysState,s':SysState,dispPage:PageNr)
    requires validSysState(s)
{
    // s1 (s)  : State on entry to the monitor
    // s2      : State just before start of userspace execution.
    // s3      : State between end of userspace execution and the exception handler
    // s4      : State between the exception handler and re-entry to the monitor
    // s5 (s') : State at the end of the monitor call
     
    smc_resume(s.d, dispPage).1 != KEV_ERR_SUCCESS() ||
    (exists s2, s3, s4 :: validEntryTransitionResume(s,s2,dispPage) 
        && userspaceExecution(s2, s3)
        && exceptionHandled(s3, s4)
        && monitorReturn(s4, s'))
}
*/

predicate exceptionHandled(s:SysState,s':SysState)
    ensures exceptionHandled(s, s') ==> 
        validERTransition(s, s') &&
        WSMemInvariantExceptAddrspace(s.hw, s'.hw, s.d)
{
    svc(s,s') || irqfiq(s,s') || abort(s,s')
}

predicate handlerCalled(hw:state,hw':state)
{
    !hw.conf.ex.none? &&
    ValidState(hw) &&
    hw'  == hw.(conf := hw.conf.(ex := none))
}

predicate monitorReturn(s:SysState,s':SysState)
{
    reveal_ValidRegState();
    validERTransition(s, s')
    && s'.d == s.d
    && WSMemInvariantExceptAddrspace(s.hw, s'.hw, s.d)
    && bankedRegsPreservedForMonitor(s.hw, s'.hw)
    && s'.hw.conf.scr.ns == NotSecure
}

predicate svc(s:SysState,s':SysState) 
{
    reveal_ValidRegState();
    
    validERTransition(s, s') &&
    s.hw.conf.cpsr.m == Supervisor &&
    s'.hw.conf.cpsr.m == Monitor &&
    s.hw.conf.ex.svc? &&
    
    WSMemInvariantExceptAddrspace(s.hw, s'.hw, s.d) &&
    bankedRegsPreservedForMonitor(s.hw, s'.hw) &&
    
    s'.hw.regs[R0] == KEV_ERR_SUCCESS()  &&
        
    s'.d == s.d
}

predicate irqfiq(s:SysState,s':SysState)
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
    reveal_ValidConfig();
    
    validERTransition(s, s') &&
    s.hw.conf.cpsr.m == Monitor &&
    s'.hw.conf.cpsr.m == Monitor &&
    (s.hw.conf.ex.irq? || s.hw.conf.ex.fiq?) &&

    WSMemInvariantExceptAddrspace(s.hw, s'.hw, s.d) &&
    bankedRegsPreservedForMonitor(s.hw, s'.hw) &&
    
    // Interrupts can be taken from other modes, but the interrupt should
    // only re-enter monitor mode when taken from user mode. The following 
    // condition checks that this interrupt was taken from user mode.
    s.hw.conf.spsr[Monitor].m == User &&

    s'.hw.regs[R0] == KEV_ERR_INTERRUPTED() &&
    
    (var dispPage := s.g.g_cur_dispatcher;
    validDispatcherPage(s'.d, dispPage) &&
    s'.d[dispPage].addrspace == s.d[dispPage].addrspace &&
    s'.d[dispPage].entry.entered == true &&
    s'.d[dispPage].entry.ctxt.regs == s.hw.regs &&
    s'.d[dispPage].entry.ctxt.pc == OperandContents(s.hw, OLR) &&
    s'.d[dispPage].entry.ctxt.cpsr == s.hw.sregs[cpsr] &&
    equivalentExceptPage(s.d, s'.d, dispPage))

}

predicate abort(s:SysState,s':SysState)
{
    reveal_ValidRegState();
   
    validERTransition(s, s') &&
    s.hw.conf.cpsr.m == Abort  &&
    s'.hw.conf.cpsr.m == Monitor &&
    s.hw.conf.ex.abt? &&
    
    s.d == s'.d &&
    bankedRegsPreservedForMonitor(s.hw, s'.hw) &&
    WSMemInvariantExceptAddrspace(s.hw, s'.hw, s.d) &&

    s'.hw.regs[R0] == KEV_ERR_FAULT() &&
    
    (var dispPage := s.g.g_cur_dispatcher;
    validDispatcherPage(s'.d, dispPage) &&
    s'.d[dispPage].addrspace == s.d[dispPage].addrspace &&
    s'.d[dispPage].entry.entered == true)
}

//-----------------------------------------------------------------------------
// Userspace Execution
//-----------------------------------------------------------------------------

predicate userspaceExecution(hw:state, hw':state, d:PageDb)
{
    validERTransitionHW(hw, hw', d)
    && hw.conf.cpsr.m == User && hw'.conf.cpsr.m == User
    && WSMemInvariantExceptAddrspace(hw, hw', d)
    && bankedRegsPreservedForMonitor(hw, hw')
    && !hw'.conf.ex.none?
}

predicate bankedRegsPreservedForMonitor(hw:state, hw':state)
    requires ValidState(hw) && ValidState(hw')
{
        reveal_ValidRegState();
        reveal_ValidConfig();
        var m := Monitor;
        hw.conf.spsr[m] == hw'.conf.spsr[m] &&
        hw.regs[LR(m)] == hw'.regs[LR(m)] &&
        hw.regs[SP(m)] == hw'.regs[SP(m)]
}

// All writeable and secure memory addresses except the ones in the active l1
// page table have their contents preserved
predicate WSMemInvariantExceptAddrspace(hw:state, hw':state, d:PageDb)
    // requires validERTransition(s, s')
    // requires userEnteredState(s) && userEnteredState(s')
    requires validERTransitionHW(hw, hw', d)
{
    WSMemInvariantExceptAddrspaceAtPage(hw, hw', d, hw.conf.ttbr0)
}

predicate WSMemInvariantExceptAddrspaceAtPage(hw:state, hw':state, 
        d:PageDb, l1p:PageNr)
    requires ValidState(hw) && ValidState(hw')
    requires validL1PTPage(d, l1p)
    requires (validPageDbImpliesWellFormed(d); !hasStoppedAddrspace(d, l1p))
{
    (forall m:mem :: m in hw.m.addresses <==> m in hw'.m.addresses) &&
    hw.m.globals == hw'.m.globals &&
    forall i :: i in hw.m.addresses && address_is_secure(i) &&
        !memSWrInAddrspace(d, l1p, i) ==>
            hw.m.addresses[i] == hw'.m.addresses[i]
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



// A purely abstract version of the memory invariant
predicate equivalentExceptPage(d:PageDb, d':PageDb, p:PageNr)
    requires validPageNr(p)
    requires validPageDb(d) && validPageDb(d')
{
    validPageDbImpliesWellFormed(d);
    validPageDbImpliesWellFormed(d');
    forall p' :: validPageNr(p') && p' != p ==> d[p'] == d'[p]
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
