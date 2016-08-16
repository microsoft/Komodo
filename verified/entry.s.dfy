include "kev_common.s.dfy"
include "ARMdef.dfy"
include "pagedb.s.dfy"
include "smcapi.s.dfy"
include "pagedb.i.dfy"
include "abstate.s.dfy"

predicate nonStoppedL1(d:PageDb, l1:PageNr)
{
    validL1PTPage(d, l1) && (validPageDbImpliesWellFormed(d);
        !hasStoppedAddrspace(d, l1))
}

predicate nonStoppedDispatcher(d:PageDb, p:PageNr)
{
    validDispatcherPage(d,p) && (validPageDbImpliesWellFormed(d);
        !hasStoppedAddrspace(d,p))
}

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
    validERTransitionHW(s.hw, s'.hw, s.d) && sd == sd'
    && equivalentExceptPage(s.d, s'.d, sd) 
    && nonStoppedDispatcher(s.d, sd) && nonStoppedDispatcher(s'.d, sd')
    && l1pOfDispatcher(s.d, sd)  == s.hw.conf.ttbr0
    && l1pOfDispatcher(s'.d, sd') == s'.hw.conf.ttbr0
    && WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d,
        l1pOfDispatcher(s.d, sd)))

}

predicate validERTransitionHW(hw:state, hw':state, d:PageDb)
{
    reveal_validPageDb();
    reveal_ValidConfig();
    ValidState(hw) && ValidState(hw')
    && hw'.conf.ttbr0 == hw.conf.ttbr0 
    && nonStoppedL1(d, hw.conf.ttbr0)
    // && bankedRegsPreserved(hw, hw') Should be part of top-level spec
}

predicate validSysStates(sset:set<SysState>) { forall s :: s in sset ==> validSysState(s) }

predicate validEnter(s:SysState,s':SysState,
    dispPage:PageNr,a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage, a1, a2, a3).1 == KEV_ERR_SUCCESS()
{
    reveal_ValidRegState();
    // smc_enter(s.d, dispPage, a1, a2, a3).1 != KEV_ERR_SUCCESS() ||
    
    // s1 (s)  : State on entry to the monitor
    // s2      : prior to MOVSPCLR that transitions to userspace
    // s3      : post MOVS State just before start of userspace execution
    // s4      : Exceptional state where handler must be called
    // s5      : State at start of exception handler
    // s6      : State at start of transition back to smc_handler
    // s7      : State on re-entry to smc_handler
    // s8 (s') : State at the end of the monitor call/
    
    // s4 == s5 except not in exceptional state in s4
    // s6 == s7 except branch has happened
    
    (exists s2, s3, s4, s5 :: validSysStates({s2,s3,s4,s5})
        && preEntryEnter(s,s2,dispPage,a1,a2,a3)
        && entryTransitionEnter(s2, s3)
        && s4.d == s3.d && userspaceExecution(s3.hw, s4.hw, s3.d)
        && validERTransition(s4, s5) &&
            !s5.hw.conf.ex.none? && mode_of_state(s5.hw) != User
        && validERTransition(s5, s')
        && (s'.hw.regs[R0], s'.hw.regs[R1], s'.d) ==
            exceptionHandled(s5))
}

/*
predicate validResume(s:SysState,s':SysState,dispPage:PageNr)
    requires validSysState(s)
{
     
    smc_resume(s.d, dispPage).1 != KEV_ERR_SUCCESS() ||
        ... state transitions
}
*/

predicate preEntryEnter(s:SysState,s':SysState,
    dispPage:PageNr,a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage, a1, a2, a3).1 == KEV_ERR_SUCCESS()
    ensures  nonStoppedL1(s.d, l1pOfDispatcher(s.d, dispPage));
    // ensures (validSysState(s) && validSysState(s') && 
    // preEntryEnter(s,s',dispPage,a1,a2,a3)) ==>false
{
    reveal_validPageDb();
    reveal_ValidConfig();
    reveal_ValidRegState();
	//var addrspace := s.d[s.d[dispPage].addrspace].entry;
    var l1p := l1pOfDispatcher(s.d, dispPage);
    
    validSysState(s') &&  s.d == s'.d &&
    s'.hw.conf.ttbr0 == l1p &&
    s'.hw.conf.cpsr.m  == User && s'.hw.conf.scr.ns == Secure &&
    
    s'.hw.regs[R0] == a1 && s'.hw.regs[R1] == a2 && s'.hw.regs[R2] == a3 &&

    s'.g.g_cur_dispatcher == dispPage &&

    // bankedRegsPreserved(s.hw, s'.hw) &&
    WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d, l1p) // TODO delete in future

}

/*
predicate preEntryResume(s:SysState, s':SysState, dispPage:PageNr)
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
    
    bankedRegsPreserved(s, s') &&
    WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, d, l1pOfDispatcher(s.d, dispPage))

}
*/

predicate entryTransitionEnter(s:SysState,s':SysState)
    // ensures (validSysState(s) && validSysState(s') && entryTransitionEnter(s,s')) ==>false
{
    validERTransition(s, s') && s'.d == s.d &&
    sp_eval(Ins(MOVS_PCLR), s.hw, s'.hw) &&
    OperandContents(s.hw, OLR) == s.d[s.g.g_cur_dispatcher].entry.entrypoint
}

predicate entryTransitionResume(s:SysState,s':SysState)
    // ensures (validSysState(s) && validSysState(s') && entryTransitionResume(s,s')) ==>false
{
    validSysState(s) && validSysState(s') && s.d == s'.d &&    
    (var disp := s.d[s.g.g_cur_dispatcher].entry;
    sp_eval(Ins(MOVS_PCLR), s.hw, s'.hw) &&
    OperandContents(s.hw, OLR) == disp.ctxt.pc)
}

predicate userspaceExecution(hw:state, hw':state, d:PageDb)
    /*ensures (exists s, s' :: validSysState(s) && validSysState(s') &&
        s.d == s'.d && userspaceExecution(s.hw, s'.hw, d)) ==> false */
{
    validERTransitionHW(hw, hw', d)
    && hw.conf.cpsr.m == User && hw'.conf.cpsr.m == User
    && WSMemInvariantExceptAddrspace(hw, hw', d)
    && !hw'.conf.ex.none?
    // TODO: ensure we didn't take any intermediate exceptions, by using a counter
}

//-----------------------------------------------------------------------------
// Exception Handler Spec
//-----------------------------------------------------------------------------
function exceptionHandled(s:SysState) : (int, int, PageDb)
    requires validSysState(s)
    requires mode_of_state(s.hw) != User
    requires !s.hw.conf.ex.none?
{
    reveal_validPageDb();
    reveal_ValidSRegState();
    reveal_ValidRegState();
    reveal_ValidConfig();
    if(s.hw.conf.ex.svc?) then
        var p := s.g.g_cur_dispatcher;
        var d' := s.d[ p := s.d[p].(entry := s.d[p].entry.(entered := false))];
        (KEV_ERR_SUCCESS(), s.hw.regs[R0], d')
    else 
        var p := s.g.g_cur_dispatcher;
        var pc := OperandContents(s.hw, OLR);
        var psr := s.hw.sregs[spsr(mode_of_state(s.hw))];
        var disp' := s.d[p].entry.(entered:=true,
            ctxt:= DispatcherContext(s.hw.regs, psr, pc));
        var d' := s.d[ p := s.d[p].(entry := disp') ];
        if(s.hw.conf.ex.irq? || s.hw.conf.ex.fiq?) then
            (KEV_ERR_INTERRUPTED(), 0, d')
        else
            assert s.hw.conf.ex.abt?;
            (KEV_ERR_FAULT(), 0, d')

    // TODO add undef exception
}

//-----------------------------------------------------------------------------
// Userspace Execution
//-----------------------------------------------------------------------------


predicate bankedRegsPreserved(hw:state, hw':state)
    requires ValidState(hw) && ValidState(hw')
{
        reveal_ValidRegState();
        reveal_ValidConfig();
        forall m :: m != User ==>
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
    requires ValidState(hw) && ValidState(hw') && nonStoppedL1(d, l1p)
{
    (forall m:mem :: m in hw.m.addresses <==> m in hw'.m.addresses) &&
    hw.m.globals == hw'.m.globals &&
    (forall i | i in hw.m.addresses && address_is_secure(i) && 
        !memSWrInAddrspace(d, l1p, i) ::  
            hw.m.addresses[i] == hw'.m.addresses[i])
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
    exists p | validPageNr(p) :: pageSWrInAddrspace(d, l1p, p) && addrInPage(m, p)
}

// is the page secure, writeable, and in the L2PT
predicate pageSWrInL2PT(l2pt:seq<L2PTE>, p:PageNr)
{
    exists l2pte :: l2pte in l2pt && (match l2pte
        case NoMapping => false
        case SecureMapping(p', w, e) => w && p' == p
        case InsecureMapping(p',w) => false)
}

predicate equivalentExceptPage(d:PageDb, d':PageDb, p:PageNr)
    requires validPageNr(p)
    requires validPageDb(d) && validPageDb(d')
{
    validPageDbImpliesWellFormed(d);
    validPageDbImpliesWellFormed(d');
    forall p' :: validPageNr(p') && p' != p ==> d[p'] == d'[p']
}
