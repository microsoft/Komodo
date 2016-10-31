include "ARMdef.dfy"
include "pagedb.s.dfy"
include "abstate.s.dfy"

predicate nonStoppedL1(d:PageDb, l1:PageNr)
{
    validL1PTPage(d, l1) && !hasStoppedAddrspace(d, l1)
}

predicate nonStoppedDispatcher(d:PageDb, p:PageNr)
{
    validDispatcherPage(d,p) && (validPageDbImpliesWellFormed(d);
        !hasStoppedAddrspace(d,p))
}

function l1pOfDispatcher(d:PageDb, p:PageNr) : PageNr
    requires validDispatcherPage(d, p) && !hasStoppedAddrspace(d, p)
    ensures  nonStoppedL1(d,l1pOfDispatcher(d,p))
{
    reveal_validPageDb();
    d[d[p].addrspace].entry.l1ptnr
}

// common success/failure checks for enter and resume
function smc_enter_err(d: PageDb, p: word, isresume: bool): word
    requires validPageDb(d)
{
    reveal_validPageDb();
    if (!(validPageNr(p) && d[p].PageDbEntryTyped? && d[p].entry.Dispatcher?)) then
        KOM_ERR_INVALID_PAGENO()
    else if (var a := d[p].addrspace; d[a].entry.state != FinalState) then
        KOM_ERR_NOT_FINAL()
    else if (!isresume && d[p].entry.entered) then
        KOM_ERR_ALREADY_ENTERED()
    else if (isresume && !d[p].entry.entered) then
        KOM_ERR_NOT_ENTERED()
    else KOM_ERR_SUCCESS()
}

// This must hold between all consecutive states on the addsrpace entry/resume path.
predicate validERTransition(s:SysState, s':SysState, dispPg:PageNr)
    requires validDispatcherPage(s.d, dispPg)
{
    reveal_validPageDb();
    validSysState(s) && validSysState(s') &&
    (validERTransitionHW(s.hw, s'.hw, s.d)
    && equivalentExceptPage(s.d, s'.d, dispPg)
    && nonStoppedDispatcher(s.d, dispPg) && nonStoppedDispatcher(s'.d, dispPg)
    && page_paddr(l1pOfDispatcher(s.d, dispPg))  == s.hw.conf.ttbr0.ptbase
    && WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d,
        l1pOfDispatcher(s.d, dispPg)))
}

function securePageFromPhysAddr(phys:int): PageNr
    requires PageAligned(phys)
    requires SecurePhysBase() <= phys < SecurePhysBase() +
        KOM_SECURE_NPAGES() * PAGESIZE() // physPageIsSecure(phys/PAGESIZE())
    ensures validPageNr(securePageFromPhysAddr(phys))
{
    (phys - SecurePhysBase()) / PAGESIZE()
}

predicate validERTransitionHW(hw:state, hw':state, d:PageDb)
{
    reveal_validPageDb();
    reveal_ValidSRegState();
    ValidState(hw) && ValidState(hw') && hw'.conf.ttbr0 == hw.conf.ttbr0
    && physPageIsSecure(hw.conf.ttbr0.ptbase / PAGESIZE())
    && nonStoppedL1(d, securePageFromPhysAddr(hw.conf.ttbr0.ptbase))
}

predicate validEnter(s:SysState,s':SysState,
    dispPg:word,a1:word,a2:word,a3:word)
    requires validSysState(s)
    requires smc_enter_err(s.d, dispPg, false) == KOM_ERR_SUCCESS()
{
    reveal_ValidRegState();
    reveal_validExceptionTransition();
    exists s2, s3, s4 | ValidState(s2) && ValidState(s3) && ValidState(s4) ::
        preEntryEnter(s.hw, s2, s.d, dispPg, a1, a2, a3)
        && entryTransitionEnter(s2, s3, s.d, dispPg)
        && userspaceExecution(s3, s4, s.d)
        && mode_of_state(s4) != User
        && validExceptionTransition(SysState(s4, s.d), s', dispPg)
        && (s'.hw.regs[R0], s'.hw.regs[R1], s'.d) ==
            exceptionHandled(s4, s.d, dispPg)
}

predicate validResume(s:SysState,s':SysState,dispPg:word)
    requires validSysState(s)
    requires smc_enter_err(s.d, dispPg, true) == KOM_ERR_SUCCESS()
{
     
    reveal_ValidRegState();
    reveal_validExceptionTransition();
    exists s2, s3, s4 | ValidState(s2) && ValidState(s3) && ValidState(s4) ::
        preEntryResume(s.hw, s2, s.d, dispPg)
        && entryTransitionResume(s2, s3, s.d, dispPg)
        && userspaceExecution(s3, s4, s.d)
        && mode_of_state(s4) != User
        && validExceptionTransition(SysState(s4, s.d), s', dispPg)
        && (s'.hw.regs[R0], s'.hw.regs[R1], s'.d)==
            exceptionHandled(s4, s.d, dispPg)
}

predicate smc_enter(s: state, pageDbIn: PageDb, s':state, pageDbOut: PageDb,
                    dispPage: word, arg1: word, arg2: word, arg3: word)
    requires ValidState(s) && validPageDb(pageDbIn) && ValidState(s')
{
    reveal_ValidRegState();
    var err := smc_enter_err(pageDbIn, dispPage, false);
    if err != KOM_ERR_SUCCESS() then
        pageDbOut == pageDbIn && s'.regs[R0] == err && s'.regs[R1] == 0
    else
        validEnter(SysState(s, pageDbIn), SysState(s', pageDbOut), dispPage,
                   arg1, arg2, arg3)
}

predicate smc_resume(s: state, pageDbIn: PageDb, s':state, pageDbOut: PageDb,
                     dispPage: word)
    requires ValidState(s) && validPageDb(pageDbIn) && ValidState(s')
{
    reveal_ValidRegState();
    var err := smc_enter_err(pageDbIn, dispPage, true);
    if err != KOM_ERR_SUCCESS() then
        pageDbOut == pageDbIn && s'.regs[R0] == err && s'.regs[R1] == 0
    else
        validResume(SysState(s, pageDbIn), SysState(s', pageDbOut), dispPage)
}

predicate preEntryEnter(s:state,s':state,d:PageDb,
    dispPage:PageNr,a1:word,a2:word,a3:word)
    requires ValidState(s)
    requires validPageDb(d)
    requires smc_enter_err(d, dispPage, false) == KOM_ERR_SUCCESS()
    ensures preEntryEnter(s,s',d,dispPage,a1,a2,a3) ==>
        PageAligned(s'.conf.ttbr0.ptbase) &&
        SecurePhysBase() <= s'.conf.ttbr0.ptbase < SecurePhysBase() +
            KOM_SECURE_NPAGES() * PAGESIZE()
    ensures preEntryEnter(s,s',d,dispPage,a1,a2,a3) ==>
        nonStoppedL1(d, securePageFromPhysAddr(s'.conf.ttbr0.ptbase));
{
    reveal_validPageDb();
    reveal_ValidRegState();
    var addrspace := d[d[dispPage].addrspace];
    assert isAddrspace(d, d[dispPage].addrspace);
    var l1p := addrspace.entry.l1ptnr; // l1pOfDispatcher(s.d, dispPage);
    assert d[l1p].addrspace == d[dispPage].addrspace;
    assert addrspace.entry.state == FinalState;
    assert !hasStoppedAddrspace(d, l1p);

    ValidState(s') &&
    s'.conf.ttbr0.ptbase == page_paddr(l1p) &&
    s'.conf.scr.ns == Secure &&
    s'.regs[R0] == a1 && s'.regs[R1] == a2 && s'.regs[R2] == a3 &&

    WSMemInvariantExceptAddrspaceAtPage(s, s', d, l1p)
}

predicate preEntryResume(s:state, s':state, d:PageDb, dispPage:PageNr)
    requires ValidState(s) && validPageDb(d)
    requires smc_enter_err(d, dispPage, true) == KOM_ERR_SUCCESS()
    ensures preEntryResume(s,s',d,dispPage) ==>
        PageAligned(s'.conf.ttbr0.ptbase) &&
        SecurePhysBase() <= s'.conf.ttbr0.ptbase < SecurePhysBase() +
            KOM_SECURE_NPAGES() * PAGESIZE()
    ensures preEntryResume(s,s',d,dispPage) ==>
        nonStoppedL1(d, securePageFromPhysAddr(s'.conf.ttbr0.ptbase));
{
    reveal_validPageDb();
    var disp := d[dispPage].entry;
    var l1p := l1pOfDispatcher(d, dispPage);
    
    ValidState(s') &&
    s'.conf.ttbr0.ptbase == page_paddr(l1p) && //l1pOfDispatcher(d, dispPage) &&
    s'.conf.scr.ns == Secure &&

    (reveal_ValidRegState(); 
    s'.regs[R0] == disp.ctxt.regs[R0] &&
    s'.regs[R1] == disp.ctxt.regs[R1] &&
    s'.regs[R2] == disp.ctxt.regs[R2] &&
    s'.regs[R3] == disp.ctxt.regs[R3] &&
    s'.regs[R4] == disp.ctxt.regs[R4] &&
    s'.regs[R5] == disp.ctxt.regs[R5] &&
    s'.regs[R6] == disp.ctxt.regs[R6] &&
    s'.regs[R7] == disp.ctxt.regs[R7] &&
    s'.regs[R8] == disp.ctxt.regs[R8] &&
    s'.regs[R9] == disp.ctxt.regs[R9] &&
    s'.regs[R10] == disp.ctxt.regs[R10] &&
    s'.regs[R11] == disp.ctxt.regs[R11] &&
    s'.regs[R12] == disp.ctxt.regs[R12] &&
    s'.regs[LR(User)] == disp.ctxt.regs[LR(User)] &&
    s'.regs[SP(User)] == disp.ctxt.regs[SP(User)]) &&
    
    (reveal_ValidSRegState();
    s'.sregs[spsr(Monitor)] == disp.ctxt.cpsr) &&
    //s'.conf.cpsr == decode_psr(disp.ctxt.cpsr)) &&
    
    WSMemInvariantExceptAddrspaceAtPage(s, s', d, l1p)
}

predicate entryTransitionEnter(s:state, s':state, d:PageDb, dispPg:PageNr)
    requires validDispatcherPage(d, dispPg)
    ensures entryTransitionEnter(s, s', d, dispPg) ==> mode_of_state(s') == User
{
    validERTransition(SysState(s,d), SysState(s',d), dispPg)
    && evalEnterUserspace(s, s')
    && s'.steps == s.steps + 1
    && OperandContents(s, OLR) == d[dispPg].entry.entrypoint
}

predicate entryTransitionResume(s:state, s':state, d:PageDb, dispPg:PageNr)
    requires validDispatcherPage(d, dispPg)
{
    ValidState(s) && ValidState(s')
    && evalEnterUserspace(s, s')
    && s'.steps == s.steps + 1
    && (var disp := d[dispPg].entry;
    OperandContents(s, OLR) == disp.ctxt.pc)
}

predicate userspaceExecution(hw:state, hw':state, d:PageDb)
    requires ValidState(hw) && mode_of_state(hw) == User
    ensures userspaceExecution(hw, hw', d) ==> mode_of_state(hw') != User
{
    validERTransitionHW(hw, hw', d)
    && exists s, ex :: evalUserspaceExecution(hw, s)
    && evalExceptionTaken(s, ex, hw')
    // frownyface about this assert -> :(
    && WSMemInvariantExceptAddrspace(hw, hw', d)
    && hw.conf.excount + 1 == hw'.conf.excount
    && hw'.conf.exstep == hw'.steps
    && mode_of_state(hw') != User
}

//-----------------------------------------------------------------------------
// Exception Handler Spec
//-----------------------------------------------------------------------------
function exceptionHandled(s:state, d:PageDb, dispPg:PageNr) : (word, word, PageDb)
    requires ValidState(s) && validPageDb(d)
    requires mode_of_state(s) != User
    requires validDispatcherPage(d, dispPg)
    // This should be true since the exception is taken from user mode
    requires 
        (reveal_ValidSRegState();
        decode_mode'(psr_mask_mode(
        s.sregs[spsr(mode_of_state(s))])) == Just(User))
    ensures var (r0,r1,d') := exceptionHandled(s, d, dispPg);
        wellFormedPageDb(d')
{
    reveal_validPageDb();
    reveal_ValidSRegState();
    reveal_ValidRegState();
    if(s.conf.ex.ExSVC?) then
        var p := dispPg;
        var d' := d[ p := d[p].(entry := d[p].entry.(entered := false))];
        (KOM_ERR_SUCCESS(), s.regs[R0], d')
    else 
        var p := dispPg;
        var pc := OperandContents(s, OLR);
        var psr := s.sregs[spsr(mode_of_state(s))];
        assert decode_mode'(psr_mask_mode(psr)) == Just(User);
        var ctxt' := DispatcherContext(s.regs, pc, psr);
        assert decode_mode'(psr_mask_mode(ctxt'.cpsr)) == Just(User);
        assert validDispatcherContext(ctxt');
        var disp' := d[p].entry.(entered:=true, ctxt:=ctxt');
        var d' := d[ p := d[p].(entry := disp') ];
        assert wellFormedPageDbEntry(d[p].(entry := disp'));
        assert wellFormedPageDb(d');
        if s.conf.ex.ExIRQ? || s.conf.ex.ExFIQ? then
            (KOM_ERR_INTERRUPTED(), 0, d')
        else
            assert s.conf.ex.ExAbt? || s.conf.ex.ExUnd? ||
                s.conf.ex.ExUnd?;
            (KOM_ERR_FAULT(), 0, d')
}

predicate {:opaque} validExceptionTransition(s:SysState, s':SysState, dispPg: PageNr)
    requires validDispatcherPage(s.d, dispPg)
    ensures validExceptionTransition(s,s',dispPg) ==>
        validSysState(s) && validSysState(s')
{
    reveal_validPageDb();
    reveal_ValidRegState();
    reveal_ValidMemState();
    validSysState(s) && validSysState(s') &&
    (validERTransitionHW(s.hw, s'.hw, s.d)
    && equivalentExceptPage(s.d, s'.d, dispPg)
    && nonStoppedDispatcher(s.d, dispPg) && nonStoppedDispatcher(s'.d, dispPg)
    && page_paddr(l1pOfDispatcher(s.d, dispPg)) == s.hw.conf.ttbr0.ptbase
    && s.hw.conf.ttbr0.ptbase == s'.hw.conf.ttbr0.ptbase
    && (forall a:addr | a in TheValidAddresses() && !(StackLimit() <= a < StackBase()) &&
        !(addrInPage(a, dispPg)) :: s.hw.m.addresses[a] == s'.hw.m.addresses[a])
    && mode_of_state(s.hw) != User
    && mode_of_state(s'.hw) == Monitor)
}

// All writeable and secure memory addresses except the ones in the active l1
// page table have their contents preserved
predicate WSMemInvariantExceptAddrspace(hw:state, hw':state, d:PageDb)
    // requires validERTransition(s, s')
    // requires userEnteredState(s) && userEnteredState(s')
    requires ValidState(hw)
    requires validERTransitionHW(hw, hw', d)
{
    reveal_ValidSRegState();
    WSMemInvariantExceptAddrspaceAtPage(hw, hw', d,
        securePageFromPhysAddr(hw.conf.ttbr0.ptbase))
}

predicate WSMemInvariantExceptAddrspaceAtPage(hw:state, hw':state, 
        d:PageDb, l1p:PageNr)
    requires ValidState(hw) && ValidState(hw') && nonStoppedL1(d, l1p)
{
    forall a | ValidMem(a) && address_is_secure(a) && !memSWrInAddrspace(d, l1p, a) ::
        MemContents(hw.m, a) == MemContents(hw'.m, a)
}


// Is the page secure, writeable, and in the L1PT
predicate pageSWrInAddrspace(d:PageDb, l1p:PageNr, p:PageNr)
    requires validPageNr(p) && validL1PTPage(d, l1p)
    requires (validPageDbImpliesWellFormed(d); !hasStoppedAddrspace(d, l1p))
{
    reveal_validPageDb();
    !hasStoppedAddrspace(d, l1p) && 
    var l1pt := d[l1p].entry.l1pt;
    exists p' :: Just(p') in l1pt && assert validL1PTE(d, p'); pageSWrInL2PT(d[p'].entry.l2pt,p)
}

predicate memSWrInAddrspace(d:PageDb, l1p:PageNr, m: addr)
    requires validL1PTPage(d, l1p)
    requires (validPageDbImpliesWellFormed(d); !hasStoppedAddrspace(d, l1p))
{
    exists p | validPageNr(p) :: pageSWrInAddrspace(d, l1p, p) && addrInPage(m, p)
}

// is the page secure, writeable, and in the L2PT
predicate pageSWrInL2PT(l2pt:seq<L2PTE>, p:PageNr)
{
    exists pte :: pte in l2pt && pte.SecureMapping? && pte.page == p && pte.write
}

predicate equivalentExceptPage(d:PageDb, d':PageDb, p:PageNr)
    requires validPageNr(p)
    requires validPageDb(d) && validPageDb(d')
{
    validPageDbImpliesWellFormed(d);
    validPageDbImpliesWellFormed(d');
    forall p' :: validPageNr(p') && p' != p ==> d[p'] == d'[p']
}
