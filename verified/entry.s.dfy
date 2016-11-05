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

function securePageFromPhysAddr(phys:int): PageNr
    requires PageAligned(phys)
    requires SecurePhysBase() <= phys < SecurePhysBase() +
        KOM_SECURE_NPAGES() * PAGESIZE() // physPageIsSecure(phys/PAGESIZE())
    ensures validPageNr(securePageFromPhysAddr(phys))
{
    (phys - SecurePhysBase()) / PAGESIZE()
}

predicate {:opaque} validEnter(s:SysState,s':SysState,
    dispPg:word,a1:word,a2:word,a3:word)
    requires validSysState(s)
    requires smc_enter_err(s.d, dispPg, false) == KOM_ERR_SUCCESS()
{
    reveal_ValidRegState();
    reveal_validExceptionTransition();
    exists s1, s2, s3, ex, s4 ::
        preEntryEnter(s.hw, s1, s.d, dispPg, a1, a2, a3)
        && entryTransition(s1, s2)
        && userspaceExecutionAndException(s2, s3, ex, s4)
        && validExceptionTransition(SysState(s4, s.d), s', dispPg)
        && (s'.hw.regs[R0], s'.hw.regs[R1], s'.d) == exceptionHandled(s4, s.d, dispPg)
}

predicate {:opaque} validResume(s:SysState,s':SysState,dispPg:word)
    requires validSysState(s)
    requires smc_enter_err(s.d, dispPg, true) == KOM_ERR_SUCCESS()
{
     
    reveal_ValidRegState();
    reveal_validExceptionTransition();
    exists s1, s2, s3, ex, s4 ::
        preEntryResume(s.hw, s1, s.d, dispPg)
        && entryTransition(s1, s2)
        && userspaceExecutionAndException(s2, s3, ex, s4)
        && validExceptionTransition(SysState(s4, s.d), s', dispPg)
        && (s'.hw.regs[R0], s'.hw.regs[R1], s'.d) ==
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

    ValidState(s') && priv_of_state(s') == PL1 &&
    s'.conf.ttbr0.ptbase == page_paddr(l1p) &&
    s'.conf.scr.ns == Secure &&
    s'.regs[R0] == a1 && s'.regs[R1] == a2 && s'.regs[R2] == a3 &&
    OperandContents(s', OLR) == d[dispPage].entry.entrypoint &&
    (reveal_ValidSRegState();
    s'.sregs[spsr(mode_of_state(s'))] == 0x10 /* XXX: Usermode PSR */)
    // TODO (more generally than just entry!): we didn't scribble on any user memory
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
    
    ValidState(s') && priv_of_state(s') == PL1 &&
    s'.conf.ttbr0.ptbase == page_paddr(l1p) &&
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
    OperandContents(s', OLR) == disp.ctxt.pc &&

    (reveal_ValidSRegState();
    s'.sregs[spsr(Monitor)] == disp.ctxt.cpsr)

    // TODO (more generally than just entry!): we didn't scribble on any user memory
}

predicate entryTransition(s:state, s':state)
    requires ValidState(s)
    ensures entryTransition(s, s') ==> ValidState(s')
{
    // we've entered userland and done nothing else
    evalEnterUserspace(s, s') && s'.steps == s.steps + 1
}

predicate userspaceExecutionAndException(s:state, s':state, ex:exception, r:state)
    requires ValidState(s) && mode_of_state(s) == User
{
    evalUserspaceExecution(s, s')
    && evalExceptionTaken(s', ex, r)
    && s.conf.excount + 1 == r.conf.excount
    && r.conf.exstep == r.steps
}

//-----------------------------------------------------------------------------
// Exception Handler Spec
//-----------------------------------------------------------------------------
function exceptionHandled(s:state, d:PageDb, dispPg:PageNr) : (word, word, PageDb)
    requires validPageDb(d) && validDispatcherPage(d, dispPg)
    requires ValidState(s) && mode_of_state(s) != User
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
        var ctxt' := DispatcherContext(s.regs, pc, psr);
        var disp' := d[p].entry.(entered:=true, ctxt:=ctxt');
        var d' := d[ p := d[p].(entry := disp') ];
        if s.conf.ex.ExIRQ? || s.conf.ex.ExFIQ? then
            (KOM_ERR_INTERRUPTED(), 0, d')
        else
            assert s.conf.ex.ExAbt? || s.conf.ex.ExUnd? ||
                s.conf.ex.ExUnd?;
            (KOM_ERR_FAULT(), 0, d')
}

predicate {:opaque} validExceptionTransition(s:SysState, s':SysState, dispPg: word)
    ensures validExceptionTransition(s,s',dispPg) ==>
        validSysState(s) && validSysState(s')
{
    validSysState(s) && validSysState(s')
    && mode_of_state(s'.hw) == Monitor
    && (s.d == s'.d || (
        validPageNr(dispPg) && validDispatcherPage(s.d, dispPg)
        && equivalentExceptPage(s.d, s'.d, dispPg)
        && nonStoppedDispatcher(s'.d, dispPg)))
    // TODO: we didn't scribble on user memory
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
