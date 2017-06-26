include "entry.s.dfy"
include "ptables.i.dfy"
include "psrbits.i.dfy"
include "svcapi.i.dfy"

//-----------------------------------------------------------------------------
// Functional model of user execution
//-----------------------------------------------------------------------------

predicate userExecutionPreconditions(s:state)
{
    var spsr := OSReg(spsr(mode_of_state(s)));
    ValidState(s) && mode_of_state(s) != User
    && ValidPsrWord(OperandContents(s, spsr))
    && decode_mode(psr_mask_mode(OperandContents(s, spsr))) == User
    && ExtractAbsPageTable(s).Just?
}

function userExecutionModelSteps(s:state): (state, state, word, exception, state)
    requires userExecutionPreconditions(s)
{
    var spsr_reg := spsr(mode_of_state(s));
    var spsr_val := OperandContents(s, OSReg(spsr_reg));
    var s2 := takestep(s).(sregs := s.sregs[cpsr := spsr_val],
                          conf := update_config_from_sreg(s, cpsr, spsr_val));
    assert evalEnterUserspace(s, s2);
    var (s3, expc, ex) := userspaceExecutionFn(s2, OperandContents(s, OLR));
    lemma_psr_of_exception(s3, ex);
    var s4 := exceptionTakenFn(s3, ex, expc);
    assert evalExceptionTaken(s3, ex, expc, s4);
    (s2, s3, expc, ex, s4)
}

lemma lemma_executionPreservesMasks(s:state, r:state)
    requires userExecutionPreconditions(s)
    requires ValidState(r)
    requires !spsr_of_state(s).f && !spsr_of_state(s).i
    requires r == userExecutionModel(s)
    requires mode_of_state(r) !=User && spsr_of_state(r).m == User
    ensures  !spsr_of_state(r).f && !spsr_of_state(r).i
{
    var (s2, s3, expc, ex, s4) := userExecutionModelSteps(s);
    assert s4 == r by { reveal userExecutionModel(); }
    assert !s2.conf.cpsr.f && !s2.conf.cpsr.i by
    {
        reveal userExecutionModel();
    }
    assert (s3, expc, ex) == userspaceExecutionFn(s2,
        OperandContents(s, OLR)) by
            { reveal userExecutionModel(); }
    assert decode_psr(s3.sregs[cpsr]) == s2.conf.cpsr by
        { reveal userspaceExecutionFn(); }
    assert !decode_psr(s3.sregs[cpsr]).f && !decode_psr(s3.sregs[cpsr]).i;
    var newmode := mode_of_exception(s3.conf, ex);
    assert s4 == exceptionTakenFn(s3, ex, expc) by
        { reveal userExecutionModel(); }
    assert s4.sregs[spsr(newmode)] == s3.sregs[cpsr];
    var maskfiq := ex == ExFIQ || newmode == Monitor;
    lemma_update_psr(s3.sregs[cpsr], encode_mode(newmode), maskfiq, true);
    assert mode_of_state(s4) == newmode;
    calc {
        spsr_of_state(r);
        spsr_of_state(s4);
        decode_psr(s3.sregs[cpsr]);
    }
}

function {:opaque} userExecutionModel(s:state): state
    requires userExecutionPreconditions(s)
    ensures ValidState(userExecutionModel(s))
{
    userExecutionModelSteps(s).4
}

lemma lemma_userExecutionModel_validity(s:state, s2:state, r:state)
    requires ValidState(s) && ExtractAbsPageTable(s).Just?
    requires evalUserExecution(s, s2, r)
    ensures userExecutionPreconditions(s) && r == userExecutionModel(s)
{
    reveal userExecutionModel();
    var (s2, s3, expc, ex, s4) := userExecutionModelSteps(s);
    assert evalEnterUserspace(s, s2);
    lemma_psr_of_exception(s3, ex);
    assert evalExceptionTaken(s3, ex, expc, s4);
}

lemma lemma_userExecutionModel_validity_cont(s:state, r:state)
    requires ValidState(s) && evalMOVSPCLRUC(s, r)
    ensures userExecutionPreconditions(s)
    ensures UsermodeContinuationInvariant(userExecutionModel(s), r)
{
    reveal evalMOVSPCLRUC();
    assert ExtractAbsPageTable(s).Just?;
    var s2, s4 :| evalUserExecution(s, s2, s4) && UsermodeContinuationInvariant(s4, r);
    lemma_userExecutionModel_validity(s, s2, s4);
}

lemma lemma_userExecutionModel_sufficiency(s:state, r:state)
    requires userExecutionPreconditions(s)
    requires r == userExecutionModel(s)
    ensures userspaceExecutionAndException(s, r)
{
    var (s2, s3, expc, ex, s4) := userExecutionModelSteps(s);
    assert equivStates(s, s);
    assert evalEnterUserspace(s, s2);
    assert (s3, expc, ex) == userspaceExecutionFn(s2, OperandContents(s, OLR));
    lemma_psr_of_exception(s3, ex);
    assert evalExceptionTaken(s3, ex, expc, s4);
    lemma_evalExceptionTaken_Mode(s3, ex, expc, s4);
    assert mode_of_state(s4) != User;
    assert s4 == r by { reveal userExecutionModel(); }
    assert userspaceExecutionAndException'(s, s, s2, r);
    reveal userspaceExecutionAndException();
}

//-----------------------------------------------------------------------------
// Exception handler invariants
//-----------------------------------------------------------------------------

const EXCEPTION_STACK_BYTES:int := 150*WORDSIZE;

predicate KomUserEntryPrecondition(s:state, pagedb:PageDb, dispPg:PageNr)
{
    SaneConstants() && ValidState(s) && s.ok && SaneStack(s) && SaneMem(s.m)
    && s.conf.scr == SCRT(Secure, true, true)
    && StackBytesRemaining(s, EXCEPTION_STACK_BYTES)
    && validPageDb(pagedb) && pageDbCorresponds(s.m, pagedb)
    && finalDispatcher(pagedb, dispPg)
    && GlobalWord(s.m, CurDispatcherOp(), 0) == page_monvaddr(dispPg)
    && s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(pagedb, dispPg))    
    && mode_of_state(s) != User
    && !spsr_of_state(s).f && !spsr_of_state(s).i
    // && (!(s.conf.ex == ExFIQ || s.conf.ex == ExIRQ) ==>
    //     !spsr_of_state(s).f && !spsr_of_state(s).i)
}

predicate PrivKomUserEntryPrecondition(s:state, pagedb:PageDb, dispPg:PageNr)
{
    SaneConstants() && ValidState(s) && s.ok && SaneStack(s) && SaneMem(s.m)
    && s.conf.scr == SCRT(Secure, true, true)
    && StackBytesRemaining(s, EXCEPTION_STACK_BYTES)
    && validPageDb(pagedb) && pageDbCorresponds(s.m, pagedb)
    && finalDispatcher(pagedb, dispPg)
    && GlobalWord(s.m, CurDispatcherOp(), 0) == page_monvaddr(dispPg)
    && s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(pagedb, dispPg))    
    && mode_of_state(s) != User
    // && !spsr_of_state(s).f && !spsr_of_state(s).i
    // && (!(s.conf.ex == ExFIQ || s.conf.ex == ExIRQ) ==>
    //     !spsr_of_state(s).f && !spsr_of_state(s).i)
}

predicate UsermodeContinuationPreconditionDefInner()
{
    forall s:state {:trigger UsermodeContinuationPrecondition(s)} ::
        ValidState(s) && UsermodeContinuationPrecondition(s)
        <==> (exists pagedb, dispPg:PageNr :: KomUserEntryPrecondition(s, pagedb, dispPg))
}

// XXX: the charade of inner/outer def and lemmas here are workarounds
// for an opaque/reveal bug in dafny
predicate {:opaque} UsermodeContinuationPreconditionDef()
{ UsermodeContinuationPreconditionDefInner() }

lemma lemma_UsermodeContinuationPreconditionDefInner()
    requires UsermodeContinuationPreconditionDef()
    ensures UsermodeContinuationPreconditionDefInner()
{ reveal UsermodeContinuationPreconditionDef(); }

lemma lemma_UsermodeContinuationPreconditionDef(s:state)
    returns (pagedb:PageDb, dispPg:PageNr)
    requires UsermodeContinuationPreconditionDef()
    requires ValidState(s) && UsermodeContinuationPrecondition(s)
    ensures KomUserEntryPrecondition(s, pagedb, dispPg)
{
    lemma_UsermodeContinuationPreconditionDefInner();
    pagedb, dispPg :| KomUserEntryPrecondition(s, pagedb, dispPg);
}

lemma lemma_Establish_UsermodeContinuationPrecondition(s:state, pagedb:PageDb, dispPg:PageNr)
    requires UsermodeContinuationPreconditionDef()
    requires KomUserEntryPrecondition(s, pagedb, dispPg)
    ensures UsermodeContinuationPrecondition(s)
{
    lemma_UsermodeContinuationPreconditionDefInner();
}

// SaneState, but not SaneStack
predicate SaneStateAfterException(s:state)
{
    SaneConstants()
    && ValidState(s)
    && SaneMem(s.m)
    && mode_of_state(s) == Monitor
    && !interrupts_enabled(s)
    //&& !spsr_of_state(s).f && !spsr_of_state(s).i
}

// what do we know between the start and end of the exception handler
// (after evalExceptionTaken, until the continuation)?
predicate KomExceptionHandlerInvariant(s:state, sd:PageDb, r:state, dp:PageNr)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires validPageDb(sd) && pageDbCorresponds(s.m, sd)
    requires finalDispatcher(sd, dp)
{
    reveal ValidRegState();
    var retToEnclave := isReturningSvc(s);
    var rd := if retToEnclave    then svcHandled(s, sd, dp).1
                                else exceptionHandled(s, sd, dp).2;
    validExceptionTransition(s, sd, r, rd, dp)
    // sp unaltered except it may have the low bit set to signify !retToEnclave
    && var ssp, rsp := s.regs[SP(Monitor)], r.regs[SP(Monitor)];
    SaneStateAfterException(r) && (s.ok ==> r.ok)
    && SaneStackPointer(ssp)
    && ParentStackPreserving(s, r)
    && s.conf.ttbr0 == r.conf.ttbr0 && s.conf.scr == r.conf.scr
    && (forall a:addr | ValidMem(a) && !(StackLimit() <= a < StackBase()) &&
        !addrInPage(a, dp) :: MemContents(s.m, a) == MemContents(r.m, a))
    && GlobalsPreservingExcept(s, r, {PendingInterruptOp()})
    && pageDbCorresponds(r.m, rd)
    && (if retToEnclave
       then rsp == ssp
        && var (regs, rd) := svcHandled(s, sd, dp); preEntryReturn(s, r, regs, rd, dp)
       else rsp == BitwiseOr(ssp, 1)
        && (r.regs[R0], r.regs[R1], rd) == exceptionHandled(s, sd, dp))
}

// this lemma is trivial, but justifies the soundness of the ARMdef assumptions
// ("EssentialContinuationInvariantProperties") about the handler
lemma lemma_KomExceptionHandlerInvariant_soundness(s:state, sd:PageDb, r:state,
                                                   dp:PageNr)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires validPageDb(sd) && pageDbCorresponds(s.m, sd)
    requires finalDispatcher(sd, dp)
    requires KomExceptionHandlerInvariant(s, sd, r, dp)
    ensures EssentialContinuationInvariantProperties(s, r)
{}

predicate {:opaque} UsermodeContinuationInvariantDef()
    requires SaneConstants()
{
    reveal ValidRegState();
    forall s:state, r:state, sd: PageDb, dp:PageNr
        | ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
            && validPageDb(sd) && pageDbCorresponds(s.m, sd)
            && finalDispatcher(sd, dp)
        :: UsermodeContinuationInvariant(s, r)
        ==> KomExceptionHandlerInvariant(s, sd, r, dp)
}

lemma lemma_UsermodeContinuationInvariantDef(s:state, r:state, d:PageDb, dp:PageNr)
    requires SaneConstants() && UsermodeContinuationInvariantDef()
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
        && validPageDb(d) && pageDbCorresponds(s.m, d)
        && finalDispatcher(d, dp)
    requires UsermodeContinuationInvariant(s, r)
    ensures KomExceptionHandlerInvariant(s, d, r, dp)
{
    reveal UsermodeContinuationInvariantDef();
}

//-----------------------------------------------------------------------------
// Proofs about userspace execution and related transitions
//-----------------------------------------------------------------------------

lemma lemma_exceptionHandled_validPageDb(s:state, d:PageDb, dispPg:PageNr)
    requires ValidState(s) && mode_of_state(s) != User && spsr_of_state(s).m == User
    requires !spsr_of_state(s).f && !spsr_of_state(s).i
    requires validPageDb(d) && validDispatcherPage(d, dispPg)
    ensures validPageDb(exceptionHandled(s, d, dispPg).2)
{
    reveal validPageDb();

    var d' := exceptionHandled(s, d, dispPg).2;
    var ex := s.conf.ex;

    if !(ex.ExSVC? || ex.ExAbt? || ex.ExUnd?) {
        reveal ValidSRegState();
        var dc := d'[dispPg].entry.ctxt;
        assert dc.cpsr == s.sregs[spsr(mode_of_state(s))];
        assert spsr_of_state(s).m == decode_psr(s.sregs[spsr(mode_of_state(s))]).m;
        assert decode_mode'(psr_mask_mode(dc.cpsr)) == Just(User);
        assert psr_mask_fiq(dc.cpsr) == 0;
        assert psr_mask_irq(dc.cpsr) == 0;
        assert validDispatcherContext(dc);
    }
    assert validPageDbEntry(d', dispPg);

    forall( p' | validPageNr(p') && d'[p'].PageDbEntryTyped? && p' != dispPg )
        ensures validPageDbEntry(d', p');
    {
        var e  := d[p'].entry;
        var e' := d'[p'].entry;
        if(e.Addrspace?){
            assert e.refcount == e'.refcount;
            assert addrspaceRefs(d', p') == addrspaceRefs(d,p');
            assert validAddrspace(d',p');
        }
    }

    assert pageDbEntriesValid(d');
    assert validPageDb(d');
}

lemma lemma_nonWritablePagesAreSafeFromHavoc(m:addr,s:state,s':state)
    requires userExecutionPreconditions(s) && userExecutionModel(s) == s'
    requires ValidMem(m)
    requires PageBase(m) !in WritablePagesInTable(ExtractAbsPageTable(s).v)
    ensures MemContents(s'.m, m) == MemContents(s.m, m)
{
    var pt := ExtractAbsPageTable(s).v;
    var user_state := user_visible_state(s, OperandContents(s, OLR), pt);
    var pages := WritablePagesInTable(pt);
    calc {
        s'.m.addresses[m];
        { reveal userExecutionModel(); reveal_userspaceExecutionFn(); }
        havocPages(pages, s, user_state)[m];
        s.m.addresses[m];
    }
}

lemma lemma_onlyDataPagesAreWritable(p:PageNr,a:addr,d:PageDb,s:state,s':state,l1:PageNr)
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires userExecutionPreconditions(s) && userExecutionModel(s) == s'
    requires validPageDb(d)
    requires SaneMem(s.m) && pageDbCorresponds(s.m, d)
    requires WordAligned(a) && addrInPage(a, p)
    requires s.conf.ttbr0.ptbase == page_paddr(l1);
    requires nonStoppedL1(d, l1) && !pageSWrInAddrspace(d, l1, p)
    ensures var pt := ExtractAbsPageTable(s);
        pt.Just? && var pages := WritablePagesInTable(fromJust(pt));
        PageBase(a) !in pages
{
    reveal validPageDb();

    var pt := ExtractAbsPageTable(s);
    assert pt.Just? by { reveal userspaceExecutionFn(); }
    var pages := WritablePagesInTable(fromJust(pt));
    var vbase := s.conf.ttbr0.ptbase + PhysBase();
    var pagebase := PageBase(a);

    assert ExtractAbsL1PTable(s.m, vbase) == fromJust(pt);

    assert fromJust(pt) == mkAbsPTable(d, l1) by 
    {
        lemma_ptablesmatch(s.m, d, l1);    
    }
    assert WritablePagesInTable(fromJust(pt)) ==
        WritablePagesInTable(mkAbsPTable(d, l1));
    
    forall( a':addr, p':PageNr | 
        var pagebase' := PageBase(a');
        pagebase' in WritablePagesInTable(fromJust(pt)) &&
        addrInPage(a',p') )
        ensures d[p'].PageDbEntryTyped? && d[p'].entry.DataPage?
        ensures pageSWrInAddrspace(d, l1, p')
    {
        var pagebase' := PageBase(a');
        assert addrInPage(a', p') <==> addrInPage(pagebase', p') by {
            lemma_bitMaskAddrInPage(a', p');
        }
        lemma_writablePagesAreDataPages(p', pagebase', d, l1);
    }
}

lemma lemma_writablePagesAreDataPages(p:PageNr,a:addr,d:PageDb,l1p:PageNr)
    requires PhysBase() == KOM_DIRECTMAP_VBASE   
    requires validPageDb(d)     
    requires nonStoppedL1(d, l1p) 
    requires PageAligned(a) && address_is_secure(a) 
    requires a in WritablePagesInTable(mkAbsPTable(d, l1p)) 
    requires addrInPage(a, p)
    ensures d[p].PageDbEntryTyped? && d[p].entry.DataPage?
    ensures pageSWrInAddrspace(d, l1p, p)
{
    reveal validPageDb();
    reveal pageDbEntryCorresponds();
    reveal pageContentsCorresponds();
    lemma_WritablePages(d, l1p, a);
}

lemma lemma_ExtractSamePages(m1:memstate, m2:memstate, p:PageNr)
    requires SaneMem(m1) && SaneMem(m2)
    requires forall a:addr | page_monvaddr(p) <= a < page_monvaddr(p) + PAGESIZE
                :: MemContents(m1, a) == MemContents(m2, a)
    ensures extractPage(m1, p) == extractPage(m2, p)
{}

lemma lemma_updateUserPagesFromState(s:state, d:PageDb, d':PageDb,
                                     dispPg:PageNr, p:PageNr)
    requires ValidState(s) && validPageDb(d) && SaneConstants()
    requires finalDispatcher(d, dispPg)
    requires d' == updateUserPagesFromState(s, d, dispPg)
    ensures d'[p] == d[p] || (d[p].PageDbEntryTyped? && d[p].entry.DataPage? && d'[p] == updateUserPageFromState(s, d, p))
{ reveal updateUserPagesFromState(); }

lemma lemma_contentsOfPage_corresponds(s:state, d:PageDb, p:PageNr)
    requires ValidState(s) && SaneMem(s.m) && validPageDb(d)
    requires d[p].PageDbEntryTyped? && d[p].entry.DataPage?
    requires d[p].entry.contents == contentsOfPage(s, p)
    ensures pageContentsCorresponds(p, d[p], extractPage(s.m, p))
{
    reveal pageContentsCorresponds();
    reveal pageDbDataCorresponds();
    forall ( i | 0 <= i < PAGESIZE / WORDSIZE )
    ensures extractPage(s.m, p)[page_monvaddr(p) + i * WORDSIZE] == contentsOfPage(s, p)[i]
    {
        calc {
            contentsOfPage(s, p)[i];
            MemContents(s.m, page_monvaddr(p) + i * WORDSIZE);
            extractPage(s.m, p)[page_monvaddr(p) + i * WORDSIZE];
        }
    }
}

lemma lemma_monvaddr_ValidMem(p:PageNr, a:addr)
    requires page_monvaddr(p) <= a < page_monvaddr(p) + PAGESIZE
    requires SaneConstants()
    ensures ValidMem(a)
{}

lemma lemma_userExecutionUpdatesPageDb(d:PageDb, s:state, s':state, dispPg:PageNr)
    requires validPageDb(d) && finalDispatcher(d, dispPg)
    requires userExecutionPreconditions(s) && userExecutionModel(s) == s'
    requires SaneMem(s.m) && pageDbCorresponds(s.m, d) && SaneMem(s'.m)
    requires s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(d, dispPg))
    ensures  pageDbCorresponds(s'.m, updateUserPagesFromState(s', d, dispPg))
{
    var d' := updateUserPagesFromState(s', d, dispPg);
    var l1 := l1pOfDispatcher(d, dispPg);
    assert nonStoppedL1(d, l1);

    forall ( p | validPageNr(p) )
        ensures pageDbEntryCorresponds(d'[p], extractPageDbEntry(s'.m, p))
    {
        lemma_updateUserPagesFromState(s', d, d', dispPg, p);
        PageDbCorrespondsImpliesEntryCorresponds(s.m, d, p);
        assert pageDbEntryCorresponds(d[p], extractPageDbEntry(s.m, p));
        lemma_userExecutionPreservesPrivState(s, s');
        assert extractPageDbEntry(s.m, p) == extractPageDbEntry(s'.m, p);
        reveal pageDbEntryCorresponds();
    }

    assert {:split_here} true;

    forall ( p | validPageNr(p) )
        ensures pageContentsCorresponds(p, d'[p], extractPage(s'.m, p));
    {
        if pageSWrInAddrspace(d, l1, p) {
            reveal updateUserPagesFromState();
            lemma_contentsOfPage_corresponds(s', d', p);
        } else if d[p].PageDbEntryTyped? {
            assert d[p] == d'[p] by { reveal updateUserPagesFromState(); }

            forall ( a:addr |
                    page_monvaddr(p) <= a < page_monvaddr(p) + PAGESIZE )
                ensures MemContents(s'.m, a) == MemContents(s.m, a)
            {
                var pt := ExtractAbsPageTable(s);
                lemma_ptablesmatch(s.m, d, l1);
                assert pt.Just?;
                var pages := WritablePagesInTable(fromJust(pt));

                lemma_onlyDataPagesAreWritable(p, a, d, s, s', l1);
                assert PageBase(a) !in pages;
                lemma_monvaddr_ValidMem(p, a);
                lemma_nonWritablePagesAreSafeFromHavoc(a, s, s');
            }
            lemma_ExtractSamePages(s.m, s'.m, p);
            reveal pageContentsCorresponds();
        } else {
            assert d[p] == d'[p] by { reveal updateUserPagesFromState(); }
            reveal pageContentsCorresponds();
        }
    }
}

lemma lemma_PageBase_properties(a: word)
    ensures PageBase(a) <= a
{ reveal PageBase(); lemma_DivMulLessThan(a, PAGESIZE); }

lemma lemma_userExecutionPreservesStack(d:PageDb,s:state,s':state, l1:PageNr)
    requires SaneMem(s.m) && SaneMem(s'.m) && validPageDb(d)
        && ValidState(s) && ValidState(s')
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires userExecutionPreconditions(s) && userExecutionModel(s) == s'
    requires pageDbCorresponds(s.m, d)
    requires s.conf.ttbr0.ptbase == page_paddr(l1);
    requires nonStoppedL1(d, l1);
    ensures forall a:addr | StackLimit() <= a < StackBase() ::
        MemContents(s.m, a) == MemContents(s'.m, a)
{
    assert StackBase() <= PhysBase();
    var pt := ExtractAbsPageTable(s).v;
    var pages := WritablePagesInTable(pt);
    forall (a | ValidMem(a) && a < PhysBase())
        ensures MemContents(s.m, a) == MemContents(s'.m, a)
    {
        assert PageBase(a) <= a < PhysBase() by { lemma_PageBase_properties(a); }
        assert PageBase(a) !in pages;
        lemma_nonWritablePagesAreSafeFromHavoc(a, s, s');
    }
}

lemma lemma_userExecutionPreservesPrivState(s:state, r:state)
    requires userExecutionPreconditions(s) && userExecutionModel(s) == r
    ensures GlobalsInvariant(s,r)
    ensures (reveal ValidRegState(); s.regs[SP(Monitor)] == r.regs[SP(Monitor)])
    ensures mode_of_state(r) != User && spsr_of_state(r).m == User
    ensures r.conf.scr == s.conf.scr
    ensures r.conf.ttbr0 == s.conf.ttbr0
    ensures r.ok == s.ok
{
    var (s2, s3, expc, ex, s4) := userExecutionModelSteps(s);
    assert s4 == r by { reveal userExecutionModel(); }
    lemma_evalExceptionTaken_Mode(s3, ex, expc, r);
    reveal userspaceExecutionFn();
}

predicate {:opaque} OpaqueEven(x:word) { x % 2 == 0 }

lemma lemma_sp_alignment(x:word)
    requires OpaqueEven(x)
    ensures x != BitwiseOr(x, 1)
{
    reveal OpaqueEven();
    assert BitsAsWord(1) == 1 && BitsAsWord(2) == 2 by { reveal BitsAsWord(); }
    lemma_BitsAndWordConversions();

    assert BitMod(WordAsBits(x), 2) == 0 by { lemma_BitModEquiv(x, 2); }
    assert x != BitwiseOr(x, 1) by { reveal BitOr(); reveal_BitMod(); }
}

lemma lemma_evalMOVSPCLRUC_inner(s:state, r:state, d:PageDb, dp:PageNr)
        returns (s4:state, d4:PageDb)
    requires SaneState(s)
    requires validPageDb(d) && pageDbCorresponds(s.m, d) && finalDispatcher(d, dp)
    requires s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(d, dp))
    requires mode_of_state(s) == Monitor && spsr_of_state(s).m == User
    requires evalMOVSPCLRUC(s, r)
    requires UsermodeContinuationInvariantDef()
    requires !spsr_of_state(s).f && !spsr_of_state(s).i
    ensures SaneStateAfterException(r)
    ensures OperandContents(r, OSP) == OperandContents(s, OSP)
        || OperandContents(r, OSP) == BitwiseOr(OperandContents(s, OSP), 1)
    ensures OperandContents(s, OSP) != BitwiseOr(OperandContents(s, OSP), 1)
    ensures ParentStackPreserving(s, r)
    ensures GlobalsPreservingExcept(s, r, {PendingInterruptOp()})
    ensures userspaceExecutionAndException(s, s4)
    ensures mode_of_state(s4) != User && spsr_of_state(s4).m == User
    ensures SaneMem(s4.m)
    ensures (reveal ValidRegState(); s.regs[SP(Monitor)] == s4.regs[SP(Monitor)])
    ensures d4 == updateUserPagesFromState(s4, d, dp) && pageDbCorresponds(s4.m, d4)
    ensures KomExceptionHandlerInvariant(s4, d4, r, dp)
    ensures s.conf.ttbr0 == r.conf.ttbr0
    ensures s.conf.scr == r.conf.scr
    ensures !spsr_of_state(s4).f && !spsr_of_state(s4).i
{
    // XXX: prove some obvious things about OSP early, to stop Z3 getting lost
    assert ValidOperand(OSP);
    assert OperandContents(s, OSP) == s.regs[SP(Monitor)];
    assert OpaqueEven(OperandContents(s, OSP)) by { reveal OpaqueEven(); }
    lemma_sp_alignment(OperandContents(s, OSP));
    assert ValidMemRange(StackLimit(), StackBase());

    var spsr := OperandContents(s, OSReg(spsr(Monitor)));
    assert ValidPsrWord(spsr) && decode_mode(psr_mask_mode(spsr)) == User
        by { reveal ValidSRegState(); }
    lemma_ptablesmatch(s.m, d, l1pOfDispatcher(d, dp));
    assert userExecutionPreconditions(s);

    lemma_userExecutionModel_validity_cont(s, r);
    s4 := userExecutionModel(s);
    lemma_userExecutionModel_sufficiency(s, s4);
    d4 := updateUserPagesFromState(s4, d, dp);
    lemma_userExecutionPreservesPrivState(s, s4);
    lemma_userExecutionUpdatesPageDb(d, s, s4, dp);
    assert pageDbCorresponds(s4.m, d4);
    lemma_UsermodeContinuationInvariantDef(s4, r, d4, dp);
    assert GlobalsInvariant(s, s4) && GlobalsPreservingExcept(s4, r, {PendingInterruptOp()});

    lemma_executionPreservesMasks(s, s4);
    assert s4.regs[SP(Monitor)] == OperandContents(r, OSP)
        || BitwiseOr(s4.regs[SP(Monitor)], 1) == OperandContents(r, OSP);

    assert ParentStackPreserving(s, r) by {
        lemma_userExecutionPreservesStack(d, s, s4, l1pOfDispatcher(d, dp));
        assert ParentStackPreserving(s4, r);
    }
}

lemma lemma_pageDbCorrespondsForSpec(s:state, d:PageDb, l1:PageNr)
    requires SaneState(s) && validPageDb(d) && pageDbCorresponds(s.m, d)
    requires nonStoppedL1(d, l1)
    requires s.conf.ttbr0.ptbase == page_paddr(l1)
    ensures pageTableCorresponds(s, d, l1) && dataPagesCorrespond(s.m, d)
{
    forall p:PageNr | d[p].PageDbEntryTyped? && d[p].entry.DataPage?
        ensures pageDbDataCorresponds(p, d[p].entry, extractPage(s.m, p))
    {
        reveal pageContentsCorresponds();
    }

    lemma_ptablesmatch(s.m, d, l1);
    reveal pageTableCorresponds();
}

lemma lemma_evalEnterUserspace_preservesAbsPageTable(s:state, r:state)
    requires ValidState(s) && evalEnterUserspace(s, r)
    ensures ExtractAbsPageTable(s) == ExtractAbsPageTable(r)
{
    assert s.m == r.m;
    assert s.conf.ttbr0 == r.conf.ttbr0;
}

lemma lemma_userspaceExecutionAndException_pre(s0:state, s1:state, r:state)
    requires ValidState(s1) && userspaceExecutionAndException(s1, r)
    requires equivStates(s0, s1)
    ensures userspaceExecutionAndException(s0, r)
{
    assert ExtractAbsPageTable(s1).Just? ==> ExtractAbsPageTable(s0).Just?;
    var s1lr := OperandContents(s1, OLR);
    assert s1lr == OperandContents(s0, OLR);
    reveal userspaceExecutionAndException();
    assert ExtractAbsPageTable(s1).Just?;
    var s', s2 :| userspaceExecutionAndException'(s1, s', s2, r);
    assert equivStates(s0, s');
    assert evalEnterUserspace(s', s2) && s2.steps == s'.steps + 1;
    lemma_evalEnterUserspace_preservesAbsPageTable(s', s2);
    var (s3, expc, ex) := userspaceExecutionFn(s2, OperandContents(s1, OLR));
    assert evalExceptionTaken(s3, ex, expc, r);
    assert r.conf.exstep == s3.steps;
    assert mode_of_state(r) != User;
    assert userspaceExecutionAndException'(s0, s', s2, r);
    assert userspaceExecutionAndException(s0, r);
}

lemma lemma_evalMOVSPCLRUC(s:state, sd:PageDb, r:state, dispPg:PageNr)
    returns (rd:PageDb, retToEnclave:bool)
    requires SaneState(s)
    requires spsr_of_state(s).m == User
    requires validPageDb(sd) && pageDbCorresponds(s.m, sd)
    requires finalDispatcher(sd, dispPg)
    requires s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(sd, dispPg))
    requires evalMOVSPCLRUC(takestep(s), r)
    requires UsermodeContinuationInvariantDef()
    requires !spsr_of_state(s).f && !spsr_of_state(s).i
    ensures SaneStateAfterException(r)
    ensures ParentStackPreserving(s, r)
    ensures GlobalsPreservingExcept(s, r, {PendingInterruptOp()})
    ensures OperandContents(s, OSP) != BitwiseOr(OperandContents(s, OSP), 1)
            && if retToEnclave
            then OperandContents(r, OSP) == OperandContents(s, OSP)
            else OperandContents(r, OSP) == BitwiseOr(OperandContents(s, OSP), 1)
    ensures s.conf.ttbr0 == r.conf.ttbr0
    ensures s.conf.scr == r.conf.scr
    ensures validPageDb(rd) && SaneMem(r.m) && pageDbCorresponds(r.m, rd)
    ensures validEnclaveExecutionStep(s, sd, r, rd, dispPg, retToEnclave)
    ensures retToEnclave ==> spsr_of_state(r).m == User
    ensures retToEnclave ==> !spsr_of_state(r).f && !spsr_of_state(r).i
{
    var s4, d4 := lemma_evalMOVSPCLRUC_inner(takestep(s), r, sd, dispPg);

    var ssp, rsp := OperandContents(s, OSP), OperandContents(r, OSP);
    assert rsp == r.regs[SP(Monitor)];

    assert !spsr_of_state(s4).f && !spsr_of_state(s4).i;

    retToEnclave := isReturningSvc(s4);
    if retToEnclave {
        assert ssp == rsp;
        var (regs, d4') := svcHandled(s4, d4, dispPg);
        //lemma_svcHandled_pageDbCorresponds(s4, d4, r, dispPg, regs, d4');
        lemma_svcHandled_validPageDb(s4, d4, dispPg, regs, d4');
        rd := d4';

        assert spsr_of_state(r).m == User by {
            assert preEntryReturn(s4, r, regs, rd, dispPg);
            assert (reveal ValidSRegState();
                        r.sregs[spsr(mode_of_state(r))] == encode_mode(User));
            assert decode_mode(psr_mask_mode(encode_mode(User))) == User by {
                assert WordAsBits(0x10) == 0x10 && WordAsBits(0x1f) == 0x1f
                    by { reveal WordAsBits(); }
                lemma_BitsAndWordConversions();
                reveal BitAnd();
            }
        }
    } else {
        assert rsp == BitwiseOr(ssp, 1);
        assert ssp != rsp;
        rd := exceptionHandled(s4, d4, dispPg).2;
        lemma_exceptionHandled_validPageDb(s4, d4, dispPg);
    }

    if(retToEnclave) {
       assert !spsr_of_state(r).f && !spsr_of_state(r).i by {
           assert psr_mask_fiq(encode_mode(User)) == 0 by {
               assert WordAsBits(0x10) == 0x10 && WordAsBits(0x40) == 0x40
                   by { reveal WordAsBits(); }
               lemma_BitsAndWordConversions();
               reveal BitAnd();
           }
           assert psr_mask_irq(encode_mode(User)) == 0 by {
               assert WordAsBits(0x10) == 0x10 && WordAsBits(0x80) == 0x80
                   by { reveal WordAsBits(); }
               lemma_BitsAndWordConversions();
               reveal BitAnd();
           }
       }
    }

    assert validEnclaveExecutionStep(s, sd, r, rd, dispPg, retToEnclave) by {
        reveal validEnclaveExecutionStep();
        lemma_userspaceExecutionAndException_pre(s, takestep(s), s4);
        lemma_pageDbCorrespondsForSpec(s, sd, l1pOfDispatcher(sd, dispPg));
        assert validExceptionTransition(s4, d4, r, rd, dispPg) by { reveal validExceptionTransition(); }
        assert validEnclaveExecutionStep'(s, sd, s4, d4, r, rd, dispPg, retToEnclave); // trigger exists
    }
    assert retToEnclave ==> !spsr_of_state(r).f && !spsr_of_state(r).i;
}

lemma lemma_ValidEntryPre(s0:state, s1:state, sd:PageDb, r:state, rd:PageDb, dp:word,
                           a1:word, a2:word, a3:word)
    requires ValidState(s0) && ValidState(s1) && ValidState(r) && validPageDb(sd)
    requires SaneConstants()
    requires s0.conf.nondet == s1.conf.nondet
    requires InsecureMemInvariant(s0, s1)
    ensures smc_enter(s1, sd, r, rd, dp, a1, a2, a3)
        ==> smc_enter(s0, sd, r, rd, dp, a1, a2, a3)
    ensures smc_resume(s1, sd, r, rd, dp) ==> smc_resume(s0, sd, r, rd, dp)
{
    if smc_enter(s1, sd, r, rd, dp, a1, a2, a3)
        && smc_enter_err(sd, dp, false) == KOM_ERR_SUCCESS {
        forall s | preEntryEnter(s1, s, sd, dp, a1, a2, a3)
            ensures preEntryEnter(s0, s, sd, dp, a1, a2, a3)
        {
        }
    }

    if smc_resume(s1, sd, r, rd, dp)
        && smc_enter_err(sd, dp, true) == KOM_ERR_SUCCESS {
        forall s | preEntryResume(s1, s, sd, dp)
            ensures preEntryResume(s0, s, sd, dp)
        {
        }
    }
}

lemma lemma_evalExceptionTaken_Mode(s:state, e:exception, expc:word, r:state)
    requires ValidState(s) && evalExceptionTaken(s, e, expc, r)
    ensures mode_of_state(r) == mode_of_exception(s.conf, e)
    ensures spsr_of_state(r) == s.conf.cpsr
{
    var newmode := mode_of_exception(s.conf, e);
    assert newmode != User;
    var f := e == ExFIQ || newmode == Monitor;
    reveal ValidSRegState();
    
    calc {
        mode_of_state(r);
        decode_psr(psr_of_exception(s, e)).m;
        { lemma_update_psr(s.sregs[cpsr], encode_mode(newmode), f, true); }
        decode_mode(encode_mode(newmode));
        { mode_encodings_are_sane(); }
        newmode;
    }
}

lemma lemma_validEnclaveExecutionStep_PageDb(s1:state, d1:PageDb, r1:state,
    rd:PageDb, dispPg:PageNr, retToEnclave:bool)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires finalDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s1, d1, r1, rd, dispPg, retToEnclave)
    ensures validPageDb(rd) && finalDispatcher(rd, dispPg)
    ensures l1pOfDispatcher(d1, dispPg) == l1pOfDispatcher(rd, dispPg)
{
    reveal validEnclaveExecutionStep();
    reveal updateUserPagesFromState();
    reveal validExceptionTransition();
}

lemma lemma_validEnclaveExecutionStepPost(s1:state, d1:PageDb, r1:state,
                            rd:PageDb, r2:state, dispPg:PageNr)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires finalDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s1, d1, r1, rd, dispPg, false)
    requires validExceptionTransition(r1, rd, r2, rd, dispPg)
    requires OperandContents(r1, OReg(R0)) == OperandContents(r2, OReg(R0))
    requires OperandContents(r1, OReg(R1)) == OperandContents(r2, OReg(R1))
    ensures validEnclaveExecutionStep(s1, d1, r2, rd, dispPg, false)
{
    reveal validEnclaveExecutionStep();
    reveal updateUserPagesFromState();
    reveal ValidRegState();

    var s4, d4 :|
        validEnclaveExecutionStep'(s1, d1, s4, d4, r1, rd, dispPg, false);

    assert validExceptionTransition(s4, d4, r2, rd, dispPg)
        by { reveal validExceptionTransition(); }
    assert (r2.regs[R0], r2.regs[R1], rd) == exceptionHandled(s4, d4, dispPg);
    assert validEnclaveExecutionStep'(s1, d1, s4, d4, r2, rd, dispPg, false);
}

lemma lemma_validEnclaveExecutionStepPre(s0:state, s1:state, sd:PageDb, r:state,
                                    rd:PageDb, dispPg:PageNr, retToEnclave:bool)
    requires ValidState(s1) && validPageDb(sd) && SaneConstants()
    requires finalDispatcher(sd, dispPg)
    requires validEnclaveExecutionStep(s1, sd, r, rd, dispPg, retToEnclave)
    requires equivStates(s0, s1)
    ensures validEnclaveExecutionStep(s0, sd, r, rd, dispPg, retToEnclave)
{
    var l1p := l1pOfDispatcher(sd, dispPg);
    reveal validEnclaveExecutionStep();
    assert pageTableCorresponds(s0, sd, l1p) by { reveal pageTableCorresponds(); }
    var s4, d4 :|
        validEnclaveExecutionStep'(s1, sd, s4, d4, r, rd, dispPg, retToEnclave);
    assert userspaceExecutionAndException(s1, s4);
    lemma_userspaceExecutionAndException_pre(s0, s1, s4);
    assert validEnclaveExecutionStep'(s0, sd, s4, d4, r, rd, dispPg, retToEnclave);
}

lemma lemma_validEnclaveExecutionPost(s1:state, d1:PageDb, r1:state, rd:PageDb,
                                      r2:state, dispPg:PageNr, steps:nat)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires finalDispatcher(d1, dispPg)
    requires validEnclaveExecution(s1, d1, r1, rd, dispPg, steps)
    requires validExceptionTransition(r1, rd, r2, rd, dispPg)
    requires OperandContents(r1, OReg(R0)) == OperandContents(r2, OReg(R0))
    requires OperandContents(r1, OReg(R1)) == OperandContents(r2, OReg(R1))
    ensures validEnclaveExecution(s1, d1, r2, rd, dispPg, steps)
    decreases steps
{
    reveal validEnclaveExecution();

    var retToEnclave := (steps > 0);
    var s5, d5 :|
        validEnclaveExecutionStep(s1, d1, s5, d5, dispPg, retToEnclave)
        && (lemma_validEnclaveExecutionStep_PageDb(s1, d1, s5, d5, dispPg, retToEnclave);
        if retToEnclave then
            validEnclaveExecution(s5, d5, r1, rd, dispPg, steps - 1)
        else
            r1 == s5 && rd == d5);

    if retToEnclave {
        lemma_validEnclaveExecutionPost(s5, d5, r1, rd, r2, dispPg, steps - 1);
    } else {
        lemma_validEnclaveExecutionStepPost(s1, d1, r1, rd, r2, dispPg);
    }
}

lemma lemma_validEnterPost(s:state, sd:PageDb, r1:state, rd:PageDb, r2:state, dp:word,
                           a1:word, a2:word, a3:word)
    requires ValidState(s) && ValidState(r1) && ValidState(r2) && validPageDb(sd)
    requires SaneConstants()
    requires smc_enter_err(sd, dp, false) == KOM_ERR_SUCCESS
    requires smc_enter(s, sd, r1, rd, dp, a1, a2, a3)
    requires validExceptionTransition(r1, rd, r2, rd, dp)
    requires OperandContents(r1, OReg(R0)) == OperandContents(r2, OReg(R0))
    requires OperandContents(r1, OReg(R1)) == OperandContents(r2, OReg(R1))
    ensures smc_enter(s, sd, r2, rd, dp, a1, a2, a3)
{
    var s1, steps:nat :|
        preEntryEnter(s, s1, sd, dp, a1, a2, a3)
        && validEnclaveExecution(s1, sd, r1, rd, dp, steps);

    lemma_validEnclaveExecutionPost(s1, sd, r1, rd, r2, dp, steps);
}

lemma lemma_validResumePost(s:state, sd:PageDb, r1:state, rd:PageDb, r2:state, dp:word)
    requires ValidState(s) && ValidState(r1) && ValidState(r2) && validPageDb(sd)
    requires SaneConstants()
    requires smc_enter_err(sd, dp, true) == KOM_ERR_SUCCESS
    requires smc_resume(s, sd, r1, rd, dp)
    requires validExceptionTransition(r1, rd, r2, rd, dp)
    requires OperandContents(r1, OReg(R0)) == OperandContents(r2, OReg(R0))
    requires OperandContents(r1, OReg(R1)) == OperandContents(r2, OReg(R1))
    ensures smc_resume(s, sd, r2, rd, dp)
{
    var s1, steps:nat :|
        preEntryResume(s, s1, sd, dp)
        && validEnclaveExecution(s1, sd, r1, rd, dp, steps);

    lemma_validEnclaveExecutionPost(s1, sd, r1, rd, r2, dp, steps);
}

function exPageDb(t: (int, int, PageDb)): PageDb { t.2 }

//-----------------------------------------------------------------------------
// Simplified (non-recursive) model of enclave execution steps
//-----------------------------------------------------------------------------

lemma lemma_singlestep_execution(s1:state, d1:PageDb,
    rs:state, rd:PageDb, dispPg:PageNr)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires finalDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s1, d1, rs, rd, dispPg, false)
    ensures validEnclaveExecution(s1, d1, rs, rd, dispPg, 0)
{
    reveal validEnclaveExecution();
    var retToEnclave := false;
    var steps := 0;
    var s5, d5 := rs, rd;
    assert (
        var retToEnclave := (steps > 0);
        exists s5, d5 {:trigger validEnclaveExecutionStep(s1, d1, s5, d5, dispPg, retToEnclave)} ::
            validEnclaveExecutionStep(s1, d1, s5, d5, dispPg, retToEnclave)
            && (if retToEnclave then
                validEnclaveExecution(s5, d5, rs, rd, dispPg, steps - 1)
              else
                rs == s5 && rd == d5));
}

predicate partialEnclaveExecution(l:seq<(state, PageDb)>, dispPg:PageNr, steps:nat)
    requires SaneConstants()
{
    |l| == steps + 1
    && (forall i | 0 <= i <= steps :: ValidState(l[i].0) && validPageDb(l[i].1)
                && finalDispatcher(l[i].1, dispPg))
    && (forall i {:trigger l[i]} | 0 < i <= steps ::
            validEnclaveExecutionStep(l[i-1].0, l[i-1].1, l[i].0, l[i].1, dispPg, true))
}

lemma lemma_partialEnclaveExecution_append(l:seq<(state, PageDb)>, s:state, d:PageDb, dispPg:PageNr, steps:nat)
    requires SaneConstants()
    requires ValidState(s) && validPageDb(d) && finalDispatcher(d, dispPg)
    requires partialEnclaveExecution(l, dispPg, steps)
    requires validEnclaveExecutionStep(l[steps].0, l[steps].1, s, d, dispPg, true)
    ensures partialEnclaveExecution(l + [(s, d)], dispPg, steps + 1)
{
    var l' := l + [(s, d)];
    var steps' := steps + 1;
    assert forall i | 0 <= i <= steps :: l[i] == l'[i]; // for triggers
    assert validEnclaveExecutionStep(l[steps].0, l[steps].1, s, d, dispPg, true);
    assert validEnclaveExecutionStep(l'[steps'-1].0, l'[steps'-1].1, l'[steps'].0, l'[steps'].1, dispPg, true);
}

lemma lemma_validEnclaveExecution_ExtraStep(s0:state, d0:PageDb, s1:state, d1:PageDb,
    rs:state, rd:PageDb, dispPg:PageNr, steps:nat)
    requires SaneConstants() && steps > 0
    requires ValidState(s0) && validPageDb(d0) && finalDispatcher(d0, dispPg)
    requires ValidState(s1) && validPageDb(d1) && finalDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s0, d0, s1, d1, dispPg, true)
    requires validEnclaveExecution(s1, d1, rs, rd, dispPg, steps - 1)
    ensures  validEnclaveExecution(s0, d0, rs, rd, dispPg, steps)
{
    reveal validEnclaveExecution();
}

lemma lemma_partialEnclaveExecution_done(l:seq<(state, PageDb)>, rs:state, rd:PageDb, dispPg:PageNr, steps:nat)
    requires SaneConstants()
    requires partialEnclaveExecution(l, dispPg, steps)
    requires validEnclaveExecutionStep(l[steps].0, l[steps].1, rs, rd, dispPg, false)
    ensures validEnclaveExecution(l[0].0, l[0].1, rs, rd, dispPg, steps)
    decreases steps
{
    if steps == 0 {
        lemma_singlestep_execution(l[0].0, l[0].1, rs, rd, dispPg);
    } else {
        var l' := l[1..];
        //assert forall i | 0 < i <= steps :: l[i] == l'[i-1]; // for triggers
        assert l'[0] == l[1];
        assert validEnclaveExecutionStep(l[0].0, l[0].1, l[1].0, l[1].1, dispPg, true);
        lemma_partialEnclaveExecution_done(l', rs, rd, dispPg, steps - 1);
        lemma_validEnclaveExecution_ExtraStep(l[0].0, l[0].1, l[1].0, l[1].1, rs, rd, dispPg, steps);
    }
}
