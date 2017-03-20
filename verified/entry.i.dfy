include "entry.s.dfy"
include "ptables.i.dfy"
include "psrbits.i.dfy"

// what do we know between the start and end of the exception handler
// (after evalExceptionTaken, until the continuation)?
predicate KomExceptionHandlerInvariant(s:state, sd:PageDb, r:state, dp:PageNr, steps:nat)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires validPageDb(sd) && pageDbCorresponds(s.m, sd)
    requires nonStoppedDispatcher(sd, dp)
    requires steps > 0 <==> isReturningSvc(s)
{
    reveal_ValidRegState();
    var d' := updateUserPagesFromState(s, sd, dp);
    assert nonStoppedDispatcher(d', dp) by { reveal_updateUserPagesFromState(); }
    var rd := if steps == 0 then exceptionHandled(s, d', dp).2 else d';
    validExceptionTransition(s, d', r, rd, dp)
    && SaneState(r)
    && StackPreserving(s, r)
    && (forall a:addr | ValidMem(a) && !(StackLimit() <= a < StackBase()) &&
        !addrInPage(a, dp) :: MemContents(s.m, a) == MemContents(r.m, a))
    && GlobalsInvariant(s, r)
    && pageDbCorresponds(r.m, rd)
    && (if steps == 0 then (r.regs[R0], r.regs[R1], rd) == exceptionHandled(s, d', dp)
    else var lr := OperandContents(s, OLR);
    var retRegs := svcHandled(s, d', dp);
            preEntryReturn(r, lr, retRegs))
}

predicate {:opaque} AUCIdef()
    requires SaneConstants()
{
    reveal_ValidRegState();
    forall s:state, r:state, sd: PageDb, dp:PageNr
        | ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
            && validPageDb(sd) && pageDbCorresponds(s.m, sd)
            && nonStoppedDispatcher(sd, dp)
        :: ApplicationUsermodeContinuationInvariant(s, r)
        ==> exists steps:nat :: (steps > 0 <==> isReturningSvc(s))
            && KomExceptionHandlerInvariant(s, sd, r, dp, steps)
}

lemma lemma_AUCIdef(s:state, r:state, d:PageDb, dp:PageNr) returns (steps:nat)
    requires SaneConstants() && AUCIdef()
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
        && validPageDb(d) && pageDbCorresponds(s.m, d)
        && nonStoppedDispatcher(d, dp)
    requires ApplicationUsermodeContinuationInvariant(s, r)
    ensures steps > 0 <==> isReturningSvc(s)
    ensures KomExceptionHandlerInvariant(s, d, r, dp, steps)
{
    reveal_AUCIdef();
    steps :| steps > 0 <==> isReturningSvc(s);
}

lemma exceptionHandledValidPageDb(us:state, ex:exception, s:state, d:PageDb, dispPg:PageNr)
    requires ValidState(us) && mode_of_state(us) == User
    requires evalExceptionTaken(us, ex, s)
    requires validPageDb(d) && validDispatcherPage(d, dispPg)
    ensures validPageDb(lemma_evalExceptionTaken_NonUser(us, ex, s);exceptionHandled(s, d, dispPg).2)
{
    reveal_validPageDb();
    reveal_ValidSRegState();
    lemma_evalExceptionTaken_NonUser(us, ex, s);
    var (r0,r1,d') := exceptionHandled(s, d, dispPg);

    if (!(ex.ExSVC? || ex.ExAbt? || ex.ExUnd?)) {
        var dc := d'[dispPg].entry.ctxt;
        lemma_update_psr(us.sregs[cpsr], encode_mode(mode_of_exception(us.conf, ex)),
            ex == ExFIQ || mode_of_exception(us.conf, ex) == Monitor, true);
        assert mode_of_state(s) == mode_of_exception(us.conf, ex);
        assert dc.cpsr == s.sregs[spsr(mode_of_state(s))] == us.sregs[cpsr];
        assert us.conf.cpsr == decode_psr(us.sregs[cpsr]);
        assert us.conf.cpsr.m == User;
        assert decode_mode'(psr_mask_mode(dc.cpsr)) == Just(User);
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

lemma enterUserspacePreservesStuff(d:PageDb,s:state,s':state)
    requires SaneMem(s.m) && SaneMem(s'.m) && validPageDb(d)
        && ValidState(s) && ValidState(s')
    requires evalEnterUserspace(s, s')
    requires pageDbCorresponds(s.m, d)
    ensures AllMemInvariant(s,s')
    ensures pageDbCorresponds(s'.m, d)
{
    reveal_ValidMemState();
    reveal_pageDbEntryCorresponds();
    reveal_pageContentsCorresponds();
}

lemma nonWritablePagesAreSafeFromHavoc(m:addr,s:state,s':state)
    requires ValidState(s) && ValidState(s')
    requires evalUserspaceExecution(s, s')
    requires var pt := ExtractAbsPageTable(s);
        pt.Just? && var pages := WritablePagesInTable(fromJust(pt));
        BitwiseMaskHigh(m, 12) !in pages
    requires m in s.m.addresses
    ensures (reveal_ValidMemState();
        s'.m.addresses[m] == s.m.addresses[m])
{
    reveal_ValidMemState();
    reveal_ValidRegState();
    reveal_evalUserspaceExecution();
    var pt := ExtractAbsPageTable(s);
    assert pt.Just?;
    var pages := WritablePagesInTable(fromJust(pt));
    assert s'.m.addresses[m] == havocPages(pages, s.m.addresses, s'.m.addresses)[m];
    assert havocPages(pages, s.m.addresses, s'.m.addresses)[m] == s.m.addresses[m];
}

lemma onlyDataPagesAreWritable(p:PageNr,a:addr,d:PageDb,s:state,s':state,l1:PageNr)
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires ValidState(s) && ValidState(s') && evalUserspaceExecution(s,s')
    requires validPageDb(d)
    requires SaneMem(s.m) && pageDbCorresponds(s.m, d)
    requires WordAligned(a) && addrInPage(a, p)
    requires s.conf.ttbr0.ptbase == page_paddr(l1);
    requires nonStoppedL1(d, l1) && !pageSWrInAddrspace(d, l1, p)
    ensures var pt := ExtractAbsPageTable(s);
        pt.Just? && var pages := WritablePagesInTable(fromJust(pt));
        BitwiseMaskHigh(a, 12) !in pages
{
    reveal_validPageDb();

    var pt := ExtractAbsPageTable(s);
    assert pt.Just? by { reveal_evalUserspaceExecution(); }
    var pages := WritablePagesInTable(fromJust(pt));
    var vbase := s.conf.ttbr0.ptbase + PhysBase();
    var pagebase := BitwiseMaskHigh(a, 12);

    assert ExtractAbsL1PTable(s.m, vbase) == fromJust(pt);

    assert fromJust(pt) == mkAbsPTable(d, l1) by 
    {
        lemma_ptablesmatch(s.m, d, l1);    
    }
    assert WritablePagesInTable(fromJust(pt)) ==
        WritablePagesInTable(mkAbsPTable(d, l1));
    
    forall( a':addr, p':PageNr | 
        var pagebase' := BitwiseMaskHigh(a', 12);
        pagebase' in WritablePagesInTable(fromJust(pt)) &&
        addrInPage(a',p') )
        ensures d[p'].PageDbEntryTyped? && d[p'].entry.DataPage?
        ensures pageSWrInAddrspace(d, l1, p')
    {
        var pagebase' := BitwiseMaskHigh(a', 12);
        assert addrInPage(a', p') <==> addrInPage(pagebase', p') by {
            lemma_bitMaskAddrInPage(a', pagebase', p');
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
    reveal_validPageDb();
    reveal_pageDbEntryCorresponds();
    reveal_pageContentsCorresponds();
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
    requires nonStoppedDispatcher(d, dispPg)
    requires d' == updateUserPagesFromState(s, d, dispPg)
    ensures d'[p] == d[p] || (d[p].PageDbEntryTyped? && d[p].entry.DataPage? && d'[p] == updateUserPageFromState(s, d, p))
{ reveal_updateUserPagesFromState(); }

lemma lemma_contentsOfPage_corresponds(s:state, d:PageDb, p:PageNr)
    requires ValidState(s) && SaneMem(s.m) && validPageDb(d)
    requires d[p].PageDbEntryTyped? && d[p].entry.DataPage?
    requires d[p].entry.contents == contentsOfPage(s, p)
    ensures pageContentsCorresponds(p, d[p], extractPage(s.m, p))
{
    reveal_pageContentsCorresponds();
    reveal_pageDbDataCorresponds();
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

lemma userspaceExecutionUpdatesPageDb(d:PageDb, s:state, s':state, dispPg:PageNr)
    requires SaneMem(s.m) && SaneMem(s'.m) && validPageDb(d)
        && ValidState(s) && ValidState(s') && nonStoppedDispatcher(d, dispPg)
    requires evalUserspaceExecution(s, s')
    requires pageDbCorresponds(s.m,  d)
    requires s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(d, dispPg))
    ensures  pageDbCorresponds(s'.m, updateUserPagesFromState(s', d, dispPg))
{
    var d' := updateUserPagesFromState(s', d, dispPg);
    var l1 := l1pOfDispatcher(d, dispPg);
    assert nonStoppedL1(d, l1);

    forall ( p | validPageNr(p) )
        ensures pageDbEntryCorresponds(d'[p], extractPageDbEntry(s'.m, p))
    {
        PageDbCorrespondsImpliesEntryCorresponds(s.m, d, p);
        assert pageDbEntryCorresponds(d[p], extractPageDbEntry(s.m, p));
        userspaceExecutionPreservesPrivState(s, s');
        assert extractPageDbEntry(s.m, p) == extractPageDbEntry(s'.m, p);
        reveal_pageDbEntryCorresponds();
        lemma_updateUserPagesFromState(s', d, d', dispPg, p);
    }
    assert {:split_here} true;

    forall ( p | validPageNr(p) )
        ensures pageContentsCorresponds(p, d'[p], extractPage(s'.m, p));
    {
        if pageSWrInAddrspace(d, l1, p) {
            reveal_updateUserPagesFromState();
            lemma_contentsOfPage_corresponds(s', d', p);
        } else if d[p].PageDbEntryTyped? {
            assert d[p] == d'[p] by { reveal_updateUserPagesFromState(); }

            forall ( a:addr |
                    page_monvaddr(p) <= a < page_monvaddr(p) + PAGESIZE )
                ensures MemContents(s'.m, a) == MemContents(s.m, a)
            {
                var pt := ExtractAbsPageTable(s);
                lemma_ptablesmatch(s.m, d, l1);
                assert pt.Just?;
                var pages := WritablePagesInTable(fromJust(pt));

                onlyDataPagesAreWritable(p, a, d, s, s', l1);
                assert BitwiseMaskHigh(a, 12) !in pages;
                lemma_monvaddr_ValidMem(p, a);
                nonWritablePagesAreSafeFromHavoc(a, s, s');
            }
            lemma_ExtractSamePages(s.m, s'.m, p);
            reveal_pageContentsCorresponds();
        } else {
            assert d[p] == d'[p] by { reveal_updateUserPagesFromState(); }
            reveal_pageContentsCorresponds();
        }
    }
}

lemma userspaceExecutionPreservesStack(d:PageDb,s:state,s':state, l1:PageNr)
    requires SaneMem(s.m) && SaneMem(s'.m) && validPageDb(d)
        && ValidState(s) && ValidState(s')
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires evalUserspaceExecution(s,s')
    requires pageDbCorresponds(s.m,  d)
    requires s.conf.ttbr0.ptbase == page_paddr(l1);
    requires nonStoppedL1(d, l1);
    ensures forall a:addr | StackLimit() <= a < StackBase() ::
        MemContents(s.m, a) == MemContents(s'.m, a)
{
    assert StackBase() <= PhysBase();
    reveal_evalUserspaceExecution();
    var pt := ExtractAbsPageTable(s);
    assert pt.Just?;
    var pages := WritablePagesInTable(fromJust(pt));
    forall (a | ValidMem(a) && a < PhysBase())
        ensures MemContents(s.m, a) == MemContents(s'.m, a)
    {
        assert BitwiseMaskHigh(a, 12) !in pages;
        nonWritablePagesAreSafeFromHavoc(a, s, s');
    }
}

lemma userspaceExecutionPreservesPrivState(s:state,s':state)
    requires ValidState(s) && ValidState(s')
    requires evalUserspaceExecution(s,s')
    ensures GlobalsInvariant(s,s')
    ensures (reveal_ValidRegState(); s.regs[SP(Monitor)] == s'.regs[SP(Monitor)])
{
    reveal_evalUserspaceExecution();
}

lemma exceptionTakenPreservesStuff(d:PageDb,s:state,ex:exception,s':state)
    requires SaneMem(s.m) && SaneMem(s'.m) && validPageDb(d)
        && ValidState(s) && ValidState(s')
    requires evalExceptionTaken(s, ex, s')
    requires pageDbCorresponds(s.m, d)
    ensures AllMemInvariant(s,s')
    ensures mode_of_state(s') != User
    ensures (reveal_ValidRegState(); s.regs[SP(Monitor)] == s'.regs[SP(Monitor)])
    ensures pageDbCorresponds(s'.m, d)
{
    reveal_ValidMemState();
    reveal_pageDbEntryCorresponds();
    reveal_pageContentsCorresponds();
    lemma_evalExceptionTaken_NonUser(s, ex, s');
}

lemma lemma_evalMOVSPCLRUC(s:state, r:state, d:PageDb, dp:PageNr)
    requires SaneState(s)
    requires validPageDb(d) && pageDbCorresponds(s.m, d) && nonStoppedDispatcher(d, dp)
    requires s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(d, dp))
    requires evalMOVSPCLRUC(s, r)
    requires AUCIdef()
    ensures SaneState(r)
    ensures OperandContents(r, OSP) == OperandContents(s, OSP)
    ensures StackPreserving(s, r)
    ensures GlobalsInvariant(s, r)
{
    // XXX: prove some obvious things about OSP early
    // before the reveal, to stop Z3 getting lost
    assert ValidAnySrcOperand(s, OSP) && ValidAnySrcOperand(r, OSP) by {
        assert ValidOperand(OSP);
    }
    assert OperandContents(s, OSP) == s.regs[SP(Monitor)];
    assert ValidMemRange(StackLimit(), StackBase());

    reveal_evalMOVSPCLRUC();
    var s2, s3, ex, s4 :| 
        evalEnterUserspace(s, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && ApplicationUsermodeContinuationInvariant(s4, r);

    enterUserspacePreservesStuff(d, s,  s2);
    userspaceExecutionPreservesPrivState(s2, s3);
    userspaceExecutionUpdatesPageDb(d, s2, s3, dp);
    var d' := updateUserPagesFromState(s3, d, dp);
    assert nonStoppedDispatcher(d', dp) by { reveal_updateUserPagesFromState(); }
    exceptionTakenPreservesStuff(d', s3, ex, s4);
    var steps := lemma_AUCIdef(s4, r, d', dp);

    calc {
        OperandContents(s, OSP);
        s.regs[SP(Monitor)];
        s2.regs[SP(Monitor)];
        s3.regs[SP(Monitor)];
        s4.regs[SP(Monitor)];
        r.regs[SP(Monitor)];
        OperandContents(r, OSP);
    }

    assert StackPreserving(s, r) by {
        assert AllMemInvariant(s, s2);
        userspaceExecutionPreservesStack(d, s2, s3, l1pOfDispatcher(d, dp));
        assert AllMemInvariant(s3, s4);
        assert StackPreserving(s4, r);
    }
}

lemma lemma_validEnclaveExecution(s1:state, sd:PageDb, r:state, dispPg:PageNr)
    returns (exs:state, rd:PageDb, steps:nat)
    requires SaneState(s1)
    requires validPageDb(sd) && pageDbCorresponds(s1.m, sd)
    requires nonStoppedDispatcher(sd, dispPg)
    requires evalMOVSPCLRUC(s1, r)
    requires AUCIdef()
    ensures ValidState(exs) && mode_of_state(exs) != User
    ensures (reveal_ValidRegState();
        (r.regs[R0], r.regs[R1], rd) == exceptionHandled(exs, sd, dispPg))
    ensures validPageDb(rd) && SaneMem(r.m) && pageDbCorresponds(r.m, rd)
    ensures validEnclaveExecution(s1, sd, r, rd, dispPg, steps)
{
    assume false;
    assert nonStoppedDispatcher(sd, dispPg);
    var l1p := l1pOfDispatcher(sd, dispPg);

    reveal_evalMOVSPCLRUC();
    var s2, s3, ex, s4 :| 
        evalEnterUserspace(s1, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && ApplicationUsermodeContinuationInvariant(s4, r);

    assert entryTransition(s1, s2);
    lemma_evalExceptionTaken_NonUser(s3, ex, s4);
    assert userspaceExecutionAndException(s2, s4)
        by { reveal_evalUserspaceExecution(); }

    enterUserspacePreservesStuff(sd, s1,  s2);
    userspaceExecutionPreservesPrivState(s2, s3);
    userspaceExecutionUpdatesPageDb(sd, s2, s3, dispPg);
    exceptionTakenPreservesStuff(sd, s3, ex, s4);
    steps := lemma_AUCIdef(s4, r, sd, dispPg);

    exs := s4;
    rd := exceptionHandled(exs, sd, dispPg).2;
    exceptionHandledValidPageDb(s3, ex, s4, sd, dispPg);

    assert validExceptionTransition(s4, sd, r, rd, dispPg);
    assert (reveal_ValidRegState();
        (r.regs[R0], r.regs[R1], rd) == exceptionHandled(exs, sd, dispPg));

    reveal_validEnclaveExecution();
}
/*
lemma lemma_validEnter(s0:state, s1:state, r:state, sd:PageDb,
                       dp:word, a1:word, a2:word, a3:word)
    returns (exs:state, rd:PageDb)
    requires SaneState(s0) && SaneState(s1)
    requires validPageDb(sd) && pageDbCorresponds(s0.m, sd) && pageDbCorresponds(s1.m, sd)
    requires smc_enter_err(sd, dp, false) == KOM_ERR_SUCCESS
    requires preEntryEnter(s0, s1, sd, dp, a1, a2, a3)
    requires evalMOVSPCLRUC(s1, r)
    requires AUCIdef()
    ensures ValidState(exs) && mode_of_state(exs) != User
    ensures (reveal_ValidRegState();
        (r.regs[R0], r.regs[R1], rd) == exceptionHandled(exs, sd, dp))
    ensures validPageDb(rd) && SaneMem(r.m) && pageDbCorresponds(r.m, rd)
    ensures validEnter(SysState(s0, sd), SysState(r, rd), dp, a1, a2, a3)
{
    assert nonStoppedDispatcher(sd, dp);
    var l1p := l1pOfDispatcher(sd, dp);

    reveal_evalMOVSPCLRUC();
    var s2, s3, ex, s4 :| 
        evalEnterUserspace(s1, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && ApplicationUsermodeContinuationInvariant(s4, r);

    assert entryTransition(s1, s2);
    lemma_evalExceptionTaken_NonUser(s3, ex, s4);
    assert userspaceExecutionAndException(s2, s4)
        by { reveal_evalUserspaceExecution(); }

    enterUserspacePreservesStuff(sd, s1,  s2);
    userspaceExecutionPreservesPrivState(s2, s3);
    userspaceExecutionPreservesPageDb(sd, s2, s3, l1p);
    exceptionTakenPreservesStuff(sd, s3, ex, s4);
    lemma_AUCIdef(s4, r, sd, dp);

    exs := s4;
    rd := exceptionHandled(exs, sd, dp).2;
    exceptionHandledValidPageDb(s3, ex, s4, sd, dp);

    assert validExceptionTransition(s4, sd, r, rd, dp);
    assert (reveal_ValidRegState();
        (r.regs[R0], r.regs[R1], rd) == exceptionHandled(exs, sd, dp));

    reveal_validEnter();
}

lemma lemma_validResume(s0:state, s1:state, r:state, sd:PageDb, dp:word)
    returns (exs:state, rd:PageDb)
    requires SaneState(s0) && SaneState(s1)
    requires validPageDb(sd) && pageDbCorresponds(s0.m, sd) && pageDbCorresponds(s1.m, sd)
    requires smc_enter_err(sd, dp, true) == KOM_ERR_SUCCESS
    requires preEntryResume(s0, s1, sd, dp)
    requires evalMOVSPCLRUC(s1, r)
    requires AUCIdef()
    ensures ValidState(exs) && mode_of_state(exs) != User
    ensures (reveal_ValidRegState();
        (r.regs[R0], r.regs[R1], rd) == exceptionHandled(exs, sd, dp))
    ensures validPageDb(rd) && SaneMem(r.m) && pageDbCorresponds(r.m, rd)
    ensures validResume(SysState(s0, sd), SysState(r, rd), dp)
{
    assert nonStoppedDispatcher(sd, dp);
    var l1p := l1pOfDispatcher(sd, dp);

    reveal_evalMOVSPCLRUC();
    var s2, s3, ex, s4 :|
        evalEnterUserspace(s1, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && ApplicationUsermodeContinuationInvariant(s4, r);

    assert entryTransition(s1, s2);
    lemma_evalExceptionTaken_NonUser(s3, ex, s4);
    assert userspaceExecutionAndException(s2, s4)
        by { reveal_evalUserspaceExecution(); }

    enterUserspacePreservesStuff(sd, s1,  s2);
    userspaceExecutionPreservesPrivState(s2, s3);
    userspaceExecutionPreservesPageDb(sd, s2, s3, l1p);
    exceptionTakenPreservesStuff(sd, s3, ex, s4);
    lemma_AUCIdef(s4, r, sd, dp);

    exs := s4;
    rd := exceptionHandled(exs, sd, dp).2;
    exceptionHandledValidPageDb(s3, ex, s4, sd, dp);

    assert validExceptionTransition(s4, sd, r, rd, dp);
    assert (reveal_ValidRegState();
        (r.regs[R0], r.regs[R1], rd) == exceptionHandled(exs, sd, dp));

    reveal_validResume();
}

lemma lemma_ValidEntryPre(s0:state, s1:state, sd:PageDb, r:state, rd:PageDb, dp:word,
                           a1:word, a2:word, a3:word)
    requires ValidState(s0) && ValidState(s1) && ValidState(r) && validPageDb(sd)
    ensures smc_enter(s1, sd, r, rd, dp, a1, a2, a3)
        ==> smc_enter(s0, sd, r, rd, dp, a1, a2, a3)
    ensures smc_resume(s1, sd, r, rd, dp) ==> smc_resume(s0, sd, r, rd, dp)
{
    reveal_validEnter();
    reveal_validResume();
}
*/
lemma lemma_evalExceptionTaken_Mode(s:state, e:exception, r:state)
    requires ValidState(s) && evalExceptionTaken(s, e, r)
    ensures mode_of_state(r) == mode_of_exception(s.conf, e)
{
    var newmode := mode_of_exception(s.conf, e);
    assert newmode != User;
    var f := e == ExFIQ || newmode == Monitor;
    reveal_ValidSRegState();
    
    calc {
        mode_of_state(r);
        decode_psr(psr_of_exception(s, e)).m;
        { lemma_update_psr(s.sregs[cpsr], encode_mode(newmode), f, true); }
        decode_mode(encode_mode(newmode));
        { mode_encodings_are_sane(); }
        newmode;
    }
}

lemma lemma_evalExceptionTaken_NonUser(s:state, e:exception, r:state)
    requires ValidState(s) && evalExceptionTaken(s, e, r)
    ensures mode_of_state(r) != User
{
    lemma_evalExceptionTaken_Mode(s, e, r);
}
/*
lemma lemma_validEnterPost(s:state, sd:PageDb, r1:state, rd:PageDb, r2:state, dp:word,
                           a1:word, a2:word, a3:word)
    requires ValidState(s) && ValidState(r1) && ValidState(r2) && validPageDb(sd)
    requires smc_enter_err(sd, dp, false) == KOM_ERR_SUCCESS
    requires validEnter(SysState(s, sd), SysState(r1, rd), dp, a1, a2, a3)
    requires validExceptionTransition(r1, rd, r2, rd, dp)
    requires OperandContents(r1, OReg(R0)) == OperandContents(r2, OReg(R0))
    requires OperandContents(r1, OReg(R1)) == OperandContents(r2, OReg(R1))
    ensures validEnter(s, sd, r2, rd, dp, a1, a2, a3)
{
    reveal_validEnter();
    reveal_ValidRegState();

    var s1, s2, s4 :|
        preEntryEnter(s, s1, sd, dp, a1, a2, a3)
        && entryTransition(s1, s2)
        && userspaceExecutionAndException(s2, s4)
        && validExceptionTransition(s4, sd, r1, rd, dp)
        && (r1.regs[R0], r1.regs[R1], rd) == exceptionHandled(s4, sd, dp);

    assert validExceptionTransition(s4, sd, r2, rd, dp)
        by { reveal_validExceptionTransition(); }
    assert (r2.regs[R0], r2.regs[R1], rd) == exceptionHandled(s4, sd, dp);
}

lemma lemma_validResumePost(s:state, sd:PageDb, r1:state, rd:PageDb, r2:state, dp:word)
    requires ValidState(s) && ValidState(r1) && ValidState(r2) && validPageDb(sd)
    requires smc_enter_err(sd, dp, true) == KOM_ERR_SUCCESS
    requires validResume(SysState(s, sd), SysState(r1, rd), dp)
    requires validExceptionTransition(r1, rd, r2, rd, dp)
    requires OperandContents(r1, OReg(R0)) == OperandContents(r2, OReg(R0))
    requires OperandContents(r1, OReg(R1)) == OperandContents(r2, OReg(R1))
    ensures validResume(SysState(s, sd), SysState(r2, rd), dp)
{
    reveal_validResume();
    reveal_ValidRegState();

    var s1, s2, s4 :|
        preEntryResume(s, s1, sd, dp)
        && entryTransition(s1, s2)
        && userspaceExecutionAndException(s2, s4)
        && validExceptionTransition(s4, sd, r1, rd, dp)
        && (r1.regs[R0], r1.regs[R1], rd) == exceptionHandled(s4, sd, dp);

    assert validDispatcherPage(sd, dp);
    assert validExceptionTransition(s4, sd, r2, rd, dp)
        by { reveal_validExceptionTransition(); }
    assert (r2.regs[R0], r2.regs[R1], rd) == exceptionHandled(s4, sd, dp);
}
*/
function exPageDb(t: (int, int, PageDb)): PageDb { t.2 }
