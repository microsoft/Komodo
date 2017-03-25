include "entry.s.dfy"
include "ptables.i.dfy"
include "psrbits.i.dfy"

// SaneState, but not SaneStack
predicate SaneStateAfterException(s:state)
{
    SaneConstants()
    && ValidState(s) && s.ok
    && SaneMem(s.m)
    && mode_of_state(s) == Monitor
}

// what do we know between the start and end of the exception handler
// (after evalExceptionTaken, until the continuation)?
predicate KomExceptionHandlerInvariant(s:state, sd:PageDb, r:state, dp:PageNr)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires validPageDb(sd) && pageDbCorresponds(s.m, sd)
    requires nonStoppedDispatcher(sd, dp)
{
    reveal_ValidRegState();
    var retToEnclave := isReturningSvc(s);
    var rd := if retToEnclave then sd else exceptionHandled(s, sd, dp).2;
    validExceptionTransition(s, sd, r, rd, dp)
    // sp unaltered except it may have the low bit set to signify !retToEnclave
    && var ssp, rsp := s.regs[SP(Monitor)], r.regs[SP(Monitor)];
    SaneStateAfterException(r)
    && SaneStackPointer(ssp)
    && ParentStackPreserving(s, r)
    && s.conf.ttbr0 == r.conf.ttbr0 && s.conf.scr == r.conf.scr
    && (forall a:addr | ValidMem(a) && !(StackLimit() <= a < StackBase()) &&
        !addrInPage(a, dp) :: MemContents(s.m, a) == MemContents(r.m, a))
    && GlobalsInvariant(s, r)
    && pageDbCorresponds(r.m, rd)
    && (if retToEnclave
       then rsp == ssp
        && preEntryReturn(r, OperandContents(s, OLR), svcHandled(s, sd, dp))
       else rsp == BitwiseOr(ssp, 1)
        && (r.regs[R0], r.regs[R1], rd) == exceptionHandled(s, sd, dp))
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
        ==> KomExceptionHandlerInvariant(s, sd, r, dp)
}

lemma lemma_AUCIdef(s:state, r:state, d:PageDb, dp:PageNr)
    requires SaneConstants() && AUCIdef()
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
        && validPageDb(d) && pageDbCorresponds(s.m, d)
        && nonStoppedDispatcher(d, dp)
    requires ApplicationUsermodeContinuationInvariant(s, r)
    ensures KomExceptionHandlerInvariant(s, d, r, dp)
{
    reveal_AUCIdef();
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

lemma lemma_sp_alignment(x:word)
    requires x % 2 == 0
    ensures x != BitwiseOr(x, 1)
{
    assert BitsAsWord(1) == 1 && BitsAsWord(2) == 2 by { reveal_BitsAsWord(); }
    lemma_BitsAndWordConversions();

    assert BitMod(WordAsBits(x), 2) == 0 by { lemma_BitModEquiv(x, 2); }
    assert x != BitwiseOr(x, 1) by { reveal_BitOr(); reveal_BitMod(); }
}

lemma lemma_evalMOVSPCLRUC_inner(s:state, r:state, d:PageDb, dp:PageNr)
        returns (s2:state, s3:state, ex:exception, s4:state, d4:PageDb)
    requires SaneState(s)
    requires validPageDb(d) && pageDbCorresponds(s.m, d) && nonStoppedDispatcher(d, dp)
    requires s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(d, dp))
    requires evalMOVSPCLRUC(s, r)
    requires AUCIdef()
    ensures SaneStateAfterException(r)
    ensures OperandContents(r, OSP) == OperandContents(s, OSP)
        || OperandContents(r, OSP) == BitwiseOr(OperandContents(s, OSP), 1)
    ensures OperandContents(s, OSP) != BitwiseOr(OperandContents(s, OSP), 1)
    ensures ParentStackPreserving(s, r)
    ensures GlobalsInvariant(s, r)
    ensures evalEnterUserspace(s, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
    ensures mode_of_state(s4) != User && SaneMem(s4.m)
    ensures d4 == updateUserPagesFromState(s3, d, dp) && pageDbCorresponds(s4.m, d4)
    ensures KomExceptionHandlerInvariant(s4, d4, r, dp)
    ensures s.conf.ttbr0 == r.conf.ttbr0
{
    // XXX: prove some obvious things about OSP early
    // before the reveal, to stop Z3 getting lost
    assert ValidAnySrcOperand(s, OSP) && ValidAnySrcOperand(r, OSP) by {
        assert ValidOperand(OSP);
    }
    assert OperandContents(s, OSP) == s.regs[SP(Monitor)];
    assert ValidMemRange(StackLimit(), StackBase());

    reveal_evalMOVSPCLRUC();
    s2, s3, ex, s4 :| 
        evalEnterUserspace(s, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && ApplicationUsermodeContinuationInvariant(s4, r);

    enterUserspacePreservesStuff(d, s, s2);
    userspaceExecutionPreservesPrivState(s2, s3);
    userspaceExecutionUpdatesPageDb(d, s2, s3, dp);
    d4 := updateUserPagesFromState(s3, d, dp);
    exceptionTakenPreservesStuff(d4, s3, ex, s4);
    lemma_AUCIdef(s4, r, d4, dp);

    calc {
        OperandContents(s, OSP);
        s.regs[SP(Monitor)];
        s2.regs[SP(Monitor)];
        s3.regs[SP(Monitor)];
        s4.regs[SP(Monitor)];
    }

    lemma_sp_alignment(OperandContents(s, OSP));

    assert s4.regs[SP(Monitor)] == OperandContents(r, OSP)
        || BitwiseOr(s4.regs[SP(Monitor)], 1) == OperandContents(r, OSP);

    assert ParentStackPreserving(s, r) by {
        assert AllMemInvariant(s, s2);
        userspaceExecutionPreservesStack(d, s2, s3, l1pOfDispatcher(d, dp));
        assert AllMemInvariant(s3, s4);
        assert ParentStackPreserving(s4, r);
    }

    calc {
        s.conf.ttbr0;
        s2.conf.ttbr0;
        { reveal_evalUserspaceExecution(); }
        s3.conf.ttbr0;
        s4.conf.ttbr0;
        r.conf.ttbr0;
    }
/*
    assert spsr_of_state(r).m == User by {
        assert mode_of_state(s3) == User;
        lemma_evalExceptionTaken_Mode(s3, ex, s4);
        calc {
            s3.conf.cpsr;
            spsr_of_state(s4);
            spsr_of_state(r);
        }
    }
*/
}

lemma lemma_evalMOVSPCLRUC(s:state, sd:PageDb, r:state, dispPg:PageNr)
    returns (rd:PageDb, retToEnclave:bool)
    requires SaneState(s)
    requires validPageDb(sd) && pageDbCorresponds(s.m, sd)
    requires nonStoppedDispatcher(sd, dispPg)
    requires s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(sd, dispPg))
    requires evalMOVSPCLRUC(s, r)
    requires AUCIdef()
    ensures SaneStateAfterException(r)
    ensures ParentStackPreserving(s, r)
    ensures GlobalsInvariant(s, r)
    ensures OperandContents(s, OSP) != BitwiseOr(OperandContents(s, OSP), 1)
            && if retToEnclave
            then OperandContents(r, OSP) == OperandContents(s, OSP)
            else OperandContents(r, OSP) == BitwiseOr(OperandContents(s, OSP), 1)
    ensures s.conf.ttbr0 == r.conf.ttbr0
    ensures validPageDb(rd) && SaneMem(r.m) && pageDbCorresponds(r.m, rd)
    ensures validEnclaveExecutionStep(s, sd, r, rd, dispPg, retToEnclave)
    ensures retToEnclave ==> spsr_of_state(r).m == User
{
    var s2, s3, ex, s4, d4 := lemma_evalMOVSPCLRUC_inner(s, r, sd, dispPg);

    assert entryTransition(s, s2);
    enterUserspacePreservesStuff(sd, s, s2);
    assert userspaceExecutionAndException(s2, s3, s4)
        by { reveal_evalUserspaceExecution(); }
    userspaceExecutionPreservesPrivState(s2, s3);
    userspaceExecutionUpdatesPageDb(sd, s2, s3, dispPg);

    var ssp, rsp := OperandContents(s, OSP), OperandContents(r, OSP);
    assert rsp == r.regs[SP(Monitor)];

    retToEnclave := isReturningSvc(s4);

    if retToEnclave {
        assert ssp == rsp;
        rd := d4;
        assert spsr_of_state(r).m == User by {
            assert preEntryReturn(r, OperandContents(s4, OLR), svcHandled(s4, d4, dispPg));
            assert (reveal_ValidSRegState();
                        r.sregs[spsr(mode_of_state(r))] == encode_mode(User));
            assert decode_mode(psr_mask_mode(encode_mode(User))) == User by {
                assert WordAsBits(0x10) == 0x10 && WordAsBits(0x1f) == 0x1f
                    by { reveal_WordAsBits(); }
                lemma_BitsAndWordConversions();
                reveal_BitAnd();
            }
        }
    } else {
        assert rsp == BitwiseOr(ssp, 1);
        assert ssp != rsp;
        rd := exceptionHandled(s4, d4, dispPg).2;
        exceptionHandledValidPageDb(s3, ex, s4, d4, dispPg);
    }

    assert validEnclaveExecutionStep(s, sd, r, rd, dispPg, retToEnclave) by {
        reveal_validEnclaveExecutionStep();
        assert validEnclaveExecutionStep'(s, sd, s2, s3, s4, d4, r, rd,
                                          dispPg, retToEnclave);
    }
}

lemma lemma_ValidEntryPre(s0:state, s1:state, sd:PageDb, r:state, rd:PageDb, dp:word,
                           a1:word, a2:word, a3:word)
    requires ValidState(s0) && ValidState(s1) && ValidState(r) && validPageDb(sd)
    requires SaneConstants()
    ensures smc_enter(s1, sd, r, rd, dp, a1, a2, a3)
        ==> smc_enter(s0, sd, r, rd, dp, a1, a2, a3)
    ensures smc_resume(s1, sd, r, rd, dp) ==> smc_resume(s0, sd, r, rd, dp)
{
}

lemma lemma_evalExceptionTaken_Mode(s:state, e:exception, r:state)
    requires ValidState(s) && evalExceptionTaken(s, e, r)
    ensures mode_of_state(r) == mode_of_exception(s.conf, e)
    ensures spsr_of_state(r) == s.conf.cpsr
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

lemma lemma_validEnclaveExecutionStep_PageDb(s1:state, d1:PageDb, r1:state,
    rd:PageDb, dispPg:PageNr, retToEnclave:bool)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires nonStoppedDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s1, d1, r1, rd, dispPg, retToEnclave)
    ensures validPageDb(rd) && nonStoppedDispatcher(rd, dispPg)
    ensures l1pOfDispatcher(d1, dispPg) == l1pOfDispatcher(rd, dispPg)
{
    reveal_validEnclaveExecutionStep();
    reveal_updateUserPagesFromState();
    reveal_validExceptionTransition();
}

lemma lemma_validEnclaveExecutionStepPost(s1:state, d1:PageDb, r1:state,
                            rd:PageDb, r2:state, dispPg:PageNr)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires nonStoppedDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s1, d1, r1, rd, dispPg, false)
    requires validExceptionTransition(r1, rd, r2, rd, dispPg)
    requires OperandContents(r1, OReg(R0)) == OperandContents(r2, OReg(R0))
    requires OperandContents(r1, OReg(R1)) == OperandContents(r2, OReg(R1))
    ensures validEnclaveExecutionStep(s1, d1, r2, rd, dispPg, false)
{
    reveal_validEnclaveExecutionStep();
    reveal_updateUserPagesFromState();
    reveal_ValidRegState();

    var s2, s3, s4, d4 :|
        validEnclaveExecutionStep'(s1, d1, s2, s3, s4, d4, r1, rd, dispPg, false);

    assert validExceptionTransition(s4, d4, r2, rd, dispPg)
        by { reveal_validExceptionTransition(); }
    assert (r2.regs[R0], r2.regs[R1], rd) == exceptionHandled(s4, d4, dispPg);
    assert validEnclaveExecutionStep'(s1, d1, s2, s3, s4, d4, r2, rd, dispPg, false);
}

lemma lemma_validEnclaveExecutionStepPrePost(s0:state, s1:state, d1:PageDb, r1:state,
                            rd:PageDb, r2:state, dispPg:PageNr, retToEnclave:bool)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires nonStoppedDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s1, d1, r1, rd, dispPg, retToEnclave)
    requires equivStates(s0, s1) && equivStates(r1, r2)
    ensures validEnclaveExecutionStep(s0, d1, r1, rd, dispPg, retToEnclave)
{
    reveal_validEnclaveExecutionStep();
    reveal_updateUserPagesFromState();
    reveal_ValidRegState();
    var s2, s3, s4, d4 :|
        validEnclaveExecutionStep'(s1, d1, s2, s3, s4, d4, r1, rd, dispPg,
                                     retToEnclave);

    assert entryTransition(s0, s2);
    assert validEnclaveExecutionStep'(s0, d1, s2, s3, s4, d4, r1, rd, dispPg,
                                     retToEnclave);
    assert validExceptionTransition(s4, d4, r2, rd, dispPg)
        by { reveal_validExceptionTransition(); }
    assert r1.regs == r2.regs;
}

lemma lemma_validEnclaveExecutionPost(s1:state, d1:PageDb, r1:state, rd:PageDb,
                                      r2:state, dispPg:PageNr, steps:nat)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires nonStoppedDispatcher(d1, dispPg)
    requires validEnclaveExecution(s1, d1, r1, rd, dispPg, steps)
    requires validExceptionTransition(r1, rd, r2, rd, dispPg)
    requires OperandContents(r1, OReg(R0)) == OperandContents(r2, OReg(R0))
    requires OperandContents(r1, OReg(R1)) == OperandContents(r2, OReg(R1))
    ensures validEnclaveExecution(s1, d1, r2, rd, dispPg, steps)
    decreases steps
{
    reveal_validEnclaveExecution();

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

lemma lemma_singlestep_execution(s1:state, d1:PageDb,
    rs:state, rd:PageDb, dispPg:PageNr)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires nonStoppedDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s1, d1, rs, rd, dispPg, false)
    ensures validEnclaveExecution(s1, d1, rs, rd, dispPg, 0)
{
    reveal_validEnclaveExecution();
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
                && nonStoppedDispatcher(l[i].1, dispPg))
    && (forall i {:trigger l[i]} | 0 < i <= steps ::
            validEnclaveExecutionStep(l[i-1].0, l[i-1].1, l[i].0, l[i].1, dispPg, true))
}

lemma lemma_partialEnclaveExecution_append(l:seq<(state, PageDb)>, s:state, d:PageDb, dispPg:PageNr, steps:nat)
    requires SaneConstants()
    requires ValidState(s) && validPageDb(d) && nonStoppedDispatcher(d, dispPg)
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
    requires ValidState(s0) && validPageDb(d0) && nonStoppedDispatcher(d0, dispPg)
    requires ValidState(s1) && validPageDb(d1) && nonStoppedDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s0, d0, s1, d1, dispPg, true)
    requires validEnclaveExecution(s1, d1, rs, rd, dispPg, steps - 1)
    ensures  validEnclaveExecution(s0, d0, rs, rd, dispPg, steps)
{
    reveal_validEnclaveExecution();
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
