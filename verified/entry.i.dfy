include "entry.s.dfy"
include "ptables.i.dfy"

predicate validSysState'(s:SysState)
{
    validSysState(s) && SaneMem(s.hw.m) && pageDbCorresponds(s.hw.m, s.d)
}

predicate KomExceptionHandlerInvariant(s:state, sd:PageDb, r:state, dp:PageNr)
    requires ValidState(s) && mode_of_state(s) != User && SaneMem(s.m)
    requires validPageDb(sd) && pageDbCorresponds(s.m, sd) && validDispatcherPage(sd, dp)
{
    reveal_ValidRegState();
    var rd := exceptionHandled(s, sd, dp).2;
    validExceptionTransition(SysState(s, sd), SysState(r, rd), dp)
    && SaneState(r)
    && StackPreserving(s, r)
    && (forall a:addr | ValidMem(a) && !(StackLimit() <= a < StackBase()) &&
        !addrInPage(a, dp) :: MemContents(s.m, a) == MemContents(r.m, a))
    && GlobalsInvariant(s, r)
    && pageDbCorresponds(r.m, rd)
    && (r.regs[R0], r.regs[R1], rd) == exceptionHandled(s, sd, dp)
}

predicate {:opaque} AUCIdef()
    requires SaneConstants()
{
    reveal_ValidRegState();
    forall s:state, r:state, sd: PageDb, dp:PageNr
        | ValidState(s) && mode_of_state(s) != User && SaneMem(s.m) && validPageDb(sd)
            && pageDbCorresponds(s.m, sd) && validDispatcherPage(sd, dp)
        :: ApplicationUsermodeContinuationInvariant(s, r)
        ==> KomExceptionHandlerInvariant(s, sd, r, dp)
}

function exceptionHandled_premium(us:state, ex:exception, s:state, d:PageDb, dispPg:PageNr) : (int, int, PageDb)
    requires ValidState(us) && mode_of_state(us) == User
    requires evalExceptionTaken(us, ex, s)
    requires validPageDb(d) && validDispatcherPage(d, dispPg)
    ensures var (r0,r1,d) := exceptionHandled_premium(us, ex, s, d, dispPg);
        validPageDb(d)
{
    exceptionHandledValidPageDb(us, ex, s, d, dispPg);
    exceptionHandled(s, d, dispPg)
}

lemma exceptionHandledValidPageDb(us:state, ex:exception, s:state, d:PageDb, dispPg:PageNr)
    requires ValidState(us) && mode_of_state(us) == User
    requires evalExceptionTaken(us, ex, s)
    requires validPageDb(d) && validDispatcherPage(d, dispPg)
    ensures validPageDb(exceptionHandled(s, d, dispPg).2)
{
    reveal_validPageDb();
    reveal_ValidSRegState();
    reveal_ValidRegState();
    var (r0,r1,d') := exceptionHandled(s, d, dispPg);

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
    var pt := ExtractAbsPageTable(s);
    assert pt.Just?;
    var pages := WritablePagesInTable(fromJust(pt));
    assert s'.m.addresses[m] == havocPages(pages, s.m.addresses, s'.m.addresses)[m];
    assert havocPages(pages, s.m.addresses, s'.m.addresses)[m] == s.m.addresses[m];
}

lemma onlyDataPagesAreWritable(p:PageNr,a:addr,d:PageDb,s:state, s':state,
    l1:PageNr)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires ValidState(s) && ValidState(s') && evalUserspaceExecution(s,s')
    requires validPageDb(d) && d[p].PageDbEntryTyped? && !d[p].entry.DataPage?
    requires SaneMem(s.m) && pageDbCorresponds(s.m, d);
    requires WordAligned(a)
    requires addrInPage(a, p)
    requires s.conf.ttbr0.ptbase == page_paddr(l1);
    requires nonStoppedL1(d, l1);
    ensures var pt := ExtractAbsPageTable(s);
        pt.Just? && var pages := WritablePagesInTable(fromJust(pt));
        BitwiseMaskHigh(a, 12) !in pages
{
    reveal_validPageDb();

    var pt := ExtractAbsPageTable(s);
    assert pt.Just?;
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
    {
        var pagebase' := BitwiseMaskHigh(a', 12);
        assert addrInPage(a', p') <==> addrInPage(pagebase', p') by {
            lemma_bitMaskAddrInPage(a', pagebase', p');
        }
        lemma_writablePagesAreDataPages(p', pagebase', d, l1);
    }
}

lemma lemma_writablePagesAreDataPages(p:PageNr,a:addr,d:PageDb,l1p:PageNr)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()   
    requires validPageDb(d)     
    requires nonStoppedL1(d, l1p) 
    requires PageAligned(a) && address_is_secure(a) 
    requires a in WritablePagesInTable(mkAbsPTable(d, l1p)) 
    requires addrInPage(a, p)
    ensures  d[p].PageDbEntryTyped? && d[p].entry.DataPage?
{
    reveal_validPageDb();
    reveal_pageDbEntryCorresponds();
    reveal_pageContentsCorresponds();
    lemma_WritablePages(d, l1p, a);
}

lemma userspaceExecutionPreservesPageDb(d:PageDb,s:state,s':state, l1:PageNr)
    requires SaneMem(s.m) && SaneMem(s'.m) && validPageDb(d)
        && ValidState(s) && ValidState(s')
    requires evalUserspaceExecution(s,s')
    requires pageDbCorresponds(s.m,  d)
    requires s.conf.ttbr0.ptbase == page_paddr(l1);
    requires nonStoppedL1(d, l1);
    ensures  pageDbCorresponds(s'.m, d)
{
    reveal_ValidMemState();
    reveal_pageDbEntryCorresponds();
    reveal_pageContentsCorresponds();


    forall ( p | validPageNr(p) )
        ensures pageDbEntryCorresponds(d[p], extractPageDbEntry(s'.m,p));
    {
        assert extractPageDbEntry(s.m, p) == extractPageDbEntry(s'.m, p);
        PageDbCorrespondsImpliesEntryCorresponds(s.m, d, p);
        assert pageDbEntryCorresponds(d[p], extractPageDbEntry(s.m, p));
        
    }

    var pt := ExtractAbsPageTable(s);
    assert pt.Just?;

    forall ( p | validPageNr(p) && d[p].PageDbEntryTyped? && 
        !d[p].entry.DataPage? )
        ensures pageContentsCorresponds(p, d[p], extractPage(s'.m, p));
    {
        forall ( a:addr | page_monvaddr(p) <= a < page_monvaddr(p) + PAGESIZE() )
            ensures s'.m.addresses[a] == s.m.addresses[a]
            {
               var pt := ExtractAbsPageTable(s);
               assert pt.Just?;
               var pages := WritablePagesInTable(fromJust(pt));

               onlyDataPagesAreWritable(p, a, d, s, s', l1);
               assert BitwiseMaskHigh(a, 12) !in pages;
               nonWritablePagesAreSafeFromHavoc(a, s, s'); 

               assert s'.m.addresses[a] == s.m.addresses[a];

            }
        assert extractPage(s.m, p) == extractPage(s'.m, p);
        assert pageContentsCorresponds(p, d[p], extractPage(s.m, p));
    }
}

lemma userspaceExecutionPreservesPrivState(s:state,s':state)
    requires ValidState(s) && ValidState(s')
    requires evalUserspaceExecution(s,s')
    ensures GlobalsInvariant(s,s')
    ensures (reveal_ValidRegState(); s.regs[SP(Monitor)] == s'.regs[SP(Monitor)])
{
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
    ensures GlobalsInvariant(s,  r)
{
    var l1p := l1pOfDispatcher(d, dp);
    reveal_evalMOVSPCLRUC();
    var s2, s3, ex, s4 :| ValidState(s2) && ValidState(s3) && ValidState(s4)
        && evalEnterUserspace(s, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && ApplicationUsermodeContinuationInvariant(s4, r);

    enterUserspacePreservesStuff(d, s,  s2);
    userspaceExecutionPreservesPrivState(s2, s3);
    userspaceExecutionPreservesPageDb(d, s2, s3, l1p);
    exceptionTakenPreservesStuff(d, s3, ex, s4);
    assert KomExceptionHandlerInvariant(s4, d, r, dp) by { reveal_AUCIdef(); }
    assert SaneState(r);
    reveal_ValidRegState();
    calc {
        OperandContents(s, OSP);
        s.regs[SP(Monitor)];
        s2.regs[SP(Monitor)];
        s3.regs[SP(Monitor)];
        s4.regs[SP(Monitor)];
        r.regs[SP(Monitor)];
        OperandContents(r, OSP);
    }
}

lemma lemma_validEnter(s0:state, s1:state, r:state, sd:PageDb,
                       dp:word, a1:word, a2:word, a3:word)
    returns (exs:state, rd:PageDb)
    requires SaneState(s0) && SaneState(s1)
    requires validPageDb(sd) && pageDbCorresponds(s0.m, sd) && pageDbCorresponds(s1.m, sd)
    requires smc_enter_err(sd, dp, false) == KOM_ERR_SUCCESS()
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
    var s2, s3, ex, s4 :| ValidState(s2) && ValidState(s3) && ValidState(s4)
        && evalEnterUserspace(s1, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && ApplicationUsermodeContinuationInvariant(s4, r);

    assert entryTransition(s1, s2);
    assert userspaceExecutionAndException(s2, s3, ex, s4);

    enterUserspacePreservesStuff(sd, s1,  s2);
    userspaceExecutionPreservesPrivState(s2, s3);
    userspaceExecutionPreservesPageDb(sd, s2, s3, l1p);
    exceptionTakenPreservesStuff(sd, s3, ex, s4);
    assert KomExceptionHandlerInvariant(s4, sd, r, dp) by { reveal_AUCIdef(); }

    exs := s4;
    rd := exceptionHandled(exs, sd, dp).2;
    exceptionHandledValidPageDb(s3, ex, s4, sd, dp);

    assert validExceptionTransition(SysState(s4, sd), SysState(r, rd), dp);
    assert (reveal_ValidRegState();
        (r.regs[R0], r.regs[R1], rd) == exceptionHandled(exs, sd, dp));

    reveal_validEnter();
}
