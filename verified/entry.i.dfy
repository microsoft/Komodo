include "entry.s.dfy"
include "ptables.i.dfy"

function exceptionHandled_premium(s:SysState) : (int, int, PageDb)
    requires validSysState(s)
    requires mode_of_state(s.hw) != User
    ensures var (r0,r1,d) := exceptionHandled_premium(s);
        validPageDb(d)
{
    exceptionHandledValidPageDb(s);
    exceptionHandled(s)
}

lemma exceptionHandledValidPageDb(s:SysState) 
    requires validSysState(s)
    requires mode_of_state(s.hw) != User
    ensures var (r0,r1,d) := exceptionHandled(s);
        validPageDb(d)
{
   reveal_validPageDb();
   reveal_ValidSRegState();
   reveal_ValidRegState();
   var (r0,r1,d') := exceptionHandled(s);
        var p := s.g.g_cur_dispatcher;
        assert validPageDbEntry(d', p);
       
        forall( p' | validPageNr(p') && d'[p'].PageDbEntryTyped? && p'!=p )
            ensures validPageDbEntry(d', p');
        {
            var e  := s.d[p'].entry;
            var e' := d'[p'].entry;
            if(e.Addrspace?){
                assert e.refcount == e'.refcount;
                assert addrspaceRefs(d', p') == addrspaceRefs(s.d,p');
                assert validAddrspace(d',p');
            }
        }
        assert pageDbEntriesValid(d');

        assert validPageDb(d');
}

/*
lemma eqAddressesSameExtraction(m:memstate, m':memstate)
    requires SaneMem(m) && SaneMem(m')
    requires m.addresses == m'.addresses
    ensures  secPagesPreserved(m, m')
{
}

lemma secAddressesImplSecPagesPres(m:memstate,m':memstate)
    requires SaneMem(m) && SaneMem(m')
    requires secAddressesPreserved(m, m')
    ensures  secPagesPreserved(m, m')
{
}

lemma enterUserspacePreservesGlobals(s:state,r:state)
    requires ValidState(s) && evalEnterUserspace(s,r)
    ensures  s.m.globals == r.m.globals
    ensures  s.m.addresses == r.m.addresses
{
    reveal_ValidMemState();
}

lemma userspaceExecutionPreservesGlobals(s:state,r:state)
    requires ValidState(s) && evalUserspaceExecution(s,r)
    ensures  s.m.globals == r.m.globals
    ensures  s.m.addresses == r.m.addresses
{
    reveal_ValidMemState();
    assume false;
}

lemma exceptionTakenPreservesGlobals(s:state, ex:exception, r:state)
    requires ValidState(s) && evalExceptionTaken(s, ex, r)
    ensures  s.m.globals == r.m.globals
    ensures  s.m.addresses == r.m.addresses
{
    reveal_ValidMemState();
}

lemma appInvariantPreservesGlobals(s:state,r:state)
    requires ValidState(s) &&
        ApplicationUsermodeContinuationInvariant(s, r)
    ensures  s.m.globals == r.m.globals
    ensures  s.m.addresses == r.m.addresses
{
    reveal_ValidMemState();
}

lemma evalMOVSPCLRUCPreservesGlobals(s:state, r:state)
    requires ValidState(s)
    requires SaneMem(s.m) && SaneMem(r.m) && evalMOVSPCLRUC(s, r)
    ensures  s.m.globals == r.m.globals
    ensures secPagesPreserved(s.m, r.m)
{

    reveal_ValidMemState();
    forall ( ex, s2, s3, s4 | ValidState(s2) && ValidState(s3) && ValidState(s4)
        && evalEnterUserspace(s, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && ApplicationUsermodeContinuationInvariant(s4, r)
        && r.ok )
    ensures s.m.globals == r.m.globals
    ensures secPagesPreserved(s.m, r.m)
    {
        enterUserspacePreservesGlobals(s,s2);
        userspaceExecutionPreservesGlobals(s2,s3);
        exceptionTakenPreservesGlobals(s3,ex,s4);
        appInvariantPreservesGlobals(s4,r);
        assert s.m.addresses == r.m.addresses;
        eqAddressesSameExtraction(s.m, r.m);
    }
}
*/

predicate secPagesPreserved(m:memstate,m':memstate)
{
    SaneMem(m) && SaneMem(m') &&
    forall p | validPageNr(p) :: extractPage(m, p) == extractPage(m', p)
}

lemma enterUserspacePreservesPageDb(d:PageDb,s:state,s':state)
    requires SaneMem(s.m) && SaneMem(s'.m) && validPageDb(d)
        && ValidState(s) && ValidState(s')
    requires evalEnterUserspace(s, s')
    requires pageDbCorresponds(s.m, d)
    ensures  pageDbCorresponds(s'.m, d)
{
    reveal_PageDb();
    reveal_ValidMemState();
    reveal_pageDbEntryCorresponds();
    reveal_pageContentsCorresponds();
}

lemma nonWriteablePagesAreSafe(m:addr,s:state,s':state)
    requires ValidState(s) && ValidState(s')
    requires evalUserspaceExecution(s, s')
    requires var pt := ExtractAbsPageTable(s);
        pt.Just? && var pages := WritablePagesInTable(fromJust(pt));
        BitwiseAnd(m, 0xffff_f000) !in pages
    requires m in s.m.addresses
    ensures s'.m.addresses[m] == s.m.addresses[m]
{
    reveal_ValidMemState();
    reveal_ValidRegState();
    var pt := ExtractAbsPageTable(s);
    assert pt.Just?;
    var pages := WritablePagesInTable(fromJust(pt));
    assert s'.m.addresses[m] == havocPages(pages, s.m.addresses, s'.m.addresses)[m];
    assert havocPages(pages, s.m.addresses, s'.m.addresses)[m] == s.m.addresses[m];
}

lemma onlyDataPagesAreWritable(p:PageNr,a:addr,d:PageDb,s:state, s':state)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires ValidState(s) && ValidState(s') && evalUserspaceExecution(s,s')
    requires validPageDb(d) && d[p].PageDbEntryTyped? && !d[p].entry.DataPage?
    requires WordAligned(a)
    requires addrInPage(a, p)
    ensures var pt := ExtractAbsPageTable(s);
        pt.Just? && var pages := WritablePagesInTable(fromJust(pt));
        BitwiseAnd(a, 0xffff_f000) !in pages
{
    reveal_validPageDb();

    var pt := ExtractAbsPageTable(s);
    assert pt.Just?;
    var pages := WritablePagesInTable(fromJust(pt));
    var vbase := s.conf.ttbr0.ptbase + PhysBase();
    assume address_is_secure(vbase);
    assume PageAligned(vbase);
    assert ExtractAbsL1PTable(s.m, vbase) == fromJust(pt);
    var l1p := monvaddr_page(vbase);
    assume BitwiseAnd(a,0xffff_f000) in pages <==> a in pages;
    assume nonStoppedL1(d,l1p);
    assume fromJust(pt) == mkAbsPTable(d, l1p);
    assume WritablePagesInTable(fromJust(pt)) ==
        WritablePagesInTable(mkAbsPTable(d, l1p));
    
    
    forall( a':addr, p':PageNr | a' in WritablePagesInTable(fromJust(pt)) &&
        addrInPage(a',p') )
        ensures d[p'].PageDbEntryTyped? && d[p'].entry.DataPage?
    {
        lemma_writablePagesAreDataPages(p', a', d, l1p);
    }
    /*
    assert a in pages ==>
        d[p].PageDbEntryTyped? && d[p].entry.DataPage? by
        {
            assume a in pages <==> a in WritablePagesInTable(mkAbsPTable(d, l1p));
            lemma_writablePagesAreDataPages(p, a, d, l1p);
        }
    */
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

lemma userspaceExecutionPreservesPageDb(d:PageDb,s:state,s':state)
    requires SaneMem(s.m) && SaneMem(s'.m) && validPageDb(d)
        && ValidState(s) && ValidState(s')
    requires evalUserspaceExecution(s,s')
    requires pageDbCorresponds(s.m,  d)
    ensures  pageDbCorresponds(s'.m, d)
{
    reveal_PageDb();
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

    /*
    assert pt == mkAbsPTable(d, s.conf.ttbr0.ptbase + PhysBase()) by
    {
        var vbase := s.conf.ttbr0.ptbase + PhysBase();
        assert ValidAbsL1PTable(s.m, vbase);
        lemma_ptablesMatch(s, d, vbase);
    }
    */


    /*
    forall( a | a in WritablePagesInTable(fromJust(pt)) )
        ensures  forall p | addrInPage(a, p) ::
            d[p].PageDbEntryTyped? && d[p].entry.DataPage?
    {
        assume false;
    }
    */

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
               onlyDataPagesAreWritable(p, a, d, s, s');
               assert BitwiseAnd(a, 0xffff_f000) !in pages;
               nonWriteablePagesAreSafe(a, s, s'); 
            }
        assert extractPage(s.m, p) == extractPage(s'.m, p);
        assert pageContentsCorresponds(p, d[p], extractPage(s.m, p));
    }
}

lemma exceptionTakenPreservesPageDb(d:PageDb,s:state,ex:exception,s':state)
    requires SaneMem(s.m) && SaneMem(s'.m) && validPageDb(d)
        && ValidState(s) && ValidState(s')
    requires evalExceptionTaken(s, ex, s')
    requires pageDbCorresponds(s.m, d)
    ensures  pageDbCorresponds(s'.m, d)
{
    reveal_PageDb();
    reveal_ValidMemState();
    reveal_pageDbEntryCorresponds();
    reveal_pageContentsCorresponds();
}

lemma appInvariantPreservesPageDb(d:PageDb,s:state,s':state)
    requires SaneMem(s.m) && SaneMem(s'.m) && validPageDb(d)
        && ValidState(s) && ValidState(s')
    requires ApplicationUsermodeContinuationInvariant(s, s')
    requires pageDbCorresponds(s.m , d)
    ensures  pageDbCorresponds(s'.m, d)
{
    reveal_PageDb();
    reveal_ValidMemState();
    reveal_pageDbEntryCorresponds();
    reveal_pageContentsCorresponds();
}


lemma evalMOVSPCLRUCPreservesPageDb(d:PageDb, s:state, r:state)
    requires ValidState(s) && ValidState(r)
    requires SaneMem(s.m) && SaneMem(r.m) && validPageDb(d)
    requires evalMOVSPCLRUC(s, r) && pageDbCorresponds(s.m, d)
    ensures  pageDbCorresponds(r.m, d)

{
    reveal_PageDb();
    reveal_ValidMemState();
    reveal_pageDbEntryCorresponds();
    reveal_pageContentsCorresponds();

    forall ( ex, s2, s3, s4 | ValidState(s2) && ValidState(s3) && ValidState(s4)
        && evalEnterUserspace(s, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && ApplicationUsermodeContinuationInvariant(s4, r)
        && r.ok )
        ensures  pageDbCorresponds(r.m, d)
    {
        enterUserspacePreservesPageDb(d, s,  s2);
        userspaceExecutionPreservesPageDb(d, s2, s3); 
        exceptionTakenPreservesPageDb(d, s3, ex, s4);
        appInvariantPreservesPageDb(d, s4, r);
    }
}

