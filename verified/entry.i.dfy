include "entry.s.dfy"
include "pagedb.i.dfy"

/*
predicate weakEquiv(d:PageDb,d':PageDb)
    requires validPageDb(d) && validPageDb(d')
{
    (forall p | validPageNr(p) :: 
        d[p].PageDbEntryTyped? <==> d'[p].PageDbEntryTyped?) &&
    (forall p | validPageNr(p) && d[p].PageDbEntryTyped? ::
        d[p].addrspace == d'[p].addrspace) &&
    (forall p | validPageNr(p) && d[p].PageDbEntryTyped? ::
        d[p].entry.Addrspace?  <==> d'[p].entry.Addrspace? &&
        d[p].entry.Dispatcher? <==> d'[p].entry.Dispatcher? &&
        d[p].entry.L1PTable?   <==> d'[p].entry.L1PTable? &&
        d[p].entry.L2PTable?   <==> d'[p].entry.L2PTable?)
}

lemma equivUpToEnteredImpliesWeakEquiv(d:PageDb,d':PageDb,p':PageNr)
    requires nonStoppedL1(d,p') && nonStoppedL1(d',p') &&
        equivalentExceptPage(d,d',p')
    ensures weakEquiv(d,d')
{
    forall ( p | validPageNr(p)) 
        ensures d[p].PageDbEntryTyped? <==> d'[p].PageDbEntryTyped?
    {
    }
    forall (p | validPageNr(p) && d[p].PageDbEntryTyped?)
        ensures d[p].addrspace == d'[p].addrspace
    {
        if(p == p'){
        } else {
            assert d[p] == d'[p];
        }
    }
    forall (p | validPageNr(p) && d[p].PageDbEntryTyped?)
        ensures 
        (d[p].entry.Addrspace?  <==> d'[p].entry.Addrspace? &&
        d[p].entry.Dispatcher? <==> d'[p].entry.Dispatcher? &&
        d[p].entry.L1PTable?   <==> d'[p].entry.L1PTable? &&
        d[p].entry.L2PTable?   <==> d'[p].entry.L2PTable?)
    {
        if(p == p'){
            assert nonStoppedL1(d,p);
            assert nonStoppedL1(d',p);
        } else {
            assert d[p] == d'[p];
            assert d[p].entry == d'[p].entry;
            assert (d[p].entry.Addrspace?  <==> d'[p].entry.Addrspace? &&
                    d[p].entry.Dispatcher? <==> d'[p].entry.Dispatcher? &&
                    d[p].entry.L1PTable?   <==> d'[p].entry.L1PTable? &&
                    d[p].entry.L2PTable?   <==> d'[p].entry.L2PTable?);
        }
    }
}

lemma MIClosedOverEquivUpToEntered(hw:state,hw':state,d:PageDb,d':PageDb,p:PageNr)
    requires ValidState(hw) && ValidState(hw') &&
        nonStoppedL1(d, p) && nonStoppedL1(d', p)
    requires equivalentExceptPage(d,d',p)
    requires WSMemInvariantExceptAddrspaceAtPage(hw,hw',d ,p)
    ensures  WSMemInvariantExceptAddrspaceAtPage(hw,hw',d',p)
{
    reveal_validPageDb();
    equivUpToEnteredImpliesWeakEquiv(d,d',p);
    forall(m | m in hw.m.addresses && address_is_secure(m))
        ensures memSWrInAddrspace(d, p, m) <==> memSWrInAddrspace(d', p, m)
    {
        assert m in hw'.m.addresses;
    }
}

lemma MIWeaklyTransitive(s1:SysState, s2:SysState, s3:SysState, d:PageDb, p:PageNr)
    requires validSysState(s1) && validSysState(s2) && validSysState(s3) && nonStoppedL1(d, p)
    requires WSMemInvariantExceptAddrspaceAtPage(s1.hw, s2.hw, d, p) &&
        WSMemInvariantExceptAddrspaceAtPage(s2.hw, s3.hw, d, p)
    ensures WSMemInvariantExceptAddrspaceAtPage(s1.hw, s3.hw, d, p)
{
}

lemma MITransitive(s1:SysState, s2:SysState, s3:SysState, p:PageNr)
    requires validSysState(s1) && validSysState(s2) && validSysState(s3) &&
        nonStoppedL1(s1.d,p) && nonStoppedL1(s2.d,p) && nonStoppedL1(s3.d,p) 
    requires equivalentExceptPage(s1.d,s2.d,p) && equivalentExceptPage(s2.d,s3.d,p) 
    requires WSMemInvariantExceptAddrspaceAtPage(s1.hw, s2.hw, s1.d, p) &&
        WSMemInvariantExceptAddrspaceAtPage(s2.hw, s3.hw, s2.d, p)
    ensures WSMemInvariantExceptAddrspaceAtPage(s1.hw, s3.hw, s1.d, p)
{
    MIClosedOverEquivUpToEntered(s2.hw,s3.hw,s2.d,s1.d,p);
    assert WSMemInvariantExceptAddrspaceAtPage(s2.hw, s3.hw, s1.d, p);
    MIWeaklyTransitive(s1,s2,s3,s1.d,p);
    assert WSMemInvariantExceptAddrspaceAtPage(s1.hw, s3.hw, s1.d, p);
}

*/

/*
lemma valEnterImpliesBRPres(s:SysState,s':SysState,dispPage:PageNr,
    a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage,a1,a2,a3).1 == KOM_ERR_SUCCESS()
        && validEnter(s, s', dispPage,a1,a2,a3)
    ensures validEnter(s,s',dispPage,a1,a2,a3) ==>
        bankedRegsPreserved(s.hw, s'.hw)
{
    reveal_ValidRegState();
    forall ( s2, s3, s4, s5 | validSysStates({s2,s3,s4,s5})
        && preEntryEnter(s,s2,dispPage,a1,a2,a3)
        && entryTransitionEnter(s2, s3)
        && s4.d == s3.d && userspaceExecution(s3.hw, s4.hw, s3.d)
        && validERTransition(s4, s5) &&
            !s5.hw.conf.ex.none? && mode_of_state(s5.hw) != User
        && validERTransition(s5, s')
        && (s'.hw.regs[R0], s'.hw.regs[R1], s'.d) ==
            exceptionHandled(s5)
        && s'.hw.conf.scr.ns == NotSecure)
        ensures bankedRegsPreserved(s.hw, s'.hw)
    {
        assert bankedRegsPreserved(s.hw,  s2.hw);
        assert bankedRegsPreserved(s2.hw, s3.hw);
        assert bankedRegsPreserved(s3.hw, s4.hw);
        assert bankedRegsPreserved(s4.hw, s5.hw);
        assert bankedRegsPreserved(s5.hw, s'.hw);
    }
}
*/

/*
lemma validERImpliesMemInv(s:SysState, s':SysState)
    requires validERTransition(s,s');
    ensures nonStoppedL1(s.d, l1pOfDispatcher(s.d, s.g.g_cur_dispatcher));
    ensures WSMemInvariantExceptAddrspaceAtPage(s.hw,s'.hw,s.d,
        l1pOfDispatcher(s.d, s.g.g_cur_dispatcher));
    // ensures equivalentExceptPage(s.d, s'.d, s.g.g_cur_dispatcher);
{
}
*/

/*
lemma valEnterImpliesMInv(s:SysState,s':SysState,dispPage:PageNr,
    a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage,a1,a2,a3).1 == KOM_ERR_SUCCESS()
    requires validEnter(s, s', dispPage,a1,a2,a3)
    ensures
        var p := l1pOfDispatcher(s.d, dispPage);
        nonStoppedL1(s.d,p)
        && validSysState(s')
        && WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d, p)
{
    var p := l1pOfDispatcher(s.d, dispPage);
    assert nonStoppedL1(s.d, p);
    reveal_ValidRegState();
    forall ( s2, s3, s4 | validSysStates({s2,s3,s4})
        && preEntryEnter(s,s2,dispPage,a1,a2,a3)
        && entryTransitionEnter(s2, s3)
        && s4.d == s3.d && userspaceExecution(s3.hw, s4.hw, s3.d)
        && validERTransition(s4, s')
        && (s'.hw.regs[R0], s'.hw.regs[R1], s'.d) ==
            exceptionHandled(s4)
        && s'.hw.conf.scr.ns == NotSecure)
        ensures 
            ValidState(s.hw) && ValidState(s'.hw) && nonStoppedL1(s.d, p) &&
            WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d, p)
    {
    /*
        assert preEntryEnter(s,s2,dispPage,a1,a2,a3) ==> 
            WSMemInvariantExceptAddrspaceAtPage(s.hw, s2.hw, s.d,p);
        assert preEntryEnter(s,s2,dispPage,a1,a2,a3);
        assert WSMemInvariantExceptAddrspaceAtPage(s.hw,  s2.hw, s.d, p);
        
        validERImpliesMemInv(s2,s3);
        assert l1pOfDispatcher(s2.d, s2.g.g_cur_dispatcher) == p;
        assert WSMemInvariantExceptAddrspaceAtPage(s2.hw, s3.hw, s2.d, p);
        MITransitive(s, s2, s3, p);
        assert WSMemInvariantExceptAddrspaceAtPage(s.hw, s3.hw, s.d, p);
     
        assert WSMemInvariantExceptAddrspaceAtPage(s3.hw, s4.hw, s.d, p);
        assert WSMemInvariantExceptAddrspaceAtPage(s.hw, s4.hw, s.d, p);
        
        assert WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d, p);
        */
    }
}
*/

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
lemma enterUserspacePreservesGlobals(s:state,r:state)
    requires ValidState(s) && evalEnterUserspace(s,r)
    ensures  s.m.globals == r.m.globals
{
}

lemma userspaceExecutionPreservesGlobals(s:state,r:state)
    requires ValidState(s) && evalUserspaceExecution(s,r)
    ensures  s.m.globals == r.m.globals
{
}

lemma exceptionTakenPreservesGlobals(s:state, ex:exception, r:state)
    requires ValidState(s) && evalExceptionTaken(s, ex, r)
    ensures  s.m.globals == r.m.globals
{
}

lemma appInvariantPreservesGlobals(s:state,r:state)
    requires ValidState(s) &&
        ApplicationUsermodeContinuationInvariant(s, r)
    ensures  s.m.globals == r.m.globals
{
}

lemma evalMOVSPCLRUCPreservesGlobals(s:state, r:state)
    requires AppStatePred(s) && evalMOVSPCLRUC(s, r)
    ensures  s.m.globals == r.m.globals
{

    forall ( ex, s2, s3, s4 | ValidState(s2) && ValidState(s3) && ValidState(s4)
        && evalEnterUserspace(s, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && ApplicationUsermodeContinuationInvariant(s4, r)
        && r.ok )
    ensures s.m.globals == r.m.globals
    {
        enterUserspacePreservesGlobals(s,s2);
        userspaceExecutionPreservesGlobals(s2,s3);
        exceptionTakenPreservesGlobals(s3,ex,s4);
        appInvariantPreservesGlobals(s4,r);
    }
}
*/

lemma enterUserspacePreservesPageDb(d:PageDb,s:state,s':state)
    requires SaneState(s) && SaneState(s') && validPageDb(d)
    requires evalEnterUserspace(s, s')
    requires pageDbCorresponds(s.m, d)
    ensures  pageDbCorresponds(s'.m, d)
{
    reveal_PageDb();
    reveal_ValidMemState();
    reveal_pageDbEntryCorresponds();
    reveal_pageContentsCorresponds();
}

lemma userspaceHavocPreservesPageDb(d:PageDb,s:state,s':state)
    requires SaneState(s) && SaneState(s') && validPageDb(d)
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
        ensures pageContentsCorresponds(p, d[p], extractPage(s'.m, p));
    {
        assert extractPageDbEntry(s.m, p) == extractPageDbEntry(s'.m, p);
        PageDbCorrespondsImpliesEntryCorresponds(s.m, d, p);
        assert pageDbEntryCorresponds(d[p], extractPageDbEntry(s.m, p));
        
        assert extractPage(s.m, p) == extractPage(s'.m, p);
        assert pageContentsCorresponds(p, d[p], extractPage(s.m, p));
    }
}

lemma exceptionTakenPreservesPageDb(d:PageDb,s:state,ex:exception,s':state)
    requires SaneState(s) && SaneState(s') && validPageDb(d)
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
    requires SaneState(s) && SaneState(s') && validPageDb(d)
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
    requires SaneState(s) && SaneState(r) && validPageDb(d)
    requires thisIsKomodo()
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
        userspaceHavocPreservesPageDb(d, s2, s3); 
        exceptionTakenPreservesPageDb(d, s3, ex, s4);
        appInvariantPreservesPageDb(d, s4, r);
    }
}

lemma MemInvarSubsumption(s:SysState,s':SysState,p:PageNr)
    requires validSysState(s) && validSysState(s') && nonStoppedL1(s.d, p)
    requires AllMemInvariant(s.hw,s'.hw) && s.d == s'.d
    ensures  WSMemInvariantExceptAddrspaceAtPage(s.hw,s'.hw,s.d,p)
{
}

/*
predicate {:opaque} validEnter_premium(s:SysState,s':SysState,dispPage:PageNr,
    a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage, a1, a2, a3).1 == KOM_ERR_SUCCESS()
    ensures validEnter_premium(s, s', dispPage,a1,a2,a3)
        == validEnter(s, s', dispPage,a1,a2,a3)
        /*
    ensures (smc_enter(s.d, dispPage,a1,a2,a3).1 == KOM_ERR_SUCCESS()
             && validEnter(s, s', dispPage,a1,a2,a3)) ==> 
             */
    ensures validEnter_premium(s, s', dispPage,a1,a2,a3) ==> 
        var p := l1pOfDispatcher(s.d, dispPage);
        nonStoppedL1(s.d, dispPage)
        && validSysState(s')
        && WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d, p)
        && bankedRegsPreserved(s.hw, s'.hw)
{
    if(validEnter(s, s',dispPage,a1,a2,a3)) then
        valEnterImpliesMInv(s, s', dispPage,a1,a2,a3);
        assert WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d, 
            l1pOfDispatcher(s.d,dispPage));
        valEnterImpliesBRPres(s, s', dispPage,a1,a2,a3);
        validEnter(s, s', dispPage,a1,a2,a3)
    else
        validEnter(s, s', dispPage,a1,a2,a3)
}
*/
