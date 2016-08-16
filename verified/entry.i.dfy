include "entry.s.dfy"

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

lemma MIWeaklyCommute(s1:SysState, s2:SysState, s3:SysState, d:PageDb, p:PageNr)
    requires validSysState(s1) && validSysState(s2) && validSysState(s3) && nonStoppedL1(d, p)
    requires WSMemInvariantExceptAddrspaceAtPage(s1.hw, s2.hw, d, p) &&
        WSMemInvariantExceptAddrspaceAtPage(s2.hw, s3.hw, d, p)
    ensures WSMemInvariantExceptAddrspaceAtPage(s1.hw, s3.hw, d, p)
{
}

lemma MICommute(s1:SysState, s2:SysState, s3:SysState, p:PageNr)
    requires validSysState(s1) && validSysState(s2) && validSysState(s3) &&
        nonStoppedL1(s1.d,p) && nonStoppedL1(s2.d,p) && nonStoppedL1(s3.d,p) 
    requires equivalentExceptPage(s1.d,s2.d,p) && equivalentExceptPage(s2.d,s3.d,p) 
    requires WSMemInvariantExceptAddrspaceAtPage(s1.hw, s2.hw, s1.d, p) &&
        WSMemInvariantExceptAddrspaceAtPage(s2.hw, s3.hw, s2.d, p)
    ensures WSMemInvariantExceptAddrspaceAtPage(s1.hw, s3.hw, s1.d, p)
{
    MIClosedOverEquivUpToEntered(s2.hw,s3.hw,s2.d,s1.d,p);
    assert WSMemInvariantExceptAddrspaceAtPage(s2.hw, s3.hw, s1.d, p);
    MIWeaklyCommute(s1,s2,s3,s1.d,p);
    assert WSMemInvariantExceptAddrspaceAtPage(s1.hw, s3.hw, s1.d, p);
}

*/

/*
lemma valEnterImpliesBRPres(s:SysState,s':SysState,dispPage:PageNr,
    a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage,a1,a2,a3).1 == KEV_ERR_SUCCESS()
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

lemma valEnterImpliesMInv(s:SysState,s':SysState,dispPage:PageNr,
    a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage,a1,a2,a3).1 == KEV_ERR_SUCCESS()
    requires validEnter(s, s', dispPage,a1,a2,a3)
    ensures
        var p := l1pOfDispatcher(s.d, dispPage);
        nonStoppedL1(s.d,p)
        && validSysState(s')
        && WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d, p)
{
        //todo. or don't use this.
    assume false;
    var p := l1pOfDispatcher(s.d, dispPage);
    assert nonStoppedL1(s.d, p);
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
        MICommute(s, s2, s3, p);
        assert WSMemInvariantExceptAddrspaceAtPage(s.hw, s3.hw, s.d, p);
     
        assert WSMemInvariantExceptAddrspaceAtPage(s3.hw, s4.hw, s.d, p);
        assert WSMemInvariantExceptAddrspaceAtPage(s.hw, s4.hw, s.d, p);
        
        assert WSMemInvariantExceptAddrspaceAtPage(s.hw, s'.hw, s.d, p);
        */
    }
}

function exceptionHandled_premium(s:SysState) : (int, int, PageDb)
    requires validSysState(s)
    requires !s.hw.conf.ex.none?
    requires mode_of_state(s.hw) != User
    ensures var (r0,r1,d) := exceptionHandled_premium(s);
        validPageDb(d)
{
    exceptionHandledValidPageDb(s);
    exceptionHandled(s)
}

lemma exceptionHandledValidPageDb(s:SysState) 
    requires validSysState(s)
    requires !s.hw.conf.ex.none?
    requires mode_of_state(s.hw) != User
    ensures var (r0,r1,d) := exceptionHandled(s);
        validPageDb(d)
{
   reveal_validPageDb();
   reveal_ValidSRegState();
   reveal_ValidRegState();
   reveal_ValidConfig();
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
predicate {:opaque} validEnter_premium(s:SysState,s':SysState,dispPage:PageNr,
    a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage, a1, a2, a3).1 == KEV_ERR_SUCCESS()
    ensures validEnter_premium(s, s', dispPage,a1,a2,a3)
        == validEnter(s, s', dispPage,a1,a2,a3)
        /*
    ensures (smc_enter(s.d, dispPage,a1,a2,a3).1 == KEV_ERR_SUCCESS()
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
