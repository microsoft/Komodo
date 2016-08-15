include "entry.s.dfy"
/*
lemma MICommute(s1:SysState, s2:SysState, s3:SysState, p:PageNr)
    requires validSysState(s1) && validSysState(s2) && validSysState(s3) &&
        s1.d == s2.d == s3.d && validL1PTPage(s1.d, p) &&
        (validPageDbImpliesWellFormed(s1.d); !hasStoppedAddrspace(s1.d, p))
    requires WSMemInvariantExceptAddrspaceAtPage(s1, s2, p) &&
        WSMemInvariantExceptAddrspaceAtPage(s2, s3, p)
    ensures WSMemInvariantExceptAddrspaceAtPage(s1, s3, p)
{
}

predicate {:opaque} validResume_premium(s:SysState,s':SysState,dispPage:PageNr)
    requires validSysState(s)
    ensures validResume_premium(s, s', dispPage) == validResume(s, s', dispPage)
    ensures (smc_resume(s.d, dispPage).1 == KEV_ERR_SUCCESS()
             && validResume(s, s', dispPage)) ==> 
        validSysState(s')
        && bankedRegsPreservedForMonitor(s, s')
        && (var p := l1pOfDispatcher(s.d, dispPage);
            validL1PTPage(s.d, p)
            && (validPageDbImpliesWellFormed(s.d); !hasStoppedAddrspace(s.d, p))
            && WSMemInvariantExceptAddrspaceAtPage(s, s', p))
{
    if(smc_resume(s.d, dispPage).1 == KEV_ERR_SUCCESS() && validResume(s, s', 
        dispPage)) then
        valResImpliesMInv(s, s', dispPage);
        valResImpliesBRPres(s, s', dispPage);
        validResume(s, s', dispPage)
    else
        validResume(s, s', dispPage)
    
}

lemma valResImpliesBRPres(s:SysState,s':SysState,dispPage:PageNr)
    requires validSysState(s)
    requires smc_resume(s.d, dispPage).1 == KEV_ERR_SUCCESS()
        && validResume(s, s', dispPage)
    ensures bankedRegsPreservedForMonitor(s, s')
{
    
    forall( s2, s3, s4 | validEntryTransitionResume(s,s2,dispPage) 
        && userspaceExecution(s2, s3)
        && exception(s3, s4)
        && monitorReturn(s4, s') )
        ensures bankedRegsPreservedForMonitor(s, s')
    {
        assert bankedRegsPreservedForMonitor(s, s2);
        assert bankedRegsPreservedForMonitor(s2, s3);
        assert bankedRegsPreservedForMonitor(s3, s4);
        assert bankedRegsPreservedForMonitor(s4, s');
    }
}

lemma valResImpliesMInv(s:SysState,s':SysState,dispPage:PageNr)
    requires validSysState(s)
    requires smc_resume(s.d, dispPage).1 == KEV_ERR_SUCCESS()
                && validResume(s, s', dispPage)
    ensures
        validSysState(s) && validSysState(s') && s'.d == s.d
    ensures
        var p := l1pOfDispatcher(s.d, dispPage);
        validL1PTPage(s.d, p)
        && (validPageDbImpliesWellFormed(s.d); !hasStoppedAddrspace(s.d, p))
        && WSMemInvariantExceptAddrspaceAtPage(s, s', p)
{   
    forall( s2, s3, s4 | validEntryTransitionResume(s,s2,dispPage) 
        && userspaceExecution(s2, s3)
        && exception(s3, s4)
        && monitorReturn(s4, s') )
        ensures WSMemInvariantExceptAddrspaceAtPage(s, s', 
            l1pOfDispatcher(s.d, dispPage))
    {
        var p := l1pOfDispatcher(s.d, dispPage);
        assert WSMemInvariantExceptAddrspaceAtPage(s,  s2, p);
        assert s2.hw.conf.ttbr0 == p;
        assert WSMemInvariantExceptAddrspaceAtPage(s2, s3, p);
        assert s3.hw.conf.ttbr0 == s2.hw.conf.ttbr0;
        assert s3.hw.conf.ttbr0 == p;
        assert WSMemInvariantExceptAddrspaceAtPage(s3, s4, p);
        assert s4.hw.conf.ttbr0 == p;
        assert WSMemInvariantExceptAddrspaceAtPage(s4, s', p);
        MICommute(s, s2, s3, p);
        MICommute(s, s3, s4, p);
        MICommute(s, s4, s', p);
    }
}

lemma valEnterImpliesBRPres(s:SysState,s':SysState,dispPage:PageNr,
    a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage,a1,a2,a3).1 == KEV_ERR_SUCCESS()
        && validEnter(s, s', dispPage,a1,a2,a3)
    ensures bankedRegsPreservedForMonitor(s, s')
{
    
    forall( s2, s3, s4 | validEntryTransitionEnter(s,s2,dispPage,a1,a2,a3) 
        && userspaceExecution(s2, s3)
        && exception(s3, s4)
        && monitorReturn(s4, s') )
        ensures bankedRegsPreservedForMonitor(s, s')
    {
        assert bankedRegsPreservedForMonitor(s, s2);
        assert bankedRegsPreservedForMonitor(s2, s3);
        assert bankedRegsPreservedForMonitor(s3, s4);
        assert bankedRegsPreservedForMonitor(s4, s');
    }
}

lemma valEnterImpliesMInv(s:SysState,s':SysState,dispPage:PageNr,
    a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    requires smc_enter(s.d, dispPage,a1,a2,a3).1 == KEV_ERR_SUCCESS()
                && validEnter(s, s', dispPage,a1,a2,a3)
    ensures
        validSysState(s) && validSysState(s') && s'.d == s.d
    ensures
        var p := l1pOfDispatcher(s.d, dispPage);
        validL1PTPage(s.d, p)
        && (validPageDbImpliesWellFormed(s.d); !hasStoppedAddrspace(s.d, p))
        && WSMemInvariantExceptAddrspaceAtPage(s, s', p)
{   
    forall( s2, s3, s4 | validEntryTransitionEnter(s,s2,dispPage,a1,a2,a3) 
        && userspaceExecution(s2, s3)
        && exception(s3, s4)
        && monitorReturn(s4, s') )
        ensures WSMemInvariantExceptAddrspaceAtPage(s, s', 
            l1pOfDispatcher(s.d, dispPage))
    {
        var p := l1pOfDispatcher(s.d, dispPage);
        assert WSMemInvariantExceptAddrspaceAtPage(s,  s2, p);
        assert s2.hw.conf.ttbr0 == p;
        assert WSMemInvariantExceptAddrspaceAtPage(s2, s3, p);
        assert s3.hw.conf.ttbr0 == s2.hw.conf.ttbr0;
        assert s3.hw.conf.ttbr0 == p;
        assert WSMemInvariantExceptAddrspaceAtPage(s3, s4, p);
        assert s4.hw.conf.ttbr0 == p;
        assert WSMemInvariantExceptAddrspaceAtPage(s4, s', p);
        MICommute(s, s2, s3, p);
        MICommute(s, s3, s4, p);
        MICommute(s, s4, s', p);
    }
}

predicate {:opaque} validEnter_premium(s:SysState,s':SysState,dispPage:PageNr,
    a1:int,a2:int,a3:int)
    requires isUInt32(a1) && isUInt32(a2) && isUInt32(a3) && validSysState(s)
    ensures validEnter_premium(s, s', dispPage,a1,a2,a3)
        == validEnter(s, s', dispPage,a1,a2,a3)
    ensures (smc_enter(s.d, dispPage,a1,a2,a3).1 == KEV_ERR_SUCCESS()
             && validEnter(s, s', dispPage,a1,a2,a3)) ==> 
        validSysState(s')
        && bankedRegsPreservedForMonitor(s, s')
        && (var p := l1pOfDispatcher(s.d, dispPage);
            validL1PTPage(s.d, p)
            && (validPageDbImpliesWellFormed(s.d); !hasStoppedAddrspace(s.d, p))
            && WSMemInvariantExceptAddrspaceAtPage(s, s', p))
{
    if(smc_enter(s.d, dispPage,a1,a2,a3).1 == KEV_ERR_SUCCESS() && validEnter(s, s', 
        dispPage,a1,a2,a3)) then
        valEnterImpliesMInv(s, s', dispPage,a1,a2,a3);
        valEnterImpliesBRPres(s, s', dispPage,a1,a2,a3);
        validEnter(s, s', dispPage,a1,a2,a3)
    else
        validEnter(s, s', dispPage,a1,a2,a3)
    
}
*/
