include "smcapi.s.dfy"
include "entry.i.dfy"

//=============================================================================
// Hoare Specification of Monitor Calls
//=============================================================================
function {:opaque} smc_initAddrspace_premium(pageDbIn: PageDb, addrspacePage: word,
    l1PTPage: word) : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn);
    ensures  validPageDb(smc_initAddrspace_premium(pageDbIn, addrspacePage, l1PTPage).0);
{
    initAddrspacePreservesPageDBValidity(pageDbIn, addrspacePage, l1PTPage);
    smc_initAddrspace(pageDbIn, addrspacePage, l1PTPage)
}

function {:opaque} smc_initDispatcher_premium(pageDbIn: PageDb, page:word,
    addrspacePage:word, entrypoint:word) : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn);
    ensures  validPageDb(smc_initDispatcher_premium(pageDbIn, page, addrspacePage, entrypoint).0);
{
    reveal_validPageDb();
    smc_initDispatcher(pageDbIn, page, addrspacePage, entrypoint)
}

function {:opaque} smc_initL2PTable_premium(pageDbIn: PageDb, page: word,
    addrspacePage: word, l1index: word) : (PageDb, word)
    requires validPageDb(pageDbIn)
    ensures validPageDb(smc_initL2PTable_premium(pageDbIn, page, addrspacePage, l1index).0)
{
    initL2PTablePreservesPageDBValidity(pageDbIn, page, addrspacePage, l1index);
    smc_initL2PTable(pageDbIn, page, addrspacePage, l1index)
}

function {:opaque} smc_remove_premium(pageDbIn: PageDb, page: word)
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_remove_premium(pageDbIn, page).0)
{
    removePreservesPageDBValidity(pageDbIn, page);
    smc_remove(pageDbIn, page)
}

function {:opaque} smc_mapSecure_premium(pageDbIn: PageDb, page: word,
    addrspacePage: word, mapping: word, physPage: word, contents: Maybe<seq<word>>) : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
    requires physPage == 0 || physPageIsInsecureRam(physPage) ==> contents.Just?
    requires contents.Just? ==> |fromJust(contents)| == PAGESIZE / WORDSIZE
    ensures  validPageDb(smc_mapSecure_premium(pageDbIn, page, addrspacePage, 
        mapping, physPage, contents).0)
    ensures  smc_mapSecure_premium(pageDbIn, page, addrspacePage, mapping, physPage, contents) ==
        smc_mapSecure(pageDbIn, page, addrspacePage, mapping, physPage,  contents);
{
    mapSecurePreservesPageDBValidity(pageDbIn, page, addrspacePage, mapping, 
        physPage, contents);
    smc_mapSecure(pageDbIn, page, addrspacePage, mapping, physPage, contents)
}

function {:opaque} smc_mapInsecure_premium(pageDbIn: PageDb, addrspacePage: word,
    physPage: word, mapping : word) : (PageDb, word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_mapInsecure_premium(pageDbIn, addrspacePage, physPage, mapping).0)
    ensures smc_mapInsecure_premium(pageDbIn, addrspacePage, physPage, mapping) ==
        smc_mapInsecure(pageDbIn, addrspacePage, physPage, mapping) 
{
    mapInsecurePreservesPageDbValidity(pageDbIn, addrspacePage, physPage, mapping);
    smc_mapInsecure(pageDbIn, addrspacePage, physPage, mapping)
}

function {:opaque} smc_finalise_premium(pageDbIn: PageDb, addrspacePage: word)
    : (PageDb, word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_finalise_premium(pageDbIn, addrspacePage).0)
{
    finalisePreservesPageDbValidity(pageDbIn, addrspacePage);
    smc_finalise(pageDbIn, addrspacePage)
}

function {:opaque} smc_stop_premium(pageDbIn: PageDb, addrspacePage: word)
    : (PageDb, word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_stop_premium(pageDbIn, addrspacePage).0)
{
    stopPreservesPageDbValidity(pageDbIn, addrspacePage);
    smc_stop(pageDbIn, addrspacePage)
}

//=============================================================================
// Properties of Monitor Calls
//=============================================================================

//-----------------------------------------------------------------------------
// PageDb Validity Preservation
//-----------------------------------------------------------------------------
lemma initAddrspacePreservesPageDBValidity(pageDbIn : PageDb,
    addrspacePage : word, l1PTPage : word)
    requires validPageDb(pageDbIn)
    ensures validPageDb(smc_initAddrspace(pageDbIn, addrspacePage, l1PTPage).0)
{
    reveal_validPageDb();
    var result := smc_initAddrspace(pageDbIn, addrspacePage, l1PTPage);
    var pageDbOut := result.0;
    var errOut := result.1;

    if( errOut != KOM_ERR_SUCCESS ) {
        // The error case is trivial because PageDbOut == PageDbIn
    } else {
        // Necessary semi-manual proof of validPageDbEntry(pageDbOut, l1PTPage)
        // The interesting part of the proof deals with the contents of addrspaceRefs
        assert forall p :: p != l1PTPage ==> !(p in addrspaceRefs(pageDbOut, addrspacePage));
	      assert l1PTPage in addrspaceRefs(pageDbOut, addrspacePage);
        assert addrspaceRefs(pageDbOut, addrspacePage) == {l1PTPage};
        // only kept for readability
        assert validPageDbEntry(pageDbOut, l1PTPage);

        forall ( n | validPageNr(n)
            && n != addrspacePage && n != l1PTPage)
            ensures validPageDbEntry(pageDbOut, n)
        {
            assert pageDbOut[n] == pageDbIn[n];
            assert validPageDbEntry(pageDbIn, n);
            assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
        }
              
        assert pageDbEntriesValid(pageDbOut);
        assert validPageDb(pageDbOut);
    }
}

lemma installL1PTEPreservesPageDbValidity(pageDbIn: PageDb, l1ptnr: PageNr,
                                          l2page: PageNr, l1index: int)
    requires validPageDb(pageDbIn)
    requires pageDbIn[l1ptnr].PageDbEntryTyped? && pageDbIn[l1ptnr].entry.L1PTable?
    // l2page belongs to this addrspace
    requires validL1PTE(pageDbIn, l2page)
        && pageDbIn[l2page].addrspace == pageDbIn[l1ptnr].addrspace
    // no double mapping
    requires forall i :: 0 <= i < NR_L1PTES && i != l1index
        ==> pageDbIn[l1ptnr].entry.l1pt[i] != Just(l2page)
    requires 0 <= l1index < NR_L1PTES
    ensures validPageDb(installL1PTEInPageDb(pageDbIn, l1ptnr, l2page, l1index))
{
    reveal_validPageDb();

    assert validL1PTable(pageDbIn, l1ptnr);
    var pageDbOut := installL1PTEInPageDb(pageDbIn, l1ptnr, l2page, l1index);

    assert validL1PTable(pageDbOut, l1ptnr);

    forall ( n | validPageNr(n) && n != l1ptnr)
        ensures validPageDbEntry(pageDbOut, n)
    {
        assert pageDbOut[n] == pageDbIn[n];
        assert validPageDbEntry(pageDbIn, n);
        assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
    }
}

lemma initL2PTablePreservesPageDBValidity(pageDbIn: PageDb, page: word,
    addrspacePage: word, l1index: word)
    requires validPageDb(pageDbIn)
    ensures validPageDb(smc_initL2PTable(pageDbIn, page, addrspacePage, l1index).0)
{
    reveal_validPageDb();
    var (pageDbOut, errOut)
        := smc_initL2PTable(pageDbIn, page, addrspacePage, l1index);
    if( errOut != KOM_ERR_SUCCESS ) {
        // trivial
    } else {
        var l1ptnr := pageDbIn[addrspacePage].entry.l1ptnr;
        var l1pt := pageDbIn[l1ptnr].entry.l1pt;
        // no refs to the free page
        forall (i | 0 <= i < NR_L1PTES)
            ensures l1pt[i] != Just(page)
        {
            assert pageIsFree(pageDbIn, page);
            assert !stoppedAddrspace(pageDbIn[addrspacePage]);
            assert validL1PTable(pageDbIn, l1ptnr);
            assert l1pt[i].Just? ==> validL1PTE(pageDbIn, fromJust(l1pt[i]));
        }
        assert forall i :: 0 <= i < NR_L1PTES
        ==> pageDbIn[l1ptnr].entry.l1pt[i] != Just(page);
        var l2pt := L2PTable(SeqRepeat(NR_L2PTES, NoMapping));
        var pageDbTmp := allocatePage(pageDbIn, page, addrspacePage, l2pt).0;
        installL1PTEPreservesPageDbValidity(pageDbTmp, l1ptnr, page, l1index);
    }
}

lemma removePreservesPageDBValidity(pageDbIn: PageDb, page: word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_remove(pageDbIn, page).0)
{
    reveal_validPageDb();
    var result := smc_remove(pageDbIn, page);
    var pageDbOut := result.0;
    var errOut := result.1;

    if ( errOut != KOM_ERR_SUCCESS ){
       // trivial
    } else if( pageDbIn[page].PageDbEntryFree?) {
        // trivial
    } else {

        var entry := pageDbIn[page].entry;
        var addrspacePage := pageDbIn[page].addrspace;
        assert validAddrspace(pageDbIn, addrspacePage);

        forall () ensures validPageDbEntry(pageDbOut, addrspacePage);
        {
            if(entry.Addrspace?){
            } else {
                var addrspace := pageDbOut[addrspacePage].entry;

                var oldRefs := addrspaceRefs(pageDbIn, addrspacePage);
                assert addrspaceRefs(pageDbOut, addrspacePage) == oldRefs - {page};
                assert addrspace.refcount == |addrspaceRefs(pageDbOut, addrspacePage)|;
                
                //assert validAddrspace(pageDbOut, addrspace);
                assert validAddrspacePage(pageDbOut, addrspacePage);
            }
        }

        assert validPageDbEntry(pageDbOut, page);

        forall ( n | validPageNr(n) && n != addrspacePage && n != page )
            ensures validPageDbEntry(pageDbOut, n)
        {
            if(pageDbOut[n].PageDbEntryFree?) {
                // trivial
            } else {
                var e := pageDbOut[n].entry;
                var d := pageDbOut;
                var a := pageDbOut[n].addrspace;

                assert pageDbOut[n] == pageDbIn[n];

                
                forall () ensures validPageDbEntryTyped(d, n){
                  
                    // This is a proof that the addrspace of n is still an addrspace
                    //
                    // The only interesting case is when the page that was
                    // removed is the addrspace of n (i.e. a == page). This
                    // case causes an error because a must have been valid in
                    // pageDbIn and therefore n has a reference to it.
                    forall() ensures a in d && d[a].PageDbEntryTyped?
                        && d[a].entry.Addrspace?;
                    {
                        assert a == page ==> n in addrspaceRefs(pageDbIn, a);
                        assert a == page ==> pageDbIn[a].entry.refcount > 0;
                        assert a != page;
                    }

                    if( a == addrspacePage ) {
                        var oldRefs := addrspaceRefs(pageDbIn, addrspacePage);
                        assert addrspaceRefs(pageDbOut, addrspacePage) == oldRefs - {page};
                        assert pageDbOut[a].entry.refcount == |addrspaceRefs(pageDbOut, addrspacePage)|;
                    } else {
                        assert pageDbOut[a].entry.refcount == pageDbIn[a].entry.refcount;
                        assert addrspaceRefs(pageDbIn, a) == addrspaceRefs(pageDbOut, a);
                    }

                }

            }
        }

        assert pageDbEntriesValid(pageDbOut);
        assert validPageDb(pageDbOut);
    }
}

lemma mapSecurePreservesPageDBValidity(pageDbIn: PageDb, page: word,
    addrspacePage: word, map_word: word, physPage: word, contents: Maybe<seq<word>>)
    requires validPageDb(pageDbIn)
    requires physPage == 0 || physPageIsInsecureRam(physPage) ==> contents.Just?
    requires contents.Just? ==> |fromJust(contents)| == PAGESIZE / WORDSIZE
    ensures  validPageDb(smc_mapSecure(pageDbIn, page, addrspacePage,
        map_word, physPage, contents).0)
{
    reveal_validPageDb();
    var mapping := wordToMapping(map_word);
    var pageDbOut := smc_mapSecure(
        pageDbIn, page, addrspacePage, map_word, physPage, contents).0;
    var err := smc_mapSecure(
        pageDbIn, page, addrspacePage, map_word, physPage, contents).1;

    if( err != KOM_ERR_SUCCESS ){
    } else {
        assert validPageDbEntryTyped(pageDbOut, page);
        var pageDbA := allocatePage(pageDbIn, page,
            addrspacePage, DataPage(fromJust(contents))).0;

        forall( n | validPageNr(n) && n != page
            && pageDbOut[n].PageDbEntryTyped?)
            ensures validPageDbEntryTyped(pageDbOut, n);
        {
            if( pageDbOut[n].entry.Addrspace? ){
                assert pageDbOut[n].entry.refcount == pageDbA[n].entry.refcount;
                assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbA, n);
            } else if (pageDbOut[n].entry.L2PTable?) {
                var addrspace := pageDbIn[addrspacePage].entry;
                var l1 := pageDbIn[addrspace.l1ptnr].entry;
                var l1pte := fromJust(l1.l1pt[mapping.l1index]);
                var l2pt := pageDbOut[n].entry.l2pt;
                if (n == l1pte) {
                    forall i | 0 <= i < |l2pt|
                        ensures validL2PTE(pageDbOut, addrspacePage, l2pt[i])
                    {
                        if (i == mapping.l2index) {
                            assert validL2PTE(pageDbOut, addrspacePage, l2pt[i]);
                        } else {
                            assert validL2PTable(pageDbIn, n);
                            assert validL2PTE(pageDbIn, addrspacePage, l2pt[i]);
                            assert l2pt[i] == pageDbIn[n].entry.l2pt[i];
                            assert validL2PTE(pageDbOut, addrspacePage, l2pt[i]);
                        }
                    }
                    assert validL2PTable(pageDbOut, n);
                }
            }
        }
    }

}

lemma mapInsecurePreservesPageDbValidity(pageDbIn: PageDb, addrspacePage: word,
    physPage: word, map_word: word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_mapInsecure(pageDbIn, addrspacePage, physPage, 
        map_word).0)
{
    reveal_validPageDb();
    var mapping := wordToMapping(map_word);
    var pageDbOut := smc_mapInsecure(
        pageDbIn, addrspacePage, physPage, map_word).0;
    var err := smc_mapInsecure(
        pageDbIn, addrspacePage, physPage, map_word).1;

    if( err != KOM_ERR_SUCCESS ){
    } else {        
        forall( n | validPageNr(n) && pageDbOut[n].PageDbEntryTyped?)
            ensures validPageDbEntryTyped(pageDbOut, n);
        {
            if( pageDbOut[n].entry.Addrspace? ){
                assert pageDbOut[n].entry.refcount == pageDbIn[n].entry.refcount;
                assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
            } else if (pageDbOut[n].entry.L2PTable?) {
                var addrspace := pageDbIn[addrspacePage].entry;
                var l1 := pageDbIn[addrspace.l1ptnr].entry;
                var l1pte := fromJust(l1.l1pt[mapping.l1index]);
                var l2pt := pageDbOut[n].entry.l2pt;
                if (n == l1pte) {
                    forall i | 0 <= i < |l2pt|
                        ensures validL2PTE(pageDbOut, addrspacePage, l2pt[i])
                    {
                        if (i == mapping.l2index) {
                            assert validL2PTE(pageDbOut, addrspacePage, l2pt[i]);
                        } else {
                            assert validL2PTable(pageDbIn, n);
                            assert validL2PTE(pageDbIn, addrspacePage, l2pt[i]);
                            assert l2pt[i] == pageDbIn[n].entry.l2pt[i];
                            assert validL2PTE(pageDbOut, addrspacePage, l2pt[i]);
                        }
                    }
                    assert validL2PTable(pageDbOut, n);
                }
            }
        }
    }
}

lemma finalisePreservesPageDbValidity(pageDbIn: PageDb, addrspacePage: word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_finalise(pageDbIn, addrspacePage).0)
{
    reveal_validPageDb();
    var pageDbOut := smc_finalise(pageDbIn, addrspacePage).0;
    var err := smc_finalise(pageDbIn, addrspacePage).1;

    if( err != KOM_ERR_SUCCESS ){
    } else {
        var a := addrspacePage;
        assert pageDbOut[a].entry.refcount == pageDbIn[a].entry.refcount;
        assert addrspaceRefs(pageDbOut, a) == addrspaceRefs(pageDbIn, a);

        forall ( n | validPageNr(n) 
            && pageDbOut[n].PageDbEntryTyped?
            && n != a )
            ensures validPageDbEntry(pageDbOut, n)
        {
            if( pageDbOut[n].entry.Addrspace? ){
                assert pageDbOut[n].entry.refcount == pageDbIn[n].entry.refcount;
                assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
            } else {
            }

        }
    }
}

lemma lemma_userspaceExecutionAndException_spsr(s:state, r:state)
    requires ValidState(s) && userspaceExecutionAndException(s, r)
    ensures mode_of_state(r) != User && spsr_of_state(r).m == User
{
    assert ValidOperand(OLR);
    reveal_userspaceExecutionAndException();
    assert ExtractAbsPageTable(s).Just?;
    var s', s2 :| equivStates(s, s')
        && evalEnterUserspace(s', s2)
        && (var (s3, expc, ex) := userspaceExecutionFn(s2, OperandContents(s, OLR));
            evalExceptionTaken(s3, ex, expc, r));
    var (s3, expc, ex) := userspaceExecutionFn(s2, OperandContents(s, OLR));
    assert mode_of_state(s3) == User by { reveal_userspaceExecutionFn(); }
    lemma_evalExceptionTaken_Mode(s3, ex, expc, r);
}

lemma lemma_validEnclaveExecutionStep_validPageDb(s1:state, d1:PageDb,
    rs:state, rd:PageDb, dispPg:PageNr, retToEnclave:bool)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires nonStoppedDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s1, d1, rs, rd, dispPg, retToEnclave)
    ensures validPageDb(rd)
    ensures nonStoppedDispatcher(rd, dispPg)
{
    reveal_validEnclaveExecutionStep();
    reveal_updateUserPagesFromState();

    if retToEnclave {
        var s4 :| userspaceExecutionAndException(s1, s4)
            && rd == updateUserPagesFromState(s4, d1, dispPg);
    } else {
        var s4, d4 :| userspaceExecutionAndException(s1, s4)
            && d4 == updateUserPagesFromState(s4, d1, dispPg)
            && rd == exceptionHandled(s4, d4, dispPg).2;
        lemma_userspaceExecutionAndException_spsr(s1, s4);
        lemma_exceptionHandled_validPageDb(s4, d4, dispPg);
        assert nonStoppedDispatcher(rd, dispPg);
    }
}

lemma lemma_validEnclaveExecution(s1:state, d1:PageDb,
    rs:state, rd:PageDb, dispPg:PageNr, steps:nat)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires nonStoppedDispatcher(d1, dispPg)
    requires validEnclaveExecution(s1, d1, rs, rd, dispPg, steps)
    ensures validPageDb(rd)
    decreases steps
{
    reveal_validEnclaveExecution();
    var retToEnclave := (steps > 0);
    var s5, d5 :|
        validEnclaveExecutionStep(s1, d1, s5, d5, dispPg, retToEnclave)
        && if retToEnclave then
        (lemma_validEnclaveExecutionStep_validPageDb(s1, d1, s5, d5, dispPg, retToEnclave);
        validEnclaveExecution(s5, d5, rs, rd, dispPg, steps - 1))
        else rd == d5;

    if retToEnclave {
        lemma_validEnclaveExecution(s5, d5, rs, rd, dispPg, steps - 1);
    }
}

lemma enterPreservesPageDbValidity(s:state, pageDbIn: PageDb, s':state,
    pageDbOut: PageDb, dispPage: word, arg1: word, arg2: word, arg3: word)
    requires ValidState(s) && validPageDb(pageDbIn) && ValidState(s')
    requires SaneConstants()
    requires smc_enter(s, pageDbIn, s', pageDbOut, dispPage, arg1, arg2, arg3)
    ensures validPageDb(pageDbOut)
{
    if (smc_enter_err(pageDbIn, dispPage, false) == KOM_ERR_SUCCESS) {
        var s1, steps:nat :|
            preEntryEnter(s, s1, pageDbIn, dispPage, arg1, arg2, arg3)
            && validEnclaveExecution(s1, pageDbIn, s', pageDbOut, dispPage, steps);
        lemma_validEnclaveExecution(s1, pageDbIn, s', pageDbOut, dispPage, steps);
    }
}

lemma resumePreservesPageDbValidity(s:state, pageDbIn: PageDb, s':state,
                                    pageDbOut: PageDb, dispPage: word)
    requires ValidState(s) && validPageDb(pageDbIn) && ValidState(s')
    requires SaneConstants()
    requires smc_resume(s, pageDbIn, s', pageDbOut, dispPage)
    ensures validPageDb(pageDbOut)
{
    if (smc_enter_err(pageDbIn, dispPage, true) == KOM_ERR_SUCCESS) {
        var s1, steps:nat :|
            preEntryResume(s, s1, pageDbIn, dispPage)
            && validEnclaveExecution(s1, pageDbIn, s', pageDbOut, dispPage, steps);
        lemma_validEnclaveExecution(s1, pageDbIn, s', pageDbOut, dispPage, steps);
    }
}

lemma stopPreservesPageDbValidity(pageDbIn: PageDb, addrspacePage: word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_stop(pageDbIn, addrspacePage).0)
{
    reveal_validPageDb();
    var pageDbOut := smc_stop(pageDbIn, addrspacePage).0;
    var err := smc_stop(pageDbIn, addrspacePage).1;

    if( err != KOM_ERR_SUCCESS ){
    } else {
        var a := addrspacePage;
        assert pageDbOut[a].entry.refcount == pageDbIn[a].entry.refcount;
        assert addrspaceRefs(pageDbOut, a) == addrspaceRefs(pageDbIn, a);

        forall ( n | validPageNr(n) 
            && pageDbOut[n].PageDbEntryTyped?
            && n != a )
            ensures validPageDbEntry(pageDbOut, n)
        {
            if( pageDbOut[n].entry.Addrspace? ){
                assert pageDbOut[n].entry.refcount == pageDbIn[n].entry.refcount;
                assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
            } else {
            }

        }

    }
}

lemma lemma_allocatePage_preservesMappingGoodness(
    pageDbIn:PageDb,securePage:word,
    addrspacePage:PageNr,entry:PageDbEntryTyped,pageDbOut:PageDb,err:word,
    abs_mapping:word)
    requires validPageDb(pageDbIn)
    requires validAddrspacePage(pageDbIn, addrspacePage)
    requires allocatePageEntryValid(entry)
    requires (pageDbOut, err) == allocatePage(pageDbIn,securePage,
        addrspacePage,entry)
    requires isValidMappingTarget(pageDbIn,addrspacePage,abs_mapping) ==
        KOM_ERR_SUCCESS;
    ensures isValidMappingTarget(pageDbOut,addrspacePage,abs_mapping) ==
        KOM_ERR_SUCCESS;
    ensures validPageDb(pageDbOut)
{
    reveal_validPageDb();
}


lemma smchandlerPreservesPageDbValidity(s: state, pageDbIn: PageDb, s':state,
    pageDbOut: PageDb)
    requires ValidState(s) && validPageDb(pageDbIn) && SaneConstants()
    requires smchandler(s, pageDbIn, s', pageDbOut)
    ensures validPageDb(pageDbOut)
{
    reveal_ValidRegState();
    var callno, arg1, arg2, arg3, arg4
        := s.regs[R0], s.regs[R1], s.regs[R2], s.regs[R3], s.regs[R4];
    var err, val := s'.regs[R0], s'.regs[R1];

    reveal_validPageDb();

    if (callno == KOM_SMC_INIT_ADDRSPACE) {
        initAddrspacePreservesPageDBValidity(pageDbIn, arg1, arg2);
    } else if(callno == KOM_SMC_INIT_DISPATCHER) {
    } else if(callno == KOM_SMC_INIT_L2PTABLE) {
        initL2PTablePreservesPageDBValidity(pageDbIn, arg1, arg2, arg3);
    } else if(callno == KOM_SMC_MAP_SECURE) {
        var pg := maybeContentsOfPhysPage(s, arg4);
        mapSecurePreservesPageDBValidity(pageDbIn, arg1, arg2, arg3, arg4, pg);
    } else if(callno == KOM_SMC_MAP_INSECURE) {
        mapInsecurePreservesPageDbValidity(pageDbIn, arg1, arg2, arg3);
    } else if(callno == KOM_SMC_REMOVE) {
        removePreservesPageDBValidity(pageDbIn, arg1);
    } else if(callno == KOM_SMC_FINALISE) {
        finalisePreservesPageDbValidity(pageDbIn, arg1);
    } else if(callno == KOM_SMC_ENTER) {
        enterPreservesPageDbValidity(s, pageDbIn, s', pageDbOut, arg1, arg2, arg3, arg4);
    } else if(callno == KOM_SMC_RESUME) {
        resumePreservesPageDbValidity(s, pageDbIn, s', pageDbOut, arg1);
    } else if(callno == KOM_SMC_STOP) {
        stopPreservesPageDbValidity(pageDbIn, arg1);
    }
}

lemma lemma_updateL2PtePreservesPageDb(d:PageDb,a:PageNr,mapping:Mapping,l2e:L2PTE) 
    requires validPageDb(d)
    requires isAddrspace(d, a)
    requires validMapping(mapping,d,a)
    requires d[a].entry.state.InitState?
    requires validL2PTE(d,a,l2e)
    ensures validPageDb(updateL2Pte(d,a,mapping,l2e))
{
    reveal_validPageDb();
    var d' := updateL2Pte(d,a,mapping,l2e);
    
    var addrspace := d[a].entry;
    assert validAddrspace(d, a);

    var l2index := mapping.l2index;
    var l1index := mapping.l1index;

    var l1p := d[a].entry.l1ptnr;
    var l1 := d[l1p].entry;
    var l1p' := d'[a].entry.l1ptnr;
    var l1' := d'[l1p'].entry;
    assert l1p' == l1p;
    assert l1' == l1;

    var l1pte := fromJust(l1.l1pt[l1index]);
    var l1pte' := fromJust(l1'.l1pt[l1index]);
    assert l1pte == l1pte';
    var l2pt := d[l1pte].entry.l2pt;
    var l2pt' := d'[l1pte].entry.l2pt;

    //it's now okay to drop the primes from everything but l2pt'

    assert !stoppedAddrspace(d[a]);
    assert !stoppedAddrspace(d'[a]);

    assert validPageDbEntry(d, a);
    assert validPageDbEntry(d', a) by
    {
        assert d'[a].entry.refcount == d[a].entry.refcount;
        assert addrspaceRefs(d', a) == addrspaceRefs(d, a);
        
    }

    assert validPageDbEntry(d, l1p);
    assert validPageDbEntry(d, l1pte);

    assert validPageDbEntry(d', l1p);
    assert validPageDbEntry(d', l1pte) by
    {
       assert d'[l1pte].entry.L2PTable?;
       assert !stoppedAddrspace(d'[a]);
       assert validL2PTE(d',a,l2e);
       assert wellFormedPageDbEntryTyped(d[l1pte].entry);
       assert wellFormedPageDbEntryTyped(d'[l1pte].entry);

       assert |l2pt| == |l2pt'|;

       forall ( i | 0 <= i < NR_L2PTES && i != l2index )
            ensures validL2PTE(d',a,l2pt'[i])
       {
            assert l2pt'[i] == l2pt[i];
            assert validL2PTE(d,a,l2pt[i]);
       }

    }

    forall ( p | validPageNr(p) && p != l1p && p != l1pte && p != a )
        ensures validPageDbEntry(d', p)
    {
            assert d'[p] == d[p];
            assert validPageDbEntry(d, p);
            assert addrspaceRefs(d', p) == addrspaceRefs(d, p);
    }
    
    assert wellFormedPageDb(d');
    assert pageDbEntriesValid(d');
    assert pageDbEntriesValidRefs(d');
  
}
