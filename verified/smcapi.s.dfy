include "kom_common.s.dfy"
include "mapping.s.dfy"
include "entry.s.dfy"
include "addrseq.dfy"

predicate allocatePageEntryValid(entry: PageDbEntryTyped)
{
    wellFormedPageDbEntryTyped(entry)
    && ((entry.Dispatcher? && !entry.entered)
        || (entry.L2PTable? && entry.l2pt == SeqRepeat(NR_L2PTES, NoMapping))
        || entry.DataPage?
        || entry.SparePage?)
}

function allocatePage(pageDbIn: PageDb, securePage: word,
    addrspacePage:PageNr, entry:PageDbEntryTyped )
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
    requires validAddrspacePage(pageDbIn, addrspacePage)
    requires allocatePageEntryValid(entry)
    ensures  allocatePage(pageDbIn, securePage, addrspacePage, entry).1 == 
        KOM_ERR_SUCCESS ==> validPageNr(securePage);
{
    reveal validPageDb();
    var addrspace := pageDbIn[addrspacePage].entry;
    if(!validPageNr(securePage)) then (pageDbIn, KOM_ERR_INVALID_PAGENO)
    else if(!pageIsFree(pageDbIn, securePage)) then (pageDbIn, KOM_ERR_PAGEINUSE)
    else if addrspace.state == StoppedState then
        (pageDbIn, KOM_ERR_STOPPED)
    else if addrspace.state == FinalState && !entry.SparePage? then
        (pageDbIn,KOM_ERR_ALREADY_FINAL)
    else
        var updatedAddrspace := addrspace.(refcount := addrspace.refcount + 1);
        var pageDbOut := (pageDbIn[
            securePage := PageDbEntryTyped(addrspacePage, entry)])[
            addrspacePage := pageDbIn[addrspacePage].(entry := updatedAddrspace)];
        (pageDbOut, KOM_ERR_SUCCESS)
}

//============================================================================
// Behavioral Specification of Monitor Calls
//=============================================================================
function smc_query() : int { KOM_MAGIC }

function smc_getPhysPages() : int { KOM_SECURE_NPAGES }

function smc_initAddrspace(pageDbIn: PageDb, addrspacePage: word, l1PTPage: word)
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn);
{
    reveal validPageDb();
    var g := pageDbIn;
    if(!validPageNr(addrspacePage) || !validPageNr(l1PTPage) ||
        addrspacePage == l1PTPage) then
        (pageDbIn, KOM_ERR_INVALID_PAGENO)
    else if(l1PTPage % 4 != 0) then
        (pageDbIn, KOM_ERR_INVALID_PAGENO)
    else if( !g[addrspacePage].PageDbEntryFree? || !g[l1PTPage].PageDbEntryFree? ) then
        (pageDbIn, KOM_ERR_PAGEINUSE)
    else
        var addrspace := Addrspace(l1PTPage, 1, InitState, [], InitialSHA256Trace());
        var l1PT := L1PTable(SeqRepeat(NR_L1PTES,Nothing));
        var pageDbOut := 
            (pageDbIn[addrspacePage := PageDbEntryTyped(addrspacePage, addrspace)])[
                l1PTPage := PageDbEntryTyped(addrspacePage, l1PT)];
        (pageDbOut, KOM_ERR_SUCCESS)
}

function initDispCtxt() : DispatcherContext
    ensures validDispatcherContext(initDispCtxt())
{
    var psr := encode_mode(User);
    assert psr == 0x10;
    assert BitwiseAnd(0x10, 0x1f) == 0x10
        by { reveal_BitAnd(); reveal_WordAsBits(); reveal_BitsAsWord(); }
    assert BitwiseAnd(0x10, 0x40) == 0x00
        by { reveal_BitAnd(); reveal_WordAsBits(); reveal_BitsAsWord(); }
    assert BitwiseAnd(0x10, 0x80) == 0x00
        by { reveal_BitAnd(); reveal_WordAsBits(); reveal_BitsAsWord(); }
    assert psr_mask_mode(psr) == 0x10;
    assert psr_mask_fiq(psr) == 0;
    assert psr_mask_irq(psr) == 0;
    assert decode_mode'(psr_mask_mode(psr)) == Just(User);
    DispatcherContext(
        map[R0 := 0, R1 := 0, R2 := 0, R3 := 0, R4 := 0, R5 := 0, R6 := 0, R7 := 0,
            R8 := 0, R9 := 0, R10 := 0, R11 := 0, R12 := 0, LR(User) := 0,
            SP(User) := 0],
        0, // PC
        psr) // PSR
}

// XXX: this is a workaround for keeping SHA256Trace objects in the pagedb spec
lemma {:axiom} lemma_SHATracesAreEqual(t1:SHA256Trace, t2:SHA256Trace)
    requires IsCompleteSHA256Trace(t1) && SHA256TraceIsCorrect(t1)
    requires IsCompleteSHA256Trace(t2) && SHA256TraceIsCorrect(t2)
    requires ConcatenateSeqs(t1.M) == ConcatenateSeqs(t2.M)
    ensures t1 == t2

// XXX: this is a workaround for keeping SHA256Trace objects in the pagedb spec
lemma {:axiom} lemma_SHATraceExists(measurement:seq<word>)
    requires |measurement| % SHA_BLOCKSIZE == 0
    ensures exists t :: IsCompleteSHA256Trace(t) && SHA256TraceIsCorrect(t)
                && ConcatenateSeqs(t.M) == measurement

function newShaTraceForMeasurement(measurement:seq<word>): SHA256Trace
    requires |measurement| % SHA_BLOCKSIZE == 0
{
    lemma_SHATraceExists(measurement);
    var newshatrace :|
        IsCompleteSHA256Trace(newshatrace) && SHA256TraceIsCorrect(newshatrace)
        && ConcatenateSeqs(newshatrace.M) == measurement;
    newshatrace
}

function updateMeasurement(d: PageDb, addrsp:PageNr, metadata:seq<word>,
                           contents:seq<word>): PageDb
    requires wellFormedPageDb(d) && validAddrspacePage(d, addrsp)
    requires |metadata| <= SHA_BLOCKSIZE
    requires |contents| % SHA_BLOCKSIZE == 0
{
    var padded_metadata := metadata + SeqRepeat(SHA_BLOCKSIZE - |metadata|, 0);
    var newmeasurement := d[addrsp].entry.measurement + padded_metadata + contents;
    d[addrsp := d[addrsp].(entry := d[addrsp].entry.(
        measurement := newmeasurement,
        shatrace := newShaTraceForMeasurement(newmeasurement)))]
}

function smc_initDispatcher(pageDbIn: PageDb, page:word, addrspacePage:word,
    entrypoint:word)
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn);
{
    reveal validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE)
    else
        var initDisp := Dispatcher(entrypoint, false, initDispCtxt(),
                                  [0, 0, 0, 0, 0, 0, 0, 0],
                                  [0, 0, 0, 0, 0, 0, 0, 0]);
        var (pagedb', err) := allocatePage(pageDbIn, page, addrspacePage, initDisp);
        if err == KOM_ERR_SUCCESS then
            (updateMeasurement(pagedb', addrspacePage,
                               [KOM_SMC_INIT_DISPATCHER, entrypoint], []), err)
        else
            (pagedb', err)
}

function smc_initL2PTable(pageDbIn: PageDb, page: word, addrspacePage: word,
                          l1index: word) : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal validPageDb();
    if(!(0<= l1index < NR_L1PTES)) then (pageDbIn, KOM_ERR_INVALID_MAPPING)
    else if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE)

    // This gets caught later in allocatePage, but putting the check
    // here means that the addrspace's state will not be stopped for the
    // l1indexInUse check. The l1indexInUse check assumes that the l1ptnr
    // is actually an l1pt table, which is true as long as the addrspace
    // is not stopped.
    //
    // Proposed change (the enc_ni proofs go through with the following and 
    // without a pair of assumes in initL2PTable):
    // else if(!(pageDbIn[addrspacePage].entry.state == InitState)) then
    else if(pageDbIn[addrspacePage].entry.state == StoppedState) then
        (pageDbIn, KOM_ERR_STOPPED)
    else if(l1indexInUse(pageDbIn, addrspacePage, l1index)) then
        (pageDbIn, KOM_ERR_ADDRINUSE)
    else 
        var l2pt := L2PTable(SeqRepeat(NR_L2PTES, NoMapping));
        // allocate the page
        var (pagedb, err) := allocatePage(pageDbIn, page, addrspacePage, l2pt);
        // update the L1 table
        if err == KOM_ERR_SUCCESS then
            var l1ptnr := pagedb[addrspacePage].entry.l1ptnr;
            (installL1PTEInPageDb(pagedb, l1ptnr, page, l1index), err)
        else
            (pagedb, err)
}

function smc_remove(pageDbIn: PageDb, page: word)
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
{
    reveal validPageDb();
    if(!validPageNr(page)) then
        (pageDbIn, KOM_ERR_INVALID_PAGENO)
    else if(pageDbIn[page].PageDbEntryFree?) then
        (pageDbIn, KOM_ERR_SUCCESS)
    else 
        var e := pageDbIn[page].entry;
        var addrspacePage := pageDbIn[page].addrspace;
        var addrspace := pageDbIn[addrspacePage].entry;
        if( e.Addrspace? ) then
            if(e.refcount !=0) then (pageDbIn, KOM_ERR_PAGEINUSE)
            else (pageDbIn[page := PageDbEntryFree], KOM_ERR_SUCCESS)
        else
            if addrspace.state.InitState?
                || (addrspace.state.FinalState? && !e.SparePage?) then
                (pageDbIn, KOM_ERR_NOT_STOPPED)
            else 
                var d := pageDbIn; var p := page; var a := addrspacePage;
                assert p in addrspaceRefs(d, a);
                var d' := (d[p := PageDbEntryFree])
                        [a := d[a].( entry := d[a].entry.( refcount := 
                            d[a].entry.refcount - 1 ))];
                (d', KOM_ERR_SUCCESS)
}

function smc_mapSecure(pageDbIn: PageDb, page: word, addrspacePage: word,
    mapping: word, physPage: word, contents: Maybe<seq<word>>) : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
    requires physPage == 0 || physPageIsInsecureRam(physPage) ==> contents.Just?
    requires contents.Just? ==> |fromJust(contents)| == PAGESIZE / WORDSIZE
{
    reveal validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE)
    else
        var err := isValidMappingTarget(pageDbIn, addrspacePage, mapping);
        if( err != KOM_ERR_SUCCESS ) then (pageDbIn, err)
        else 
            var abs_mapping := wordToMapping(mapping);
            // Check physPage (which is optionally used to populate
            // the initial contents of the secure page) for validity
            if (physPage != 0 && !physPageIsInsecureRam(physPage)) then
                (pageDbIn, KOM_ERR_INVALID_PAGENO)
            else
                var ap_ret := allocatePage(pageDbIn, page,
                    addrspacePage, DataPage(fromJust(contents)));
                var pageDbA := ap_ret.0;
                var errA := ap_ret.1;
                if(errA != KOM_ERR_SUCCESS) then (pageDbIn, errA)
                else
                    var l2pte := SecureMapping(page, abs_mapping.perm.w, abs_mapping.perm.x);
                    var pageDbB := updateL2Pte(pageDbA, addrspacePage, abs_mapping, l2pte);
                    var pageDbOut := updateMeasurement(pageDbB, addrspacePage,
                               [KOM_SMC_MAP_SECURE, mapping], fromJust(contents));
                    (pageDbOut, KOM_ERR_SUCCESS)
}

function smc_allocSpare(pageDbIn: PageDb, page: word, addrspacePage: word) : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
{
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE)
    else
        allocatePage(pageDbIn, page, addrspacePage, SparePage)
}

function smc_mapInsecure(pageDbIn: PageDb, addrspacePage: word,
    physPage: word, mapping : word) : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE)
    else 
        var err := isValidMappingTarget(pageDbIn, addrspacePage, mapping);
        if( err != KOM_ERR_SUCCESS ) then (pageDbIn, err)
        else if(!physPageIsInsecureRam(physPage)) then
            (pageDbIn, KOM_ERR_INVALID_PAGENO)
        else
            var abs_mapping := wordToMapping(mapping);
            assert validInsecurePageNr(physPage);
            var l2pte := InsecureMapping( physPage,  abs_mapping.perm.w);
            var pageDb' := updateL2Pte(pageDbIn, addrspacePage, abs_mapping, l2pte);
            // FUTURE WORK: also measure insecure mappings
            // var pageDbOut := updateMeasurement(pageDb', addrspacePage,
            //                    [KOM_SMC_MAP_INSECURE, mapping], []);
            // (pageDbOut, KOM_ERR_SUCCESS)
            (pageDb', KOM_ERR_SUCCESS)
}

function smc_finalise(pageDbIn: PageDb, addrspacePage: word) : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal validPageDb();
    var d := pageDbIn; var a := addrspacePage;
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE)
    else if(pageDbIn[addrspacePage].entry.state != InitState) then
        (pageDbIn, KOM_ERR_ALREADY_FINAL)
    else
        var d' := d[ a := d[a].( entry := d[a].entry.( state := FinalState ))];
        (d', KOM_ERR_SUCCESS)
}

function smc_stop(pageDbIn: PageDb, addrspacePage: word)
    : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal validPageDb();
    var d := pageDbIn; var a := addrspacePage;
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE)
    else
        var d' := d[ a := d[a].( entry := d[a].entry.( state := StoppedState ))];
        (d', KOM_ERR_SUCCESS)
}

function contentsOfPhysPage(s: state, physPage: word) : seq<word>
    requires ValidState(s) && SaneConstants()
    requires physPageIsInsecureRam(physPage)
    ensures |contentsOfPhysPage(s, physPage)| == PAGESIZE / WORDSIZE
{
    reveal ValidMemState();
    var base := physPage * PAGESIZE + KOM_DIRECTMAP_VBASE;
    assert |addrRangeSeq(base,base+PAGESIZE)| == PAGESIZE / WORDSIZE;
    addrSeqToContents(addrsInPhysPage(physPage, base), s.m)
}

function maybeContentsOfPhysPage(s: state, physPage: word) : Maybe<seq<word>>
    requires ValidState(s) && SaneConstants()
    ensures var r := maybeContentsOfPhysPage(s, physPage);
        r.Just? ==> |r.v| == PAGESIZE / WORDSIZE
{
    if physPage == 0 then Just(SeqRepeat(PAGESIZE/WORDSIZE, 0))
    else if physPageIsInsecureRam(physPage) then Just(contentsOfPhysPage(s, physPage))
    else Nothing
}

//=============================================================================
// Behavioral Specification of SMC Handler
//=============================================================================
predicate smchandlerRelation(s: state, pageDbIn: PageDb, s':state, pageDbOut: PageDb)
    requires ValidState(s) && validPageDb(pageDbIn) && SaneConstants()
{
    ValidState(s') && (reveal ValidRegState();
    var callno, arg1, arg2, arg3, arg4
        := s.regs[R0], s.regs[R1], s.regs[R2], s.regs[R3], s.regs[R4];
    var err, val := s'.regs[R0], s'.regs[R1];

    if callno == KOM_SMC_QUERY then
        pageDbOut == pageDbIn && err == KOM_MAGIC && val == 0
    else if callno == KOM_SMC_GETPHYSPAGES then
        pageDbOut == pageDbIn && err == KOM_ERR_SUCCESS && val == KOM_SECURE_NPAGES
    else if callno == KOM_SMC_INIT_ADDRSPACE then
        (pageDbOut, err) == smc_initAddrspace(pageDbIn, arg1, arg2) && val == 0
    else if callno == KOM_SMC_INIT_DISPATCHER then
        (pageDbOut, err) == smc_initDispatcher(pageDbIn, arg1, arg2, arg3) && val == 0
    else if callno == KOM_SMC_INIT_L2PTABLE then
        (pageDbOut, err) == smc_initL2PTable(pageDbIn, arg1, arg2, arg3) && val == 0
    else if callno == KOM_SMC_MAP_SECURE then
        var pg := maybeContentsOfPhysPage(s, arg4);
        (pageDbOut, err) == smc_mapSecure(pageDbIn, arg1, arg2, arg3, arg4, pg) && val == 0
    else if callno == KOM_SMC_ALLOC_SPARE then
        (pageDbOut, err) == smc_allocSpare(pageDbIn, arg1, arg2) && val == 0
    else if callno == KOM_SMC_MAP_INSECURE then
        (pageDbOut, err) == smc_mapInsecure(pageDbIn, arg1, arg2, arg3) && val == 0
    else if callno == KOM_SMC_REMOVE then
        (pageDbOut, err) == smc_remove(pageDbIn, arg1) && val == 0
    else if callno == KOM_SMC_FINALISE then
        (pageDbOut, err) == smc_finalise(pageDbIn, arg1) && val == 0
    else if callno == KOM_SMC_ENTER then
        smc_enter(s, pageDbIn, s', pageDbOut, arg1, arg2, arg3, arg4)
    else if callno == KOM_SMC_RESUME then
        smc_resume(s, pageDbIn, s', pageDbOut, arg1)
    else if callno == KOM_SMC_STOP then
        (pageDbOut, err) == smc_stop(pageDbIn, arg1) && val == 0
    else
        pageDbOut == pageDbIn && err == KOM_ERR_INVALID && val == 0)
}

// non-volatile regs preserved
predicate smcNonvolatileRegInvariant(s:state, s':state)
    requires ValidState(s)
{
    reveal ValidRegState();
    ValidState(s')
        && s.regs[R4] == s'.regs[R4] && s.regs[R5] == s'.regs[R5]
        && s.regs[R6] == s'.regs[R6] && s.regs[R7] == s'.regs[R7]
        && s.regs[R8] == s'.regs[R8] && s.regs[R9] == s'.regs[R9]
        && s.regs[R10] == s'.regs[R10] && s.regs[R11] == s'.regs[R11]
        && s.regs[R12] == s'.regs[R12]
}

/* Overall invariant across SMC handler state */
predicate smchandlerInvariant(s:state, s':state, entry:bool)
    requires ValidState(s) && ValidState(s')
{
    reveal ValidRegState();
    reveal ValidSRegState();
    smcNonvolatileRegInvariant(s, s') && s'.regs[R2] == s'.regs[R3] == 0
        // return in non-secure world, in same (i.e., monitor) mode
        && mode_of_state(s') == mode_of_state(s) == Monitor
        && s'.conf.scr.ns == NotSecure
        // return to a non-monitor mode (so we leave secure world)
        && decode_mode(psr_mask_mode(s.sregs[spsr(Monitor)])) != Monitor
        // most banked regs are preserved -- carve-outs for IRQ/FIQ injection 
        && (forall m :: s.regs[SP(m)] == s'.regs[SP(m)])
        && (forall m | m !in {Monitor, IRQ, FIQ} ::
            (m != User ==> s.sregs[spsr(m)] == s'.sregs[spsr(m)])
            && s.regs[LR(m)] == s'.regs[LR(m)])
        && (!entry ==> InsecureMemInvariant(s, s'))
}

predicate smchandler(s: state, pageDbIn: PageDb, s':state, pageDbOut: PageDb)
    requires ValidState(s) && validPageDb(pageDbIn) && SaneConstants()
{
    reveal ValidRegState();
    var entry := s.regs[R0] == KOM_SMC_ENTER || s.regs[R0] == KOM_SMC_RESUME;
    smchandlerRelation(s, pageDbIn, s', pageDbOut) &&
        smchandlerInvariant(s, s', entry)
}
