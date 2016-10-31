include "kom_common.s.dfy"
include "pagedb.s.dfy"
include "entry.s.dfy"

predicate pageIsFree(d:PageDb, pg:PageNr)
{
    pg in d && d[pg].PageDbEntryFree?
}

predicate l1indexInUse(d: PageDb, a: PageNr, l1index: int)
    requires validPageDb(d)
    requires isAddrspace(d, a)
    requires !stoppedAddrspace(d[a])
    requires 0 <= l1index < NR_L1PTES()
{
    reveal_validPageDb();
    assert validAddrspace(d, a);
    var l1ptnr := d[a].entry.l1ptnr;
    var l1pt := d[l1ptnr].entry;
    l1pt.l1pt[l1index].Just?
}

//=============================================================================
// Mapping
//=============================================================================
datatype Mapping = Mapping(l1index: word, l2index: word, perm: Perm)
datatype Perm = Perm(r: bool, w: bool, x: bool)

predicate validMapping(m:Mapping,d:PageDb,a:PageNr)
{
    reveal_validPageDb();
    validPageDb(d) && isAddrspace(d,a) && validAddrspace(d,a) 
    && validPageNr(m.l1index) && 0 <= m.l1index < NR_L1PTES()
    && validPageNr(m.l2index) && 0 <= m.l2index < NR_L2PTES()
    && (var addrspace := d[a].entry;
        addrspace.state == InitState &&
        (var l1 := d[addrspace.l1ptnr].entry;
        l1.l1pt[m.l1index].Just?))
}

function l1indexFromMapping(arg:word) : word
    { RightShift(arg,20) }

function l2indexFromMapping(arg:word) : word
    { BitwiseAnd(RightShift(arg,12),0xff) }

function permFromMapping(arg:word) : Perm
{
    Perm(BitwiseAnd(arg,KOM_MAPPING_R()) != 0,
        BitwiseAnd(arg,KOM_MAPPING_W()) != 0,
        BitwiseAnd(arg,KOM_MAPPING_X()) != 0)
}

function {:opaque} wordToMapping(arg:word) : Mapping
{
    Mapping(l1indexFromMapping(arg),l2indexFromMapping(arg),
        permFromMapping(arg))
}

function updateL2Pte(d: PageDb, a: PageNr, mapping: Mapping, l2e : L2PTE)
    : PageDb 
    requires validPageDb(d)
    requires isAddrspace(d, a)
    requires validMapping(mapping,d,a)
    //requires isValidMappingTarget(d, a, mapping) == KOM_ERR_SUCCESS()
    requires d[a].entry.state.InitState?
    requires validL2PTE(d, a, l2e)
{
    reveal_validPageDb();
    var addrspace := d[a].entry;
    assert validAddrspace(d, a);
    var l1 := d[addrspace.l1ptnr].entry;
    var l1pte := fromJust(l1.l1pt[mapping.l1index]);
    var l2pt := d[l1pte].entry.l2pt;
    d[ l1pte := d[l1pte].( entry := d[l1pte].entry.( l2pt := 
        l2pt[mapping.l2index := l2e] ))]
}

function isValidMappingTarget(d: PageDb, a: PageNr, mapping: word)
    : int // KOM_ERROR
    requires validPageDb(d)
    requires isAddrspace(d, a)
    ensures  isValidMappingTarget(d,a,mapping) == KOM_ERR_SUCCESS() ==>
        validMapping(wordToMapping(mapping),d,a)
{
    reveal_validPageDb();
    reveal_wordToMapping();
    var addrspace := d[a].entry;
    var l1index := l1indexFromMapping(mapping);
    var l2index := l2indexFromMapping(mapping);
    var perm := permFromMapping(mapping);
    if(!addrspace.state.InitState?) then
        KOM_ERR_ALREADY_FINAL()
    else if(!validPageNr(l1indexFromMapping(mapping)) ||
        !validPageNr(l2indexFromMapping(mapping))) then
        KOM_ERR_INVALID_MAPPING()
    else 
        if(!perm.r) then KOM_ERR_INVALID_MAPPING()
        else if(!(0 <= l1index < NR_L1PTES())
            || !(0 <= l2index < NR_L2PTES()) ) then
            KOM_ERR_INVALID_MAPPING()
        else
            assert validAddrspace(d, a);
            var l1 := d[addrspace.l1ptnr].entry;
            var l1pte := l1.l1pt[l1index];
            if(l1pte.Nothing?) then KOM_ERR_INVALID_MAPPING()
            else KOM_ERR_SUCCESS()
}

//============================================================================
// Behavioral Specification of Monitor Calls
//=============================================================================
function smc_query() : int { KOM_MAGIC() }

function smc_getPhysPages() : int { KOM_SECURE_NPAGES() }

function smc_initAddrspace(pageDbIn: PageDb, addrspacePage: word, l1PTPage: word)
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn);
{
    reveal_validPageDb();
    var g := pageDbIn;
    if(!validPageNr(addrspacePage) || !validPageNr(l1PTPage) ||
        addrspacePage == l1PTPage) then
        (pageDbIn, KOM_ERR_INVALID_PAGENO())
    else if(l1PTPage % 4 != 0) then
        (pageDbIn, KOM_ERR_INVALID_PAGENO())
    else if( !g[addrspacePage].PageDbEntryFree? || !g[l1PTPage].PageDbEntryFree? ) then
        (pageDbIn, KOM_ERR_PAGEINUSE())
    else
        var addrspace := Addrspace(l1PTPage, 1, InitState);
        var l1PT := L1PTable(SeqRepeat(NR_L1PTES(),Nothing));
        var pageDbOut := 
            (pageDbIn[addrspacePage := PageDbEntryTyped(addrspacePage, addrspace)])[
                l1PTPage := PageDbEntryTyped(addrspacePage, l1PT)];
        (pageDbOut, KOM_ERR_SUCCESS())
}

function initDispCtxt() : DispatcherContext
    ensures validDispatcherContext(initDispCtxt())
{
    var psr := encode_mode(User);
    assert psr == 0x10;
    assert BitwiseAnd(0x10, 0x1f) == 0x10
        by { reveal_BitAnd(); reveal_WordAsBits(); reveal_BitsAsWord(); }
    assert psr_mask_mode(psr) == 0x10;
    assert decode_mode'(psr_mask_mode(psr)) == Just(User);
    DispatcherContext(
        map[R0 := 0, R1 := 0, R2 := 0, R3 := 0, R4 := 0, R5 := 0, R6 := 0, R7 := 0,
            R8 := 0, R9 := 0, R10 := 0, R11 := 0, R12 := 0, LR(User) := 0,
            SP(User) := 0],
        0, // PC
        psr) // PSR
}

function smc_initDispatcher(pageDbIn: PageDb, page:word, addrspacePage:word,
    entrypoint:word)
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn);
{
    reveal_validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE())
    else
        allocatePage(pageDbIn, page, addrspacePage, Dispatcher(entrypoint, false, initDispCtxt()))
}

function installL1PTE(l1pt: PageDbEntryTyped, l2page: PageNr, l1index: int): PageDbEntryTyped
    requires l1pt.L1PTable? && wellFormedPageDbEntryTyped(l1pt)
    requires 0 <= l1index < NR_L1PTES()
    ensures var r := installL1PTE(l1pt, l2page, l1index);
        r.L1PTable? && wellFormedPageDbEntryTyped(r)
{
    l1pt.(l1pt := l1pt.l1pt[l1index := Just(l2page)])
}

function installL1PTEInPageDb(pagedb: PageDb, l1ptnr: PageNr, l2page: PageNr,
    l1index: int): PageDb
    requires validPageDb(pagedb)
    requires pagedb[l1ptnr].PageDbEntryTyped? && pagedb[l1ptnr].entry.L1PTable?
    requires 0 <= l1index < NR_L1PTES()
    ensures wellFormedPageDb(installL1PTEInPageDb(pagedb, l1ptnr, l2page, l1index))
{
    reveal_validPageDb();
    var l1ptentry := installL1PTE(pagedb[l1ptnr].entry, l2page, l1index);
    pagedb[l1ptnr := pagedb[l1ptnr].(entry := l1ptentry)]
}

function smc_initL2PTable(pageDbIn: PageDb, page: word, addrspacePage: word,
                          l1index: word) : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!(0<= l1index < NR_L1PTES())) then (pageDbIn, KOM_ERR_INVALID_MAPPING())
    else if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE())

    // This gets caught later in allocatePage, but putting the check
    // here means that the addrspace's state will not be stopped for the
    // l1indexInUse check. The l1indexInUse check assumes that the l1ptnr
    // is actually an l1pt table, which is true as long as the addrspace
    // is not stopped.
    else if(pageDbIn[addrspacePage].entry.state != InitState) then
        (pageDbIn, KOM_ERR_ALREADY_FINAL())
    else if(l1indexInUse(pageDbIn, addrspacePage, l1index)) then
        (pageDbIn, KOM_ERR_ADDRINUSE())
    else 
        var l2pt := L2PTable(SeqRepeat(NR_L2PTES(), NoMapping));
        // allocate the page
        var (pagedb, err) := allocatePage(pageDbIn, page, addrspacePage, l2pt);
        // update the L1 table
        if err == KOM_ERR_SUCCESS() then
            var l1ptnr := pagedb[addrspacePage].entry.l1ptnr;
            (installL1PTEInPageDb(pagedb, l1ptnr, page, l1index), err)
        else
            (pagedb, err)
}

predicate allocatePageEntryValid(entry: PageDbEntryTyped)
{
    wellFormedPageDbEntryTyped(entry)
    && ((entry.Dispatcher? && !entry.entered)
        || (entry.L2PTable? && entry.l2pt == SeqRepeat(NR_L2PTES(), NoMapping))
        || entry.DataPage?)
}

// This is not literally an SMC handler. Move elsewhere in file???
function allocatePage_inner(pageDbIn: PageDb, securePage: word,
    addrspacePage:PageNr, entry:PageDbEntryTyped)
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
    requires validAddrspacePage(pageDbIn, addrspacePage)
    requires allocatePageEntryValid(entry)
{
    reveal_validPageDb();
    var addrspace := pageDbIn[addrspacePage].entry;
    if(!validPageNr(securePage)) then (pageDbIn, KOM_ERR_INVALID_PAGENO())
    else if(!pageIsFree(pageDbIn, securePage)) then (pageDbIn, KOM_ERR_PAGEINUSE())
    else if(addrspace.state != InitState) then
        (pageDbIn,KOM_ERR_ALREADY_FINAL())
    // TODO ?? Model page clearing for non-data pages?
    else
        var updatedAddrspace := addrspace.(refcount := addrspace.refcount + 1);
        var pageDbOut := (pageDbIn[
            securePage := PageDbEntryTyped(addrspacePage, entry)])[
            addrspacePage := pageDbIn[addrspacePage].(entry := updatedAddrspace)];
        (pageDbOut, KOM_ERR_SUCCESS())
}

// TODO move this elsewhere since it is not a monitor call
function allocatePage(pageDbIn: PageDb, securePage: word,
    addrspacePage:PageNr, entry:PageDbEntryTyped )
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
    requires validAddrspacePage(pageDbIn, addrspacePage)
    requires allocatePageEntryValid(entry)
    ensures  validPageDb(allocatePage(pageDbIn, securePage, addrspacePage, entry).0);
    ensures  allocatePage(pageDbIn, securePage, addrspacePage, entry).1 == 
        KOM_ERR_SUCCESS() ==> validPageNr(securePage);
{
    reveal_validPageDb();
    allocatePagePreservesPageDBValidity(pageDbIn, securePage, addrspacePage, entry);
    allocatePage_inner(pageDbIn, securePage, addrspacePage, entry)
}


function smc_remove(pageDbIn: PageDb, page: word)
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!validPageNr(page)) then
        (pageDbIn, KOM_ERR_INVALID_PAGENO())
    else if(pageDbIn[page].PageDbEntryFree?) then
        (pageDbIn, KOM_ERR_SUCCESS())
    else 
        var e := pageDbIn[page].entry;
        var addrspacePage := pageDbIn[page].addrspace;
        var addrspace := pageDbIn[addrspacePage].entry;
        if( e.Addrspace? ) then
           if(e.refcount !=0) then (pageDbIn, KOM_ERR_PAGEINUSE())
           else (pageDbIn[page := PageDbEntryFree], KOM_ERR_SUCCESS())
        else 
            if( !addrspace.state.StoppedState?) then
                (pageDbIn, KOM_ERR_NOT_STOPPED())
            else 
                var d := pageDbIn; var p := page; var a := addrspacePage;
                assert p in addrspaceRefs(d, a);
                var d' := (d[p := PageDbEntryFree])
                        [a := d[a].( entry := d[a].entry.( refcount := 
                            d[a].entry.refcount - 1 ))];
                (d', KOM_ERR_SUCCESS())
}

function smc_mapSecure(pageDbIn: PageDb, page: word, addrspacePage: word,
    mapping: word, physPage: word) : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE())
    else 
        var err := isValidMappingTarget(pageDbIn, addrspacePage, mapping);
        if( err != KOM_ERR_SUCCESS() ) then (pageDbIn, err)
        else 
            var abs_mapping := wordToMapping(mapping);
            // Check physPage (which is optionally used to populate
            // the initial contents of the secure page) for validity
            if (physPage != 0 && !physPageIsInsecureRam(physPage)) then
                (pageDbIn, KOM_ERR_INVALID_PAGENO())
            else
                var ap_ret := allocatePage(pageDbIn, page,
                    addrspacePage, DataPage);
                var pageDbA := ap_ret.0;
                var errA := ap_ret.1;
                if(errA != KOM_ERR_SUCCESS()) then (pageDbIn, errA)
                else
                    var l2pte := SecureMapping(page, abs_mapping.perm.w, abs_mapping.perm.x);
                    var pageDbOut := updateL2Pte(pageDbA, addrspacePage, abs_mapping, l2pte);
                    (pageDbOut, KOM_ERR_SUCCESS())
}

function smc_mapInsecure(pageDbIn: PageDb, addrspacePage: word,
    physPage: word, mapping : word) : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE())
    else
        var err := isValidMappingTarget(pageDbIn, addrspacePage, mapping);
        if( err != KOM_ERR_SUCCESS() ) then (pageDbIn, err)
        else if(!physPageIsInsecureRam(physPage)) then
            (pageDbIn, KOM_ERR_INVALID_PAGENO())
        else
            var abs_mapping := wordToMapping(mapping);
            assert validInsecurePageNr(physPage);
            var l2pte := InsecureMapping( physPage,  abs_mapping.perm.w);
            var pageDbOut := updateL2Pte(pageDbIn, addrspacePage, abs_mapping, l2pte);
            (pageDbOut, KOM_ERR_SUCCESS())
}

function smc_finalise(pageDbIn: PageDb, addrspacePage: word) : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    var d := pageDbIn; var a := addrspacePage;
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE())
    else if(pageDbIn[addrspacePage].entry.state != InitState) then
        (pageDbIn, KOM_ERR_ALREADY_FINAL())
    else
        var d' := d[ a := d[a].( entry := d[a].entry.( state := FinalState ))];
        (d', KOM_ERR_SUCCESS())
}

function smc_stop(pageDbIn: PageDb, addrspacePage: word)
    : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    var d := pageDbIn; var a := addrspacePage;
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE())
    else
        var d' := d[ a := d[a].( entry := d[a].entry.( state := StoppedState ))];
        (d', KOM_ERR_SUCCESS())
}

//=============================================================================
// Behavioral Specification of SMC Handler
//=============================================================================
predicate smchandler(s: state, pageDbIn: PageDb, s':state, pageDbOut: PageDb)
    requires ValidState(s) && validPageDb(pageDbIn)
{
    smchandlerInvariant(s, s') &&

    (reveal_ValidRegState();
    var callno, arg1, arg2, arg3, arg4
        := s.regs[R0], s.regs[R1], s.regs[R2], s.regs[R3], s.regs[R4];
    var err, val := s'.regs[R0], s'.regs[R1];

    if callno == KOM_SMC_QUERY() then
        pageDbOut == pageDbIn && err == KOM_MAGIC() && val == 0
    else if callno == KOM_SMC_GETPHYSPAGES() then
        pageDbOut == pageDbIn && err == KOM_ERR_SUCCESS() && val == KOM_SECURE_NPAGES()
    else if callno == KOM_SMC_INIT_ADDRSPACE() then
        (pageDbOut, err) == smc_initAddrspace(pageDbIn, arg1, arg2) && val == 0
    else if callno == KOM_SMC_INIT_DISPATCHER() then
        (pageDbOut, err) == smc_initDispatcher(pageDbIn, arg1, arg2, arg3) && val == 0
    else if callno == KOM_SMC_INIT_L2PTABLE() then
        (pageDbOut, err) == smc_initL2PTable(pageDbIn, arg1, arg2, arg3) && val == 0
    else if callno == KOM_SMC_MAP_SECURE() then
        (pageDbOut, err) == smc_mapSecure(pageDbIn, arg1, arg2, arg3, arg4) && val == 0
    else if callno == KOM_SMC_MAP_INSECURE() then
        (pageDbOut, err) == smc_mapInsecure(pageDbIn, arg1, arg2, arg3) && val == 0
    else if callno == KOM_SMC_REMOVE() then
        (pageDbOut, err) == smc_remove(pageDbIn, arg1) && val == 0
    else if callno == KOM_SMC_FINALISE() then
        (pageDbOut, err) == smc_finalise(pageDbIn, arg1) && val == 0
    else if callno == KOM_SMC_ENTER() then
        smc_enter(s, pageDbIn, s', pageDbOut, arg1, arg2, arg3, arg4)
    else if callno == KOM_SMC_RESUME() then
        smc_resume(s, pageDbIn, s', pageDbOut, arg1)
    else if callno == KOM_SMC_STOP() then
        (pageDbOut, err) == smc_stop(pageDbIn, arg1) && val == 0
    else
        pageDbOut == pageDbIn && err == KOM_ERR_INVALID() && val == 0)
}

// non-volatile regs preserved
predicate nonvolatileRegInvariant(s:state, s':state)
    requires ValidState(s)
{
    reveal_ValidRegState();
    ValidState(s')
        && s.regs[R4] == s'.regs[R4] && s.regs[R5] == s'.regs[R5]
        && s.regs[R6] == s'.regs[R6] && s.regs[R7] == s'.regs[R7]
        && s.regs[R8] == s'.regs[R8] && s.regs[R9] == s'.regs[R9]
        && s.regs[R10] == s'.regs[R10] && s.regs[R11] == s'.regs[R11]
        && s.regs[R12] == s'.regs[R12]
    && OperandContents(s, OSP) == OperandContents(s', OSP)
    && OperandContents(s, OLR) == OperandContents(s', OLR)
}

/* Overall invariant across SMC handler state */
predicate smchandlerInvariant(s:state, s':state)
    requires ValidState(s)
{
    reveal_ValidRegState();
    reveal_ValidConfig();
    ValidState(s') && nonvolatileRegInvariant(s, s')
        // all banked regs, including SPSR and LR (our return target) are preserved
        // TODO: we may need to weaken this to reason about IRQ/FIQ injection.
        && forall m :: ((m == User || s.conf.spsr[m] == s'.conf.spsr[m]) // (no User SPSR)
                && s.regs[LR(m)] == s'.regs[LR(m)]
                && s.regs[SP(m)] == s'.regs[SP(m)])
        // return in non-secure world, in same (i.e., monitor) mode
        && mode_of_state(s') == mode_of_state(s)
        && s'.conf.scr == SCR(NotSecure, false, false)
}

// lemma for allocatePage; FIXME: not trusted, should not be in a .s.dfy file
lemma allocatePagePreservesPageDBValidity(pageDbIn: PageDb,
    securePage: word, addrspacePage: PageNr, entry: PageDbEntryTyped)
    requires validPageDb(pageDbIn)
    requires validAddrspacePage(pageDbIn, addrspacePage)
    requires allocatePageEntryValid(entry)
    ensures  validPageDb(allocatePage_inner(
        pageDbIn, securePage, addrspacePage, entry).0);
{
    reveal_validPageDb();
    assert validAddrspace(pageDbIn, addrspacePage);
    var result := allocatePage_inner(pageDbIn, securePage, addrspacePage, entry);
    var pageDbOut := result.0;
    var errOut := result.1;

    if ( errOut != KOM_ERR_SUCCESS() ){
        // The error case is trivial because PageDbOut == PageDbIn
    } else {
        forall () ensures validPageDbEntry(pageDbOut, addrspacePage);
        {
            var oldRefs := addrspaceRefs(pageDbIn, addrspacePage);
            assert addrspaceRefs(pageDbOut, addrspacePage ) == oldRefs + {securePage};
            
            var addrspace := pageDbOut[addrspacePage].entry;
            assert addrspace.refcount == |addrspaceRefs(pageDbOut, addrspacePage)|;
            assert validAddrspacePage(pageDbOut, addrspacePage);
        }

        forall ( n | validPageNr(n) && n != addrspacePage && n != securePage )
            ensures validPageDbEntry(pageDbOut, n)
        {
            assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
            assert validPageDbEntry(pageDbIn, n) && validPageDbEntry(pageDbOut, n);
        }

        assert pageDbEntriesValid(pageDbOut);
        assert validPageDb(pageDbOut);
    }
}
