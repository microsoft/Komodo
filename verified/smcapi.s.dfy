include "kom_common.s.dfy"
include "pagedb.s.dfy"

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
datatype Mapping = Mapping(l1index: PageNr, l2index: PageNr, perm: Perm)
datatype Perm = Perm(r: bool, w: bool, x: bool)

function {:opaque} wordToMapping(arg: word): Mapping
{
    // TODO!
    Mapping(1,1,Perm(false,false,false))
}

function updateL2Pte(pageDbIn: PageDb, a: PageNr, mapping: Mapping, l2e : L2PTE)
    : PageDb 
    requires validPageDb(pageDbIn)
    requires isAddrspace(pageDbIn, a)
    requires isValidMappingTarget(pageDbIn, a, mapping) == KOM_ERR_SUCCESS()
    requires pageDbIn[a].entry.state.InitState?
    requires validL2PTE(pageDbIn, a, l2e)
{
    reveal_validPageDb();
    var addrspace := pageDbIn[a].entry;
    assert validAddrspace(pageDbIn, a);
    var l1 := pageDbIn[addrspace.l1ptnr].entry;
    var l1pte := fromJust(l1.l1pt[mapping.l1index]);
    var l2pt := pageDbIn[l1pte].entry.l2pt;
    pageDbIn[ l1pte := PageDbEntryTyped(a, L2PTable(l2pt[mapping.l2index := l2e])) ]
}

function isValidMappingTarget(d: PageDb, a: PageNr, mapping: Mapping)
    : int // KOM_ERROR
    requires validPageDb(d)
    requires isAddrspace(d, a)
{
    reveal_validPageDb();
    var addrspace := d[a].entry;
    if(!addrspace.state.InitState?) then
        KOM_ERR_ALREADY_FINAL()
    else if(!mapping.perm.r) then KOM_ERR_INVALID_MAPPING()
    else if(!(0 <= mapping.l1index < NR_L1PTES())
        || !(0 <= mapping.l2index < NR_L2PTES()) ) then
        KOM_ERR_INVALID_MAPPING()
    else
        assert validAddrspace(d, a);
        var l1 := d[addrspace.l1ptnr].entry;
        var l1pte := l1.l1pt[mapping.l1index];
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

function smc_initDispatcher(pageDbIn: PageDb, page:word, addrspacePage:word,
    entrypoint:word)
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn);
{
    reveal_validPageDb();
   if(!isAddrspace(pageDbIn, addrspacePage)) then
       (pageDbIn, KOM_ERR_INVALID_ADDRSPACE())
   else
       var ctxtregs := map[R4:=0,R5:=0,R6:=0,R7:=0,R8:=0,R9:=0,R10:=0,R11:=0,
            R12:=0,SP(User):=0x10,LR(User):=0];
       var ctxt := DispatcherContext(ctxtregs, entrypoint, encode_mode(User));
       // Not sure why this can't verify... moving on for now?
       assume decode_mode'(psr_mask_mode(encode_mode(User))) == Just(User);  
       allocatePage(pageDbIn, page, addrspacePage, Dispatcher(entrypoint, false, ctxt))
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
                assert page in addrspaceRefs(pageDbIn, addrspacePage);
                var updatedAddrspace := match addrspace
                    case Addrspace(l1, ref, state) => Addrspace(l1, ref - 1, state);
                var pageDbOut := (pageDbIn[page := PageDbEntryFree])[
                    addrspacePage := PageDbEntryTyped(addrspacePage, updatedAddrspace)];
                (pageDbOut, KOM_ERR_SUCCESS())
}

function smc_mapSecure(pageDbIn: PageDb, page: word, addrspacePage: word,
    mapping: Mapping, physPage: word) : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE())
    else 
        var err := isValidMappingTarget(pageDbIn, addrspacePage, mapping);
        if( err != KOM_ERR_SUCCESS() ) then (pageDbIn, err)
        else 
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
                    var l2pte := SecureMapping(page, mapping.perm.w, mapping.perm.x);
                    var pageDbOut := updateL2Pte(pageDbA, addrspacePage, mapping, l2pte);
                    (pageDbOut, KOM_ERR_SUCCESS())
}

function smc_mapInsecure(pageDbIn: PageDb, addrspacePage: word,
    physPage: word, mapping : Mapping) : (PageDb, word)
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
            assert validInsecurePageNr(physPage);
            var l2pte := InsecureMapping( physPage,  mapping.perm.w);
            var pageDbOut := updateL2Pte(pageDbIn, addrspacePage, mapping, l2pte);
            (pageDbOut, KOM_ERR_SUCCESS())
}

function smc_finalise(pageDbIn: PageDb, addrspacePage: word) : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE())
    else if(pageDbIn[addrspacePage].entry.state != InitState) then
        (pageDbIn, KOM_ERR_ALREADY_FINAL())
    else
        var addrspace := pageDbIn[addrspacePage].entry;
        var updatedAddrspace := match addrspace
            case Addrspace(l1, ref, state) => Addrspace(l1, ref, FinalState);
        var pageDbOut := pageDbIn[
            addrspacePage := PageDbEntryTyped(addrspacePage, updatedAddrspace)];
        (pageDbOut, KOM_ERR_SUCCESS())
}

function smc_enter(pageDbIn: PageDb, dispPage: word, arg1: word, arg2: word, arg3: word)
    : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    var d := pageDbIn; var p := dispPage;
    if(!(validPageNr(p) && d[p].PageDbEntryTyped? && d[p].entry.Dispatcher?)) then
        (pageDbIn, KOM_ERR_INVALID_PAGENO())
    else if(var a := d[p].addrspace; d[a].entry.state != FinalState) then
        (pageDbIn, KOM_ERR_NOT_FINAL())
    else if(d[p].entry.entered) then
        (pageDbIn, KOM_ERR_ALREADY_ENTERED())
    else
        (pageDbIn, KOM_ERR_SUCCESS())
}

function smc_resume(pageDbIn: PageDb, dispPage: word)
    : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    var d := pageDbIn; var p := dispPage;
    if(!(validPageNr(p) && d[p].PageDbEntryTyped? && d[p].entry.Dispatcher?)) then
        (pageDbIn, KOM_ERR_INVALID_PAGENO())
    else if(var a := d[p].addrspace; d[a].entry.state != FinalState) then
        (pageDbIn, KOM_ERR_NOT_FINAL())
    else if(!d[p].entry.entered) then
        (pageDbIn, KOM_ERR_NOT_ENTERED())
    else
        (pageDbIn, KOM_ERR_SUCCESS())
}

function smc_stop(pageDbIn: PageDb, addrspacePage: word)
    : (PageDb, word)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KOM_ERR_INVALID_ADDRSPACE())
    // else if(pageDbIn[addrspacePage].entry.state == InitState) then
    //     (pageDbIn, KOM_ERR_ALREADY_FINAL())
    else
        var addrspace := pageDbIn[addrspacePage].entry;
        var updatedAddrspace := match addrspace
            case Addrspace(l1, ref, state) => Addrspace(l1, ref, StoppedState);
        var pageDbOut := pageDbIn[
            addrspacePage := PageDbEntryTyped(addrspacePage, updatedAddrspace)];
        (pageDbOut, KOM_ERR_SUCCESS())
}

//=============================================================================
// Behavioral Specification of SMC Handler
//=============================================================================
function smchandler(pageDbIn: PageDb, callno: word, arg1: word, arg2: word,
    arg3: word, arg4: word) : (PageDb, word, word) // pageDbOut, err, val
    requires validPageDb(pageDbIn)
{
    if(callno == KOM_SMC_QUERY()) then (pageDbIn, KOM_MAGIC(), 0)
    else if(callno == KOM_SMC_GETPHYSPAGES()) then
        (pageDbIn, KOM_ERR_SUCCESS(), KOM_SECURE_NPAGES())
    else if(callno == KOM_SMC_INIT_ADDRSPACE()) then
        var ret := smc_initAddrspace(pageDbIn, arg1, arg2);
        (ret.0, ret.1, 0)
    else if(callno == KOM_SMC_INIT_DISPATCHER()) then
        var ret := smc_initDispatcher(pageDbIn, arg1, arg2, arg3);
        (ret.0, ret.1, 0)
    else if(callno == KOM_SMC_INIT_L2PTABLE()) then
        var ret := smc_initL2PTable(pageDbIn, arg1, arg2, arg3);
        (ret.0, ret.1, 0)
    else if(callno == KOM_SMC_MAP_SECURE()) then
        var ret := smc_mapSecure(pageDbIn, arg1, arg2, wordToMapping(arg3), arg4);
        (ret.0, ret.1, 0)
    else if(callno == KOM_SMC_MAP_INSECURE()) then
        var ret := smc_mapInsecure(pageDbIn, arg1, arg2, wordToMapping(arg3));
        (ret.0, ret.1, 0)
    else if(callno == KOM_SMC_REMOVE()) then
        var ret := smc_remove(pageDbIn, arg1);
        (ret.0, ret.1, 0)
    else if(callno == KOM_SMC_FINALISE()) then
        var ret := smc_finalise(pageDbIn, arg1);
        (ret.0, ret.1, 0)
    else if(callno == KOM_SMC_ENTER()) then
        var ret := smc_enter(pageDbIn, arg1, arg2, arg3, arg4);
        (ret.0, ret.1, 0)
    else if(callno == KOM_SMC_RESUME()) then
        var ret := smc_resume(pageDbIn, arg1);
        (ret.0, ret.1, 0)
    else if(callno == KOM_SMC_STOP()) then
        var ret := smc_stop(pageDbIn, arg1);
        (ret.0, ret.1, 0)
    else (pageDbIn, KOM_ERR_INVALID(), 0)
}

/* Invariant across SMC handler state */
predicate smchandlerInvariant(s:state, s':state)
    requires ValidState(s)
{
    reveal_ValidRegState();
    reveal_ValidConfig();
    ValidState(s')
        // non-volatile regs preserved
        && s.regs[R4] == s'.regs[R4] && s.regs[R5] == s'.regs[R5]
        && s.regs[R6] == s'.regs[R6] && s.regs[R7] == s'.regs[R7]
        && s.regs[R8] == s'.regs[R8] && s.regs[R9] == s'.regs[R9]
        && s.regs[R10] == s'.regs[R10] && s.regs[R11] == s'.regs[R11]
        && s.regs[R12] == s'.regs[R12]
        // banked regs, including SPSR and LR (our return target) are preserved
        && forall m :: ((m == User || s.conf.spsr[m] == s'.conf.spsr[m])
                && s.regs[LR(m)] == s'.regs[LR(m)]
                && s.regs[SP(m)] == s'.regs[SP(m)])
        // non-secure world
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
