include "kev_constants.s.dfy"
include "pagedb.s.dfy"

predicate pageIsFree(d:PageDb, pg:PageNr)
    { pg in d && d[pg].PageDbEntryFree? }

// a points to an address space and it is closed
predicate validAddrspacePage(d: PageDb, a: PageNr)
{
    wellFormedPageDb(d) &&
    isAddrspace(d, a) && d[a].entry.l1ptnr in d
}

predicate physPageInvalid( physPage: int )
{
    physPage != 0 && !(physPageIsRam(physPage)
        && !physPageIsSecure(physPage))
}

predicate physPageIsRam( physPage: int )
{
   physPage * KEVLAR_PAGE_SIZE() < SecurePhysBase()
}

predicate physPageIsSecure( physPage: int )
{
    var paddr := physPage * KEVLAR_PAGE_SIZE();
    SecurePhysBase() <= paddr < SecurePhysBase() +
        KEVLAR_SECURE_NPAGES() * KEVLAR_PAGE_SIZE()
}

predicate l1indexInUse(d: PageDb, a: PageNr, l1index: int)
    requires validPageDb(d)
    requires isAddrspace(d, a)
    requires d[a].entry.state != StoppedState
    requires 0 <= l1index < NR_L1PTES()
{
	reveal_validPageDb();
    var l1ptnr := d[a].entry.l1ptnr;
    var l1 := d[l1ptnr].entry.l1pt;
    l1[l1index].Just?
}

//=============================================================================
// Mapping
//=============================================================================
datatype Mapping = Mapping(l1index: PageNr, l2index: PageNr, perm: Perm)
datatype Perm = Perm(r: bool, w: bool, x: bool)

function {:opaque} intToMapping(arg: int) : Mapping
{
    Mapping(1,1,Perm(false,false,false))
}

function updateL2Pte(pageDbIn: PageDb, a: PageNr, mapping: Mapping, l2e : L2PTE)
    : PageDb 
    requires validPageDb(pageDbIn)
    requires validPageNr(a)
    requires isAddrspace(pageDbIn, a)
    requires isValidMappingTarget(pageDbIn, a, mapping) == KEV_ERR_SUCCESS()
    requires pageDbIn[a].PageDbEntryTyped? && pageDbIn[a].entry.Addrspace?
    requires pageDbIn[a].entry.state.InitState?
{
	reveal_validPageDb();
    var addrspace := pageDbIn[a].entry;
    var l1 := pageDbIn[addrspace.l1ptnr].entry;
    var l1pte := fromJust(l1.l1pt[mapping.l1index]);
    var l2pt := pageDbIn[l1pte].entry.l2pt;
    validPageDbImpliesClosedRefs(pageDbIn);
	reveal_pageDbClosedRefs();
    pageDbIn[ l1pte := PageDbEntryTyped(a, L2PTable(l2pt[mapping.l2index := l2e])) ]

}

function isValidMappingTarget(d: PageDb, a: PageNr, mapping: Mapping)
    : int // KEV_ERROR
    requires validPageDb(d)
    requires validPageNr(a)
    requires isAddrspace(d, a)
{
    reveal_validPageDb();
    var addrspace := d[a].entry;
    if(!addrspace.state.InitState?) then
        KEV_ERR_ALREADY_FINAL()
    else if(!mapping.perm.r) then KEV_ERR_INVALID_MAPPING()
    else if(!(0 <= mapping.l1index < NR_L1PTES())
        || !(0 <= mapping.l2index < NR_L2PTES()) ) then
        KEV_ERR_INVALID_MAPPING()
    else
        var l1 := d[addrspace.l1ptnr].entry;
        var l1pte := l1.l1pt[mapping.l1index];
        if(l1pte.Nothing?) then KEV_ERR_INVALID_MAPPING()
        else KEV_ERR_SUCCESS()
}

//============================================================================
// Behavioral Specification of Monitor Calls
//=============================================================================
function smc_query() : int { KEV_MAGIC() }

function smc_getPhysPages() : int { KEVLAR_SECURE_NPAGES() }

function smc_initAddrspace(pageDbIn: PageDb, addrspacePage: PageNr, l1PTPage: PageNr)
    : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn);
{
    reveal_validPageDb();
    var g := pageDbIn;
    if(!validPageNr(addrspacePage) || !validPageNr(l1PTPage) ||
        addrspacePage == l1PTPage) then
        (pageDbIn, KEV_ERR_INVALID_PAGENO())
    else if(l1PTPage % 4 != 0) then
        (pageDbIn, KEV_ERR_INVALID_PAGENO())
    else if( !g[addrspacePage].PageDbEntryFree? || !g[l1PTPage].PageDbEntryFree? ) then
        (pageDbIn, KEV_ERR_PAGEINUSE())
    else
        var addrspace := Addrspace(l1PTPage, 1, InitState);
        var l1PT := L1PTable(SeqRepeat(NR_L1PTES(),Nothing));
        var pageDbOut := 
            (pageDbIn[addrspacePage := PageDbEntryTyped(addrspacePage, addrspace)])[
                l1PTPage := PageDbEntryTyped(addrspacePage, l1PT)];
        (pageDbOut, KEV_ERR_SUCCESS())
}

function smc_initDispatcher(pageDbIn: PageDb, page:PageNr, addrspacePage:PageNr,
    entrypoint:int)
    : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn);
{
    reveal_validPageDb();
   var n := page;
   var d := pageDbIn;
   if(!isAddrspace(pageDbIn, addrspacePage)) then
       (pageDbIn, KEV_ERR_INVALID_ADDRSPACE())
   else
       allocatePage(pageDbIn, page, addrspacePage, Dispatcher(entrypoint, false))
}


function smc_initL2PTable(pageDbIn: PageDb, page: PageNr,
    addrspacePage: PageNr, l1index: int) : (PageDb, int)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!(0<= l1index < NR_L1PTES())) then (pageDbIn, KEV_ERR_INVALID_MAPPING())
    else if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KEV_ERR_INVALID_ADDRSPACE())

    // This gets caught later in allocatePage, but putting the check
    // here means that the addrspace's state will not be stopped for the
    // l1indexInUse check. The l1indexInUse check assumes that the l1ptnr
    // is actually an l1pt table, which is true as long as the addrspace
    // is not stopped.
    else if(pageDbIn[addrspacePage].entry.state != InitState) then
        (pageDbIn, KEV_ERR_ALREADY_FINAL())
    else if(l1indexInUse(pageDbIn, addrspacePage, l1index)) then
        (pageDbIn, KEV_ERR_ADDRINUSE())
    else 
        var l2pt := L2PTable(SeqRepeat(NR_L2PTES(), NoMapping));
        allocatePage(pageDbIn, page, addrspacePage, l2pt)
}

// This is not literally an SMC handler. Move elsewhere in file???
function allocatePage_inner(pageDbIn: PageDb, securePage: PageNr,
    addrspacePage:PageNr, entry:PageDbEntryTyped)
    : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn)
    requires validAddrspacePage(pageDbIn, addrspacePage)
    requires closedRefsPageDbEntry(entry)
    requires !entry.L1PTable?
    requires !entry.Addrspace?
    requires entry.L2PTable? ==>
        entry.l2pt == SeqRepeat(NR_L2PTES(), NoMapping)
{
    reveal_validPageDb();
    var addrspace := pageDbIn[addrspacePage].entry;
    if(!validPageNr(securePage)) then (pageDbIn, KEV_ERR_INVALID_PAGENO())
    else if(!pageIsFree(pageDbIn, securePage)) then (pageDbIn, KEV_ERR_PAGEINUSE())
    else if(addrspace.state != InitState) then
        (pageDbIn,KEV_ERR_ALREADY_FINAL())
    // TODO ?? Model page clearing for non-data pages?
    else
        var updatedAddrspace := match addrspace
            case Addrspace(l1, ref, state) => Addrspace(l1, ref + 1, state);
        var pageDbOut := (pageDbIn[
            securePage := PageDbEntryTyped(addrspacePage, entry)])[
            addrspacePage := PageDbEntryTyped(addrspacePage, updatedAddrspace)];
        (pageDbOut, KEV_ERR_SUCCESS())
}

// TODO move this elsewhere since it is not a monitor call
function allocatePage(pageDbIn: PageDb, securePage: PageNr,
    addrspacePage:PageNr, entry:PageDbEntryTyped )
    : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn)
    requires validAddrspacePage(pageDbIn, addrspacePage)
    requires closedRefsPageDbEntry(entry)
    requires !entry.L1PTable?
    requires !entry.Addrspace?
    requires entry.L2PTable? ==>
        entry.l2pt == SeqRepeat(NR_L2PTES(), NoMapping)
    ensures  validPageDb(allocatePage(pageDbIn, securePage, addrspacePage, entry).0);
{
    reveal_validPageDb();
    allocatePagePreservesPageDBValidity(pageDbIn, securePage, addrspacePage, entry);
    allocatePage_inner(pageDbIn, securePage, addrspacePage, entry)
}

function smc_remove(pageDbIn: PageDb, page: PageNr)
    : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!validPageNr(page)) then
        (pageDbIn, KEV_ERR_INVALID_PAGENO())
    else if(pageDbIn[page].PageDbEntryFree?) then
        (pageDbIn, KEV_ERR_SUCCESS())
    else 
        var e := pageDbIn[page].entry;
        var addrspacePage := pageDbIn[page].addrspace;
        var addrspace := pageDbIn[addrspacePage].entry;
        if( e.Addrspace? ) then
           if(e.refcount !=0) then (pageDbIn, KEV_ERR_PAGEINUSE())
           else (pageDbIn[page := PageDbEntryFree], KEV_ERR_SUCCESS())
        else 
            if( !addrspace.state.StoppedState?) then
                (pageDbIn, KEV_ERR_NOT_STOPPED())
            else 
                assert page in addrspaceRefs(pageDbIn, addrspacePage);
                var updatedAddrspace := match addrspace
                    case Addrspace(l1, ref, state) => Addrspace(l1, ref - 1, state);
                var pageDbOut := (pageDbIn[page := PageDbEntryFree])[
                    addrspacePage := PageDbEntryTyped(addrspacePage, updatedAddrspace)];
                (pageDbOut, KEV_ERR_SUCCESS())
}

function smc_mapSecure(pageDbIn: PageDb, page: PageNr, addrspacePage: PageNr,
    mapping: Mapping, physPage: int) : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KEV_ERR_INVALID_ADDRSPACE())
    else 
        var err := isValidMappingTarget(pageDbIn, addrspacePage, mapping);
        if( err != KEV_ERR_SUCCESS() ) then (pageDbIn, err)
        else 
            // I'm not actually sure if this makes sense. I don't know
            // that physPage is actually modeling a physical page here...
            // address translation isn't modeled here at all.
            if( physPageInvalid(physPage) ) then
                (pageDbIn, KEV_ERR_INVALID_PAGENO())
            else
                var ap_ret := allocatePage(pageDbIn, page,
                    addrspacePage, DataPage);
                var pageDbA := ap_ret.0;
                var errA := ap_ret.1;
                if(errA != KEV_ERR_SUCCESS()) then (pageDbIn, errA)
                else
                    var l2pte := SecureMapping(page, mapping.perm.w, mapping.perm.x);
                    var pageDbOut := updateL2Pte(pageDbA, addrspacePage, mapping, l2pte);
                    (pageDbOut, KEV_ERR_SUCCESS())
}

function smc_mapInsecure(pageDbIn: PageDb, addrspacePage: PageNr,
    physPage: int, mapping : Mapping) : (PageDb, int)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KEV_ERR_INVALID_ADDRSPACE())
    else
        var err := isValidMappingTarget(pageDbIn, addrspacePage, mapping);
        if( err != KEV_ERR_SUCCESS() ) then (pageDbIn, err)
        else if( physPageIsSecure(physPage) ) then
            (pageDbIn, KEV_ERR_INVALID_PAGENO())
        else
            var l2pte := InsecureMapping( physPage );
            var pageDbOut := updateL2Pte(pageDbIn, addrspacePage, mapping, l2pte);
            (pageDbOut, KEV_ERR_SUCCESS())
}

function smc_finalise(pageDbIn: PageDb, addrspacePage: PageNr) : (PageDb, int)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KEV_ERR_INVALID_ADDRSPACE())
    else if(pageDbIn[addrspacePage].entry.state != InitState) then
        (pageDbIn, KEV_ERR_ALREADY_FINAL())
    else
        var addrspace := pageDbIn[addrspacePage].entry;
        var updatedAddrspace := match addrspace
            case Addrspace(l1, ref, state) => Addrspace(l1, ref, FinalState);
        var pageDbOut := pageDbIn[
            addrspacePage := PageDbEntryTyped(addrspacePage, updatedAddrspace)];
        (pageDbOut, KEV_ERR_SUCCESS())
}

function smc_enter(pageDbIn: PageDb, dispPage: PageNr, arg1: int, arg2: int, arg3: int)
    : (PageDb, int)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    var d := pageDbIn; var p := dispPage;
    if(!(validPageNr(p) && d[p].PageDbEntryTyped? && d[p].entry.Dispatcher?)) then
        (pageDbIn, KEV_ERR_INVALID_PAGENO())
    else if(var a := d[p].addrspace; d[a].entry.state != FinalState) then
        (pageDbIn, KEV_ERR_NOT_FINAL())
    else if(d[p].entry.entered) then
        (pageDbIn, KEV_ERR_ALREADY_ENTERED())
    else
        // A model of registers is needed to model more.
        // For now all this does is change the dispatcher.
        var a := d[p].addrspace;
        var pageDbOut := match d[p].entry 
                case Dispatcher(entrypoint, entered) => 
                    d[p := PageDbEntryTyped(a,Dispatcher(entrypoint,true))];
        (pageDbOut, KEV_ERR_SUCCESS())
}

function smc_resume(pageDbIn: PageDb, dispPage: PageNr)
    : (PageDb, int)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    var d := pageDbIn; var p := dispPage;
    if(!(validPageNr(p) && d[p].PageDbEntryTyped? && d[p].entry.Dispatcher?)) then
        (pageDbIn, KEV_ERR_INVALID_PAGENO())
    else if(var a := d[p].addrspace; d[a].entry.state != FinalState) then
        (pageDbIn, KEV_ERR_NOT_FINAL())
    else if(!d[p].entry.entered) then
        (pageDbIn, KEV_ERR_ALREADY_ENTERED())
    else
        // A model of registers is needed to model more.
        // For now all this does is change the dispatcher.
        var a := d[p].addrspace;
        var pageDbOut := match d[p].entry 
                case Dispatcher(entrypoint, entered) => 
                    d[p := PageDbEntryTyped(a,Dispatcher(entrypoint,false))];
        (pageDbOut, KEV_ERR_SUCCESS())
}

function smc_stop(pageDbIn: PageDb, addrspacePage: PageNr)
    : (PageDb, int)
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(!isAddrspace(pageDbIn, addrspacePage)) then
        (pageDbIn, KEV_ERR_INVALID_ADDRSPACE())
    // else if(pageDbIn[addrspacePage].entry.state == InitState) then
    //     (pageDbIn, KEV_ERR_ALREADY_FINAL())
    else
        var addrspace := pageDbIn[addrspacePage].entry;
        var updatedAddrspace := match addrspace
            case Addrspace(l1, ref, state) => Addrspace(l1, ref, StoppedState);
        var pageDbOut := pageDbIn[
            addrspacePage := PageDbEntryTyped(addrspacePage, updatedAddrspace)];
        (pageDbOut, KEV_ERR_SUCCESS())
}

//=============================================================================
// Behavioral Specification of SMC Handler
//=============================================================================
function smchandler(pageDbIn: PageDb, callno: int, arg1: int, arg2: int,
    arg3: int, arg4: int) : (PageDb, int, int) // pageDbOut, err, val
    requires validPageDb(pageDbIn)
{
    reveal_validPageDb();
    if(callno == KEV_SMC_QUERY()) then (pageDbIn, KEV_MAGIC(), 0)
    else if(callno == KEV_SMC_GETPHYSPAGES()) then
        (pageDbIn, KEV_ERR_SUCCESS(), KEVLAR_SECURE_NPAGES())
    else if(callno == KEV_SMC_INIT_ADDRSPACE()) then
        var ret := smc_initAddrspace(pageDbIn, arg1, arg2);
        (ret.0, ret.1, 0)
    else if(callno == KEV_SMC_INIT_DISPATCHER()) then
        var ret := smc_initDispatcher(pageDbIn, arg1, arg2, arg3);
        (ret.0, ret.1, 0)
    else if(callno == KEV_SMC_INIT_L2PTABLE()) then
        var ret := smc_initL2PTable(pageDbIn, arg1, arg2, arg3);
        (ret.0, ret.1, 0)
    else if(callno == KEV_SMC_MAP_SECURE()) then
        var ret := smc_mapSecure(pageDbIn, arg1, arg2, intToMapping(arg3), arg4);
        (ret.0, ret.1, 0)
    else if(callno == KEV_SMC_MAP_INSECURE()) then
        var ret := smc_mapInsecure(pageDbIn, arg1, arg2, intToMapping(arg3));
        (ret.0, ret.1, 0)
    else if(callno == KEV_SMC_REMOVE()) then
        var ret := smc_remove(pageDbIn, arg1);
        (ret.0, ret.1, 0)
    else if(callno == KEV_SMC_FINALISE()) then
        var ret := smc_finalise(pageDbIn, arg1);
        (ret.0, ret.1, 0)
    else if(callno == KEV_SMC_ENTER()) then
        var ret := smc_enter(pageDbIn, arg1, arg2, arg3, arg4);
        (ret.0, ret.1, 0)
    else if(callno == KEV_SMC_RESUME()) then
        var ret := smc_resume(pageDbIn, arg1);
        (ret.0, ret.1, 0)
    else if(callno == KEV_SMC_STOP()) then
        var ret := smc_stop(pageDbIn, arg1);
        (ret.0, ret.1, 0)
    else (pageDbIn, KEV_ERR_INVALID(), 0)
}


// lemma for allocatePage; FIXME: not trusted, should not be in a .s.dfy file
lemma allocatePagePreservesPageDBValidity(pageDbIn: PageDb,
    securePage: PageNr, addrspacePage: PageNr, entry: PageDbEntryTyped)
    requires validPageDb(pageDbIn)
    requires validAddrspacePage(pageDbIn, addrspacePage)
    requires closedRefsPageDbEntry(entry)
    requires !entry.Addrspace?
    requires !entry.L1PTable?
    requires entry.L2PTable? ==>
        entry.l2pt == SeqRepeat(NR_L2PTES(), NoMapping)
    ensures  validPageDb(allocatePage_inner(
        pageDbIn, securePage, addrspacePage, entry).0);
{
    reveal_validPageDb();
    var pageDbOut := allocatePage_inner(pageDbIn, securePage,
        addrspacePage, entry).0;
    var errOut := allocatePage_inner(pageDbIn, securePage,
        addrspacePage, entry).1;

    if ( errOut != KEV_ERR_SUCCESS() ){
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
        }

        assert pageDbEntriesValid(pageDbOut);
        assert validPageDb(pageDbOut);
    }
}
