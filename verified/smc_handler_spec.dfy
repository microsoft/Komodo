include "kev_constants.dfy"
include "Maybe.dfy"
include "pagedb.dfy"

function pageIsFree(d:PageDb, pg:PageNr) : bool
    requires pg in d;
    { d[pg].PageDbEntryFree? }

// a points to an address space and it is closed
predicate validAddrspacePage(d: PageDb, a: PageNr)
    requires wellFormedPageDb(d)
{
    isAddrspace(d, a) && d[a].entry.l1ptnr in d
}

function page_paddr(p: PageNr) : int
{
    G_SECURE_PHYSBASE() + p * KEVLAR_PAGE_SIZE()
}

predicate physPageInvalid( physPage: int )
{
    physPage != 0 && !(physPageIsRam(physPage)
        && !physPageIsSecure(physPage))
}

predicate physPageIsRam( physPage: int )
{
   physPage * KEVLAR_PAGE_SIZE() < G_SECURE_PHYSBASE() 
}

predicate physPageIsSecure( physPage: int )
{
    var paddr := physPage * KEVLAR_PAGE_SIZE();
    G_SECURE_PHYSBASE() <= paddr < G_SECURE_PHYSBASE() +
        page_paddr(KEVLAR_SECURE_NPAGES())
}

predicate l1indexInUse(d: PageDb, a: PageNr, l1index: int)
    requires validPageDb(d)
    requires isAddrspace(d, a)
    requires d[a].entry.state != StoppedState
    requires 0 <= l1index < NR_L1PTES()
{
    var l1ptnr := d[a].entry.l1ptnr;
    var l1 := d[l1ptnr].entry.l1pt;
    l1[l1index].Just?
}

//=============================================================================
// Mapping
//=============================================================================
datatype Mapping = Mapping(l1index: PageNr, l2index: PageNr, perm: Perm)
datatype Perm = Perm(r: bool, w: bool, x: bool)

function updateL2Pte(pageDbIn: PageDb, a: PageNr, mapping: Mapping, l2e : L2PTE)
    : PageDb 
    requires validPageDb(pageDbIn)
    requires validPageNr(a)
    requires isAddrspace(pageDbIn, a)
    requires isValidMappingTarget(pageDbIn, a, mapping) == KEV_ERR_SUCCESS()
    requires pageDbIn[a].PageDbEntryTyped? && pageDbIn[a].entry.Addrspace?
    requires pageDbIn[a].entry.state.InitState?
{
    var addrspace := pageDbIn[a].entry;
    var l1 := pageDbIn[addrspace.l1ptnr].entry;
    var l1pte := fromJust(l1.l1pt[mapping.l1index]);
    var l2pt := pageDbIn[l1pte].entry.l2pt;
    validPageDbImpliesClosedRefs(pageDbIn);
    pageDbIn[ l1pte := PageDbEntryTyped(a, L2PTable(l2pt[mapping.l2index := l2e])) ]

}

function isValidMappingTarget(d: PageDb, a: PageNr, mapping: Mapping)
    : int // KEV_ERROR
    requires validPageDb(d)
    requires validPageNr(a)
    requires isAddrspace(d, a)
{
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
function initAddrspace_inner(pageDbIn: PageDb, addrspacePage: PageNr, l1PTPage: PageNr)
    : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn);
{
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

function initDispatcher_inner(pageDbIn: PageDb, page:PageNr, addrspacePage:PageNr,
    entrypoint:int)
    : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn);
{
   var n := page;
   var d := pageDbIn;
   if(!isAddrspace(pageDbIn, addrspacePage)) then
       (pageDbIn, KEV_ERR_INVALID_ADDRSPACE())
   else
       allocatePage(pageDbIn, page, addrspacePage, Dispatcher(entrypoint, false))
}


function initL2PTable_inner(pageDbIn: PageDb, page: PageNr,
    addrspacePage: PageNr, l1index: int) : (PageDb, int)
    requires validPageDb(pageDbIn)
{
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

function remove_inner(pageDbIn: PageDb, page: PageNr)
    : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn)
{
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

function mapSecure_inner(pageDbIn: PageDb, page: PageNr, addrspacePage: PageNr,
    mapping: Mapping, physPage: int) : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn)
    requires validPageNr(page)
    requires validPageNr(addrspacePage)
{
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

function mapInsecure_inner(pageDbIn: PageDb, addrspacePage: PageNr,
    physPage: int, mapping : Mapping) : (PageDb, int)
    requires validPageDb(pageDbIn)
    requires validPageNr(addrspacePage)
{
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

function finalise_inner(pageDbIn: PageDb, addrspacePage: PageNr) : (PageDb, int)
    requires validPageDb(pageDbIn)
{
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

function enter_inner(pageDbIn: PageDb, dispPage: PageNr, arg1: int, arg2: int, arg3: int)
    : (PageDb, int)
    requires validPageDb(pageDbIn)
{
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

function resume_inner(pageDbIn: PageDb, dispPage: PageNr, arg1: int, arg2: int, arg3: int)
    : (PageDb, int)
    requires validPageDb(pageDbIn)
{
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

//=============================================================================
// Hoare Specification of Monitor Calls
//=============================================================================
// (i.e. specs with postconditions)

function initAddrspace(pageDbIn: PageDb, addrspacePage: PageNr, l1PTPage: PageNr)
    : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn);
    ensures  validPageDb(initAddrspace(pageDbIn, addrspacePage, l1PTPage).0);
{
    initAddrspacePreservesPageDBValidity(pageDbIn, addrspacePage, l1PTPage);
    initAddrspace_inner(pageDbIn, addrspacePage, l1PTPage)
}

function initDispatcher(pageDbIn: PageDb, page:PageNr, addrspacePage:PageNr,
    entrypoint:int) : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn);
    ensures  validPageDb(initDispatcher(pageDbIn, page, addrspacePage, entrypoint).0);
{
    initDispatcher_inner(pageDbIn, page, addrspacePage, entrypoint)
}

function initL2PTable(pageDbIn: PageDb, page: PageNr,
    addrspacePage: PageNr, l1index: int) : (PageDb, int)
    requires validPageDb(pageDbIn)
    ensures validPageDb(initL2PTable(pageDbIn, page, addrspacePage, l1index).0)
{
    initL2PTable_inner(pageDbIn, page, addrspacePage, l1index)
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
    allocatePagePreservesPageDBValidity(pageDbIn, securePage, addrspacePage, entry);
    allocatePage_inner(pageDbIn, securePage, addrspacePage, entry)
}

function remove(pageDbIn: PageDb, page: PageNr) : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn)
    ensures  validPageDb(remove(pageDbIn, page).0)
{
    removePreservesPageDBValidity(pageDbIn, page);
    remove_inner(pageDbIn, page)
}

function mapSecure(pageDbIn: PageDb, page: PageNr, addrspacePage: PageNr,
    mapping: Mapping, physPage: int) : (PageDb, int) // PageDbOut, KEV_ERR
    requires validPageDb(pageDbIn)
    requires validPageNr(page)
    requires validPageNr(addrspacePage)
    ensures  validPageDb(mapSecure(pageDbIn, page, addrspacePage, mapping, physPage).0)
{
    mapSecurePreservesPageDBValidity(pageDbIn, page, addrspacePage, mapping, physPage);
    mapSecure_inner(pageDbIn, page, addrspacePage, mapping, physPage)
}

function mapInsecure(pageDbIn: PageDb, addrspacePage: PageNr,
    physPage: int, mapping : Mapping) : (PageDb, int)
    requires validPageDb(pageDbIn)
    requires validPageNr(addrspacePage)
    ensures  validPageDb(mapInsecure(pageDbIn, addrspacePage, physPage, mapping).0)
{
    mapInsecurePreservesPageDbValidity(pageDbIn, addrspacePage, physPage, mapping);
    mapInsecure_inner(pageDbIn, addrspacePage, physPage, mapping)
}

function finalise(pageDbIn: PageDb, addrspacePage: PageNr) : (PageDb, int)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(finalise(pageDbIn, addrspacePage).0)
{
    finalisePreservesPageDbValidity(pageDbIn, addrspacePage);
    finalise_inner(pageDbIn, addrspacePage)
}

function enter(pageDbIn: PageDb, dispPage: PageNr, arg1: int, arg2: int, arg3: int)
    : (PageDb, int)
    requires validPageDb(pageDbIn) 
    ensures validPageDb(enter(pageDbIn, dispPage, arg1, arg2, arg3).0)
{
    enterPreservesPageDbValidity(pageDbIn, dispPage, arg1, arg2, arg3);
    enter_inner(pageDbIn, dispPage, arg1, arg2, arg3)
}

function resume(pageDbIn: PageDb, dispPage: PageNr, arg1: int, arg2: int, arg3: int)
    : (PageDb, int)
    requires validPageDb(pageDbIn) 
    ensures validPageDb(resume(pageDbIn, dispPage, arg1, arg2, arg3).0)
{
    resumePreservesPageDbValidity(pageDbIn, dispPage, arg1, arg2, arg3);
    resume_inner(pageDbIn, dispPage, arg1, arg2, arg3)
}

//=============================================================================
// Properties of Monitor Calls
//=============================================================================

//-----------------------------------------------------------------------------
// PageDb Validity Preservation
//-----------------------------------------------------------------------------
lemma initAddrspacePreservesPageDBValidity(pageDbIn : PageDb,
    addrspacePage : PageNr, l1PTPage : PageNr)
    requires validPageDb(pageDbIn)
    ensures validPageDb(initAddrspace_inner(pageDbIn, addrspacePage, l1PTPage).0)
{
     var pageDbOut := initAddrspace_inner(pageDbIn, addrspacePage, l1PTPage).0;
     var errOut := initAddrspace_inner(pageDbIn, addrspacePage, l1PTPage).1;

     if( errOut != KEV_ERR_SUCCESS() ) {
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
             && pageDbOut[n].PageDbEntryTyped?
             && n != addrspacePage && n != l1PTPage)
             ensures validPageDbEntryTyped(pageDbOut, n)
         {
             assert pageDbOut[n] == pageDbIn[n];
             assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
         }
              
         assert pageDbEntriesValid(pageDbOut);
         assert validPageDb(pageDbOut);
    }
}


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


lemma removePreservesPageDBValidity(pageDbIn: PageDb, page: PageNr)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(remove_inner(pageDbIn, page).0)
{

    var pageDbOut := remove_inner(pageDbIn, page).0;
    var errOut := remove_inner(pageDbIn, page).1;

    if ( errOut != KEV_ERR_SUCCESS() ){
       // trivial
    } else if( pageDbIn[page].PageDbEntryFree?) {
        // trivial
    } else {

        var entry := pageDbIn[page].entry;
        var addrspacePage := pageDbIn[page].addrspace;

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

                
                forall () ensures pageDbEntryOk(d, n){
                  
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

lemma mapSecurePreservesPageDBValidity(pageDbIn: PageDb, page: PageNr, addrspacePage: PageNr,
    mapping: Mapping, physPage: int)
    requires validPageDb(pageDbIn)
    requires validPageNr(page)
    requires validPageNr(addrspacePage)
    ensures  validPageDb(mapSecure_inner(pageDbIn, page, addrspacePage,
        mapping, physPage).0)
{
    var pageDbOut := mapSecure_inner(
        pageDbIn, page, addrspacePage, mapping, physPage).0;
    var err := mapSecure_inner(
        pageDbIn, page, addrspacePage, mapping, physPage).1;

    if( err != KEV_ERR_SUCCESS() ){
    } else {
        assert validPageDbEntryTyped(pageDbOut, page);
        
        var pageDbA := allocatePage(pageDbIn, page,
            addrspacePage, DataPage).0;
       
        forall() ensures validPageDbEntryTyped(pageDbOut, addrspacePage){
            var a := addrspacePage;
            assert pageDbOut[a].entry.refcount == pageDbA[a].entry.refcount;
            assert addrspaceRefs(pageDbOut, a) == addrspaceRefs(pageDbA, a);
        }

        forall( n | validPageNr(n)
            && pageDbOut[n].PageDbEntryTyped?
            && n != page && n != addrspacePage)
            ensures validPageDbEntryTyped(pageDbOut, n);
        {
            if( pageDbOut[n].entry.Addrspace? ){
                assert pageDbOut[n].entry.refcount == pageDbA[n].entry.refcount;
                assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbA, n);
            } else {
                // trivial
            }
        }
    }

}

lemma mapInsecurePreservesPageDbValidity(pageDbIn: PageDb, addrspacePage: PageNr,
    physPage: int, mapping : Mapping)
    requires validPageDb(pageDbIn)
    requires validPageNr(addrspacePage)
    ensures  validPageDb(mapInsecure_inner(pageDbIn, addrspacePage, physPage, mapping).0)
{
    var pageDbOut := mapInsecure_inner(
        pageDbIn, addrspacePage, physPage, mapping).0;
    var err := mapInsecure_inner(
        pageDbIn, addrspacePage, physPage, mapping).1;

    if( err != KEV_ERR_SUCCESS() ){
    } else {        
        forall() ensures validPageDbEntryTyped(pageDbOut, addrspacePage){
            var a := addrspacePage;
            assert pageDbOut[a].entry.refcount == pageDbIn[a].entry.refcount;
            assert addrspaceRefs(pageDbOut, a) == addrspaceRefs(pageDbIn, a);
        }

        forall( n | validPageNr(n)
            && pageDbOut[n].PageDbEntryTyped?
            && n != addrspacePage)
            ensures validPageDbEntryTyped(pageDbOut, n);
        {
            if( pageDbOut[n].entry.Addrspace? ){
                assert pageDbOut[n].entry.refcount == pageDbIn[n].entry.refcount;
                assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
            } else {
                // trivial
            }
        }
    }
}

lemma finalisePreservesPageDbValidity(pageDbIn: PageDb, addrspacePage: PageNr)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(finalise_inner(pageDbIn, addrspacePage).0)
{
    var pageDbOut := finalise_inner(pageDbIn, addrspacePage).0;
    var err := finalise_inner(pageDbIn, addrspacePage).1;

    if( err != KEV_ERR_SUCCESS() ){
    } else {
        var a := addrspacePage;
        assert pageDbOut[a].entry.refcount == pageDbIn[a].entry.refcount;
        assert addrspaceRefs(pageDbOut, a) == addrspaceRefs(pageDbIn, a);

        forall ( n | validPageNr(n) && n != a )
            ensures validPageDbEntry(pageDbOut, n);
    }
}

lemma enterPreservesPageDbValidity(pageDbIn: PageDb, dispPage: PageNr,
    arg1: int, arg2: int, arg3: int)
    requires validPageDb(pageDbIn) 
    ensures validPageDb(enter_inner(pageDbIn, dispPage, arg1, arg2, arg3).0)
{
    var pageDbOut := enter_inner(pageDbIn, dispPage, arg1, arg2, arg3).0;
    var err := enter_inner(pageDbIn, dispPage, arg1, arg2, arg3).1;

    if( err != KEV_ERR_SUCCESS() ){
    } else {
        var a := pageDbOut[dispPage].addrspace;
        assert pageDbOut[a].entry.refcount == pageDbIn[a].entry.refcount;
        assert addrspaceRefs(pageDbOut, a) == addrspaceRefs(pageDbIn, a);

        forall ( n | validPageNr(n) && n != a )
            ensures validPageDbEntry(pageDbOut, n);
    }
}

lemma resumePreservesPageDbValidity(pageDbIn: PageDb, dispPage: PageNr,
    arg1: int, arg2: int, arg3: int)
    requires validPageDb(pageDbIn) 
    ensures validPageDb(resume_inner(pageDbIn, dispPage, arg1, arg2, arg3).0)
{
    var pageDbOut := resume_inner(pageDbIn, dispPage, arg1, arg2, arg3).0;
    var err := resume_inner(pageDbIn, dispPage, arg1, arg2, arg3).1;

    if( err != KEV_ERR_SUCCESS() ){
    } else {
        var a := pageDbOut[dispPage].addrspace;
        assert pageDbOut[a].entry.refcount == pageDbIn[a].entry.refcount;
        assert addrspaceRefs(pageDbOut, a) == addrspaceRefs(pageDbIn, a);

        forall ( n | validPageNr(n) && n != a )
            ensures validPageDbEntry(pageDbOut, n);
    }
}
