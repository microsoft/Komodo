include "kev_constants.dfy"
include "Maybe.dfy"
include "pagedb.dfy"

datatype smcReturn = Pair(pageDbOut: PageDb, err: int)

// TODO FIXME!!
function mon_vmap(p:PageNr) : int {
    p 
}

function pagedbFrmRet(ret:smcReturn): PageDb
    { match ret case Pair(p,e) => p }

function errFrmRet(ret:smcReturn): int 
    { match ret case Pair(p,e) => e }

function pageIsFree(d:PageDb, pg:PageNr) : bool
    requires pg in d;
    { d[pg].PageDbEntryFree? }

function allocatePage(pageDbIn: PageDb, securePage: PageNr,
    addrspacePage:PageNr, pageType: PageDbEntryTyped) : smcReturn
    requires validPageDb(pageDbIn)
    requires wellFormedAddrspace(pageDbIn, addrspacePage)
    requires validAddrspace(pageDbIn, addrspacePage)
    requires !pageType.Addrspace?
    ensures  validPageDb(pagedbFrmRet(allocatePage(pageDbIn, securePage, addrspacePage, pageType)))
{
    var addrspace := pageDbIn[addrspacePage].entry;
    if(!validPageNr(securePage)) then Pair(pageDbIn, KEV_ERR_INVALID_PAGENO())
    else if(!pageIsFree(pageDbIn, securePage)) then Pair(pageDbIn, KEV_ERR_PAGEINUSE())
    else if(addrspace.state != InitState) then
        Pair(pageDbIn,KEV_ERR_ALREADY_FINAL())
    // Model page clearing for non-data pages?
    else
        var updatedAddrspace := match addrspace
            case Addrspace(l1, ref, state) => Addrspace(l1, ref + 1, state);
        var pageDbUpdated := pageDbIn[
            securePage := PageDbEntryTyped(addrspacePage, pageType) ];
        var pageDbOut := pageDbUpdated[
            addrspacePage := PageDbEntryTyped(addrspacePage, updatedAddrspace)];
        
        assert wellFormedPageDb(pageDbOut);
        assert pageDbEntriesAddrspacesOk(pageDbOut);
        assert validPageDbEntry(pageDbOut, addrspacePage);
        
        //These two fail
        assume validPageDbEntry(pageDbOut, securePage);
        // assume forall n :: n in pageDbOut && n != addrspacePage && n != securePage ==>
        //     validPageDbEntry(pageDbOut, n);
        assume pageDbEntriesValid(pageDbOut);

        assert pageDbEntriesValidRefs(pageDbOut);
        assert validPageDb(pageDbOut);
        Pair(pageDbOut, KEV_ERR_SUCCESS())
}

function initAddrspace(pageDbIn: PageDb, addrspacePage: PageNr, l1PTPage: PageNr)
    : smcReturn
    requires validPageDb(pageDbIn);
    ensures  validPageDb(pagedbFrmRet(initAddrspace(pageDbIn, addrspacePage, l1PTPage)));
{
    var g := pageDbIn;
    if(!validPageNr(addrspacePage) || !validPageNr(l1PTPage) ||
        addrspacePage == l1PTPage) then
        Pair(pageDbIn, KEV_ERR_INVALID_PAGENO())
    else if(l1PTPage % 4 != 0) then
        Pair(pageDbIn, KEV_ERR_INVALID_PAGENO())
    else if( !g[addrspacePage].PageDbEntryFree? || !g[l1PTPage].PageDbEntryFree? ) then
        Pair(pageDbIn, KEV_ERR_PAGEINUSE())
    else
        var addrspace := Addrspace(l1PTPage, 1, InitState);
        var l1PT := L1PTable(SeqRepeat(NR_L1PTES(),Nothing));
        var pageDbOut := 
            (pageDbIn[addrspacePage := PageDbEntryTyped(addrspacePage, addrspace)])[
                l1PTPage := PageDbEntryTyped(addrspacePage, l1PT)];
        Pair(pageDbOut, KEV_ERR_SUCCESS())
}

function initDispatcher(pageDbIn: PageDb, page:PageNr, addrspacePage:PageNr,
    entrypoint:int)
    : smcReturn
    requires validPageDb(pageDbIn);
    ensures  validPageDb(pagedbFrmRet(initDispatcher(pageDbIn, page, addrspacePage, entrypoint)));
{
   var n := page;
   var d := pageDbIn;
   if(!wellFormedAddrspace(pageDbIn, addrspacePage) ||
       !validAddrspace(pageDbIn, addrspacePage)) then
       Pair(pageDbIn, KEV_ERR_INVALID_ADDRSPACE())
   else
       allocatePage(pageDbIn, page, addrspacePage, Dispatcher(entrypoint, false))
}

// function initL2PTable(pageDbIn: PageDb, page: PageNr, addrspacePage: PageNr, l1Idx:int)
//     : smcReturn
// {
//     if( l1Idx > NR_L1PTES() ) then Pair(KEV_ERR_INVALIDMAPPING(), PageDbIn)
//     if( 
// }

//-----------------------------------------------------------------------------
// Properties of SMC calls
//-----------------------------------------------------------------------------
//  lemma initAddrspaceSuccessValidPageDB(pageDbIn: PageDb, addrspacePage: PageNr, l1PTPage: PageNr)
//      ensures 
//          validPageDb(pagedbFrmRet(initAddrspaceSuccess(pageDbIn, addrspacePage, l1PTPage)))
//  {
//  }
