include "kev_constants.dfy"
include "Maybe.dfy"
include "pagedb.dfy"

datatype smcReturn = Pair(pageDbOut: PageDb, err: int)

// TODO FIXME!!
function mon_vmap(p:PageNr) : int {
    p 
}

//Returns a sequence containing n instances of T.
function seqTimesN<T>(datum:T, n:int) : seq<T>
    requires n >= 0;
    decreases n;
{
    if n == 0 then []
    else 
        if n == 1 then [datum]
        else [datum] + seqTimesN(datum, n-1)
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
    requires validPageDb(pageDbIn);
    requires validAddrspace(pageDbIn, addrspacePage);
    requires wellFormedAddrspace(pageDbIn, addrspacePage);
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
        var pageDbOut := pageDbIn[ securePage :=
            PageDbEntryTyped(addrspacePage, pageType) ][
            addrspacePage := PageDbEntryTyped(addrspacePage, updatedAddrspace)];
        Pair(pageDbOut, KEV_ERR_SUCCESS())
}

// init_addrspace is split into two cases because the current implementation
// in spartan is split into two parts: one produces error cases, and one handles
// just the success case. The spartan implementation is split
// into two cases for performance, but this may no longer be necessary.
function initAddrspaceSuccess(pageDbIn: PageDb, addrspacePage: PageNr, l1PTPage: PageNr)
    : smcReturn
    requires validPageDb(pageDbIn);
    requires validPageNr(addrspacePage);
    requires validPageNr(l1PTPage);
    //ensures  validPageDb(pagedbFrmRet(initAddrspaceSuccess(pageDbIn, addrspacePage, l1PTPage)));
{
        var addrspace := Addrspace(l1PTPage, 1, InitState);
        var l1PT := L1PTable(seqTimesN(Nothing,NR_L1PTES()));
        var pageDbOut := 
            pageDbIn[addrspacePage := PageDbEntryTyped(addrspacePage, addrspace)][
                l1PTPage := PageDbEntryTyped(addrspacePage, l1PT)];
        Pair( pageDbOut, KEV_ERR_SUCCESS())
}

function initAddrspace(pageDbIn: PageDb, addrspacePage: PageNr, l1PTPage: PageNr)
    : smcReturn
    requires validPageDb(pageDbIn);
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
        initAddrspaceSuccess(pageDbIn, addrspacePage, l1PTPage)
}

function initDispatcher(pageDbIn: PageDb, page:PageNr, addrspacePage:PageNr,
    entrypoint:int)
    : smcReturn
    requires validPageDb(pageDbIn);
{
   var n := page;
   var d := pageDbIn;
   if(!validAddrspace(pageDbIn, addrspacePage) ||
       !wellFormedAddrspace(pageDbIn, addrspacePage)) then
       Pair(pageDbIn, KEV_ERR_INVALID_ADDRSPACE())
   else
       allocatePage(pageDbIn, page, addrspacePage, Dispatcher(entrypoint, false))
}

function initL2PTable(

//-----------------------------------------------------------------------------
// Properties of SMC calls
//-----------------------------------------------------------------------------
//  lemma initAddrspaceSuccessValidPageDB(pageDbIn: PageDb, addrspacePage: PageNr, l1PTPage: PageNr)
//      ensures 
//          validPageDb(pagedbFrmRet(initAddrspaceSuccess(pageDbIn, addrspacePage, l1PTPage)))
//  {
//  }
