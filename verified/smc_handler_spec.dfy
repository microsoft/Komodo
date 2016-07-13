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


function allocateDispatcherPage(pageDbIn: PageDb, securePage: PageNr,
    addrspacePage:PageNr, entrypoint:int) : smcReturn
    requires validPageDb(pageDbIn)
    requires wellFormedAddrspace(pageDbIn, addrspacePage)
    requires validAddrspace(pageDbIn, addrspacePage)
    // ensures  validPageDb(pagedbFrmRet(allocateDispatcherPage(pageDbIn, securePage, addrspacePage, entrypoint )))
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
            securePage := PageDbEntryTyped(addrspacePage, Dispatcher(entrypoint, false))];
        var pageDbOut := pageDbUpdated[
            addrspacePage := PageDbEntryTyped(addrspacePage, updatedAddrspace)];
        
        // assert wellFormedPageDb(pageDbOut);
        // assert pageDbEntriesWellTypedAddrspace(pageDbOut);
        // assert validPageDbEntry(pageDbOut, addrspacePage);
        // 
        // //These two fail
        // assert validPageDbEntry(pageDbOut, securePage);
        // assert forall n :: n in pageDbOut && n != addrspacePage && n != securePage ==>
        //     validPageDbEntry(pageDbOut, n);
        // assert pageDbEntriesValid(pageDbOut);

        // assert pageDbEntriesValidRefs(pageDbOut);
        // assert validPageDb(pageDbOut);
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

        // Necessary semi-manual proof of validPageDbEntry(pageDbOut, l1PTPage)
        // The interesting part of the proof deals with the contents of addrspaceRefs
        assert forall p :: p != l1PTPage ==> !(p in addrspaceRefs(pageDbOut, addrspacePage));
		assert l1PTPage in addrspaceRefs(pageDbOut, addrspacePage);
        assert addrspaceRefs(pageDbOut, addrspacePage) == {l1PTPage};
        // only kept for readability
        assert validPageDbEntry(pageDbOut, l1PTPage);


        // Manual proof that the umodified pageDb entries are still valid. The only
        // interesting case is for addrspaces other than the newly created one.
        // Specifically, the only non-trivial aspect of validity is the reference
        // count. Their references are not corrupted because the only touched
        // pages only reference the newly created page.
        ghost var otherAddrspaces := set n : PageNr | 0 <= n < KEVLAR_SECURE_NPAGES()
             && pageDbOut[n].PageDbEntryTyped?
             && pageDbOut[n].entry.Addrspace?
             && n != addrspacePage && n != l1PTPage;
        assert forall n :: n in otherAddrspaces ==>
            addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
        // only kept for readability
        assert forall n :: n in otherAddrspaces  ==>
            validPageDbEntryTyped(pageDbOut, n);

        assert pageDbEntriesValid(pageDbOut);

        assert validPageDb(pageDbOut);
        Pair(pageDbOut, KEV_ERR_SUCCESS())
}

function initDispatcher(pageDbIn: PageDb, page:PageNr, addrspacePage:PageNr,
    entrypoint:int)
    : smcReturn
    requires validPageDb(pageDbIn);
    // ensures  validPageDb(pagedbFrmRet(initDispatcher(pageDbIn, page, addrspacePage, entrypoint)));
{
   var n := page;
   var d := pageDbIn;
   if(!wellFormedAddrspace(pageDbIn, addrspacePage) ||
       !validAddrspace(pageDbIn, addrspacePage)) then
       Pair(pageDbIn, KEV_ERR_INVALID_ADDRSPACE())
   else
       allocateDispatcherPage(pageDbIn, page, addrspacePage, entrypoint)
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
