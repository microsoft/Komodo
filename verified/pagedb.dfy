include "kev_constants.dfy"
include "Maybe.dfy"

type PageNr = int
type InsecurePageNr = int

function NR_L1PTES(): int { 256 }
function NR_L2PTES(): int { 1024 }

predicate validPageNr(p: PageNr)
{
    0 <= p < KEVLAR_SECURE_NPAGES()
}

datatype AddrspaceState = InitState | FinalState | StoppedState

datatype PageDbEntryTyped
    = Addrspace(l1ptnr: PageNr, refcount: nat, state: AddrspaceState)
    | Dispatcher(entrypoint:int, entered: bool)
    | L1PTable(l1pt: seq<Maybe<PageNr>>)
    | L2PTable(l2pt: seq<L2PTE>)
    | DataPage

datatype L2PTE
    = SecureMapping(page: PageNr, write: bool, exec: bool)
    | InsecureMapping(insecurePage: InsecurePageNr)
    | NoMapping

datatype PageDbEntry
    = PageDbEntryFree
    | PageDbEntryTyped(addrspace: PageNr, entry: PageDbEntryTyped)

type PageDb = imap<PageNr, PageDbEntry>

predicate wellFormedPageDb(d: PageDb)
{
    forall n :: validPageNr(n) <==> n in d
}

predicate validPageDb(d: PageDb)
{
    wellFormedPageDb(d)
    && pageDbEntriesValidRefs(d)
    && pageDbEntriesWellTypedAddrspace(d)
    && pageDbEntriesValid(d)
}

predicate pageDbEntriesWellTypedAddrspace(d:PageDb)
    requires wellFormedPageDb(d)
{
    forall n :: n in d && d[n].PageDbEntryTyped? ==> pageDbEntryWellTypedAddrspace(d, n)
}

predicate pageDbEntriesValid(d:PageDb)
    requires wellFormedPageDb(d)
    requires pageDbEntriesWellTypedAddrspace(d)
{
    forall n :: n in d ==> validPageDbEntry(d, n)
}

predicate pageDbEntriesValidRefs(d: PageDb)
{
    forall n :: n in d && d[n].PageDbEntryTyped? ==> 
        pageDbEntryValidRefs(d, n)
}

predicate validPageDbEntry(d: PageDb, n: PageNr)
    requires n in d
{
    var e := d[n];
    e.PageDbEntryFree? || (e.PageDbEntryTyped? &&
        pageDbEntryWellTypedAddrspace(d, n) &&
        validPageDbEntryTyped(d, n))
}

predicate pageDbEntryWellTypedAddrspace(d: PageDb, n: PageNr)
    requires n in d && d[n].PageDbEntryTyped?
{
    var e := d[n];
    e.addrspace in d
    && d[e.addrspace].PageDbEntryTyped?
    && d[e.addrspace].entry.Addrspace?
}

predicate validPageDbEntryTyped(d: PageDb, n: PageNr)
    requires n in d && d[n].PageDbEntryTyped?
    requires pageDbEntryWellTypedAddrspace(d, n)
{
    var e := d[n];
    var addrspaceIsStopped := d[e.addrspace].entry.state == StoppedState;
    (e.entry.Addrspace? && wellFormedAddrspace(d, n) && validAddrspace(d, n))
    || (e.entry.L1PTable? && (addrspaceIsStopped || validL1PTable(d, n)))
    || (e.entry.L2PTable? && (addrspaceIsStopped || validL2PTable(d, n)))
    || (e.entry.Dispatcher? )
    || (e.entry.DataPage? )
}

// Free pages and non-addrspace entries should have a refcount of 0
predicate pageDbEntryValidRefs(d: PageDb, n: PageNr)
    requires n in d
{
    var e := d[n];
    (e.PageDbEntryTyped? && e.entry.Addrspace?) ||
        forall m : PageNr :: validPageNr(m) ==>
            |addrspaceRefs(d, n)| == 0
}

predicate validL1PTable(d: PageDb, n: PageNr)
    requires n in d && d[n].PageDbEntryTyped? && d[n].entry.L1PTable?
    // requires var a := d[n].addrspace; a in d && d[a].PageDbEntryTyped? && d[a].entry.Addrspace?
{
    var e := d[n];
    var l1pt := e.entry.l1pt;
    // our addrspace points to us as the L1PT (there should be only one)
    // d[e.addrspace].entry.l1ptnr == n
        // it's the right length (all page tables are this length)
        |l1pt| == NR_L1PTES()
        // each non-zero entry is a valid L2PT belonging to this address space
        && forall pte :: pte in l1pt && pte.Just? ==> validL1PTE(d, e.addrspace, fromJust(pte))
        // no L2PT is referenced twice
        && forall i, j :: 0 <= i < |l1pt| && 0 <= j < |l1pt| && l1pt[i].Just? && i != j
            ==> l1pt[i] != l1pt[j]
}

predicate validL1PTE(d: PageDb, addrspace: PageNr, pte: PageNr)
{
    pte in d
        && d[pte].PageDbEntryTyped?
        && d[pte].addrspace == addrspace
        && d[pte].entry.L2PTable?
}

predicate validL2PTable(d: PageDb, n: PageNr)
    requires n in d && d[n].PageDbEntryTyped? && d[n].entry.L2PTable?
{
    var l2pt := d[n].entry.l2pt;
    |l2pt| == NR_L2PTES()
    // each secure entry is a valid data page belonging to this address space
    && forall pte :: pte in l2pt && pte.SecureMapping?
        ==> validL2PTE(d, d[n].addrspace, pte.page)
}

predicate validL2PTE(d: PageDb, addrspace: PageNr, pte: PageNr)
{
    pte in d
        && d[pte].PageDbEntryTyped?
        && d[pte].addrspace == addrspace
        && d[pte].entry.DataPage?
}

predicate wellFormedAddrspace(d: PageDb, n: PageNr)
    { n in d && d[n].PageDbEntryTyped? && d[n].entry.Addrspace? }
   
predicate validAddrspace(d: PageDb, n: PageNr)
    requires wellFormedAddrspace(d, n);
{
    var a := d[n].entry;
    // valid L1PT page
    wellFormedAddrspace(d, n)
        && addrspaceL1Unique(d, n)
        && validPageNr(a.l1ptnr)
        && a.l1ptnr in d
        && d[a.l1ptnr].PageDbEntryTyped?
        && d[a.l1ptnr].entry.L1PTable?
        // correct refcount
        && a.refcount == |addrspaceRefs(d, n)|
}

predicate addrspaceL1Unique(d: PageDb, n: PageNr)
    requires wellFormedAddrspace(d, n);
{
    var a := d[n].entry;
    a.l1ptnr in d &&
    forall p :: p in d && p != a.l1ptnr &&
        d[p].PageDbEntryTyped? && d[p].addrspace == n ==>
        !d[p].entry.L1PTable?
}


// returns the number of references to an addrspace page with the given index
function addrspaceRefs(d: PageDb, addrspacePageNr: PageNr): set<PageNr>
    requires addrspacePageNr in d
{
    // XXX: inlined validPageNr(n) to help dafny see that this set is bounded
    (set n | 0 <= n < KEVLAR_SECURE_NPAGES() && n in d
        && d[n].PageDbEntryTyped?
        && n != addrspacePageNr
        && d[n].addrspace == addrspacePageNr)
}


function initialPageDb(): PageDb
  ensures validPageDb(initialPageDb())
{
  imap n: PageNr | validPageNr(n) :: PageDbEntryFree
}

//-----------------------------------------------------------------------------
// PageDB Updates
//-----------------------------------------------------------------------------


// Given than p may have changed but n has not changed, n is still valid as long as
// it is not an address space
lemma updatesPreserveNonAddrspaceEntryValidity(pageDbIn: PageDb, pageDbOut: PageDb,
    n: PageNr, p:PageNr)

    // Implies that n is valid in pageDbIn
    requires validPageDb(pageDbIn);
    requires wellFormedPageDb(pageDbOut);

    requires validPageNr(n);
    requires validPageNr(p);

    // p is not an address space
    requires 
        var e := pageDbIn[p];
        !(e.PageDbEntryTyped? && e.entry.Addrspace?)
    // n is unchanged by the update
    requires
        pageDbIn[n] == pageDbOut[n]

    // check special cases for debugging
    requires
        pageDbIn[n].PageDbEntryTyped? && pageDbIn[n].entry.Dispatcher?
    requires
        pageDbOut[n].PageDbEntryTyped? && pageDbOut[n].entry.Dispatcher?
    requires
        pageDbEntryWellTypedAddrspace(pageDbOut, n);
    ensures
        validPageDbEntryTyped(pageDbOut, n);
        
{
}

// predicate lemma_updateValidityPreservation(pIn: PageDb, pOut: PageDb, n: PageNr)
//     requires wellFormedPageDb(pIn)
//     requires wellFormedPageDb(pOut)
//     requires validPageNr(n)
//     requires pIn[n].PageDbEntryTyped?
//     requires pOut[n].PageDbEntryTyped?
//     requires pageDbEntryWellTypedAddrspace(pIn, n)
//     requires pageDbEntryWellTypedAddrspace(pOut, n)
//     requires pIn[n].addrspace == pOut[n].addrspace
//     requires pIn[n].entry == pOut[n].entry
//     requires validPageDbEntryTyped(pIn, n)
//     ensures lemma_updateValidityPreservation(pIn, pOut, n)
// {
//     validPageDbEntryTyped(pOut, n)
// }

// lemma updatesToFreeEntriesPreserveValidity(pageDbIn: PageDb, pageDbOut: PageDb, p:PageNr)
//     requires validPageDb(pageDbIn);
//     requires wellFormedPageDb(pageDbOut);
//     requires validPageNr(p);
//     requires pageDbIn[p].PageDbEntryFree?
//     requires pageDbOut[p].PageDbEntryTyped?
//     requires !pageDbOut[p].entry.Addrspace?
//     requires forall n :: n in pageDbIn && n != p &&
//         n != pageDbOut[p].addrspace ==> pageDbOut[n] == pageDbIn[n]
//     ensures  forall n :: n in pageDbIn && n != p &&
//         n != pageDbOut[p].addrspace ==> validPageDbEntry(pageDbOut, n)
// {
// }

