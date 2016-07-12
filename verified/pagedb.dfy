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
    && pageDbEntriesAddrspacesOk(d)
    && pageDbEntriesValid(d)
    && pageDbEntriesValidRefs(d)
}

predicate pageDbEntriesAddrspacesOk(d:PageDb)
    requires wellFormedPageDb(d)
{
    forall n :: n in d && d[n].PageDbEntryTyped? ==> pageDbEntryAddrspacesOk(d, n)
}

predicate pageDbEntriesValid(d:PageDb)
    requires wellFormedPageDb(d)
    requires pageDbEntriesAddrspacesOk(d)
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
        pageDbEntryAddrspacesOk(d, n) &&
        validPageDbEntryTyped(d, n))
}

predicate pageDbEntryAddrspacesOk(d: PageDb, n: PageNr)
    requires n in d && d[n].PageDbEntryTyped?
{
    var e := d[n];
    e.addrspace in d
    && d[e.addrspace].PageDbEntryTyped?
    && d[e.addrspace].entry.Addrspace?
}

predicate validPageDbEntryTyped(d: PageDb, n: PageNr)
    requires n in d && d[n].PageDbEntryTyped?
    requires pageDbEntryAddrspacesOk(d, n)
{
    var e := d[n];
    var addrspaceIsStopped := d[e.addrspace].entry.state == StoppedState;
    (e.entry.Addrspace? && wellFormedAddrspace(d, n))
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
            addrspaceRefCount(d, n) == 0
}

// predicate lemma_validPageDBImpliesWellFormedAddrspaces(d: PageDb, n: PageNr)
//     requires validPageDb(d)
//     requires wellFormedPageDb(d)
//     requires validPageNr(n)
//     requires d[n].PageDbEntryTyped? && d[n].entry.Addrspace?
//     ensures lemma_validPageDBImpliesWellFormedAddrspaces(d, n)
// {
//     wellFormedAddrspace(d, n) && validAddrspace(d, n)
// }

predicate validL1PTable(d: PageDb, n: PageNr)
    requires n in d && d[n].PageDbEntryTyped? && d[n].entry.L1PTable?
    requires var a := d[n].addrspace; a in d && d[a].PageDbEntryTyped? && d[a].entry.Addrspace?
{
    var e := d[n];
    var l1pt := e.entry.l1pt;
    // our addrspace points to us as the L1PT (there should be only one)
    d[e.addrspace].entry.l1ptnr == n
        // it's the right length (all page tables are this length)
        && |l1pt| == NR_L1PTES()
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
        && validPageNr(a.l1ptnr)
        && a.l1ptnr in d
        && d[a.l1ptnr].PageDbEntryTyped?
        && d[a.l1ptnr].entry.L1PTable?
        // correct refcount
        && a.refcount == addrspaceRefCount(d, n)
}

// returns the number of references to an addrspace page with the given index
function addrspaceRefCount(d: PageDb, addrspacePageNr: PageNr): nat
    requires addrspacePageNr in d
{
    // XXX: inlined validPageNr(n) to help dafny see that this set is bounded
    |(set n | 0 <= n < KEVLAR_SECURE_NPAGES() && n in d
        && d[n].PageDbEntryTyped?
        && n != addrspacePageNr
        && d[n].addrspace == addrspacePageNr)|
}

function initialPageDb(): PageDb
  ensures validPageDb(initialPageDb())
{
  imap n: PageNr | validPageNr(n) :: PageDbEntryFree
}

//-----------------------------------------------------------------------------
// PageDB Updates
//-----------------------------------------------------------------------------
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

