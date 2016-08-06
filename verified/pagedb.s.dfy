include "kev_common.s.dfy"
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
    | InsecureMapping(insecurePage: InsecurePageNr, insecureWrite: bool)
    | NoMapping

datatype PageDbEntry
    = PageDbEntryFree
    | PageDbEntryTyped(addrspace: PageNr, entry: PageDbEntryTyped)

type PageDb = imap<PageNr, PageDbEntry>

predicate wellFormedPageDb(d: PageDb)
{
    forall n {:trigger validPageNr(n)} :: validPageNr(n) <==> n in d
}

// this is a weak predicate that simply says internal refs are all in bounds
predicate {:opaque} pageDbClosedRefs(d: PageDb)
    ensures pageDbClosedRefs(d) ==> wellFormedPageDb(d)
{
    wellFormedPageDb(d) && forall n :: validPageNr(n) ==> closedRefsPageDbEntry(d[n])
}

predicate {:opaque} validPageDb(d: PageDb)
    ensures validPageDb(d) ==> pageDbClosedRefs(d)
{
    wellFormedPageDb(d) && pageDbEntriesValid(d) && pageDbEntriesValidRefs(d)
}

predicate pageDbEntriesValid(d:PageDb)
    requires wellFormedPageDb(d)
    ensures pageDbEntriesValid(d) ==> pageDbClosedRefs(d)
{
    reveal_pageDbClosedRefs();
    forall n :: validPageNr(n) ==> validPageDbEntry(d, n)
}

predicate pageDbEntriesValidRefs(d: PageDb)
    requires wellFormedPageDb(d)
{
    forall n :: validPageNr(n) && d[n].PageDbEntryTyped? ==>  pageDbEntryValidRefs(d, n)
}

// Free pages and non-addrspace entries should have a refcount of 0
predicate pageDbEntryValidRefs(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
{
    var e := d[n];
    (e.PageDbEntryTyped? && e.entry.Addrspace?) ||
        |addrspaceRefs(d, n)| == 0
}

predicate validPageDbEntry(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
    //ensures validPageDbEntry(d, n) ==> closedRefsPageDbEntry(d[n])
{
    var e := d[n];
    e.PageDbEntryFree? ||
    (e.PageDbEntryTyped? && validPageDbEntryTyped(d, n))
}

predicate validPageDbEntryTyped(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
    requires d[n].PageDbEntryTyped?
{
    closedRefsPageDbEntry(d[n]) && isAddrspace(d, d[n].addrspace)
    // Type-specific requirements
    && (var entry := d[n].entry;
         (entry.Addrspace? && validAddrspace(d, n))
       || (entry.L1PTable? && validL1PTable(d, n))
       || (entry.L2PTable? && validL2PTable(d, n))
       || (entry.Dispatcher?)
       || (entry.DataPage?) )
}

predicate isAddrspace(d: PageDb, n: PageNr)
{
    wellFormedPageDb(d) && validPageNr(n)
        && d[n].PageDbEntryTyped?
        && d[n].entry.Addrspace?
}

predicate stoppedAddrspace(e: PageDbEntry)
{
    e.PageDbEntryTyped? && e.entry.Addrspace? && e.entry.state == StoppedState
}

predicate validAddrspace(d: PageDb, n: PageNr)
    requires isAddrspace(d, n)
    requires closedRefsPageDbEntry(d[n])
{
    var addrspace := d[n].entry;
    n == d[n].addrspace
        && addrspaceL1Unique(d, n)
        && addrspace.refcount == |addrspaceRefs(d, n)|
        && (stoppedAddrspace(d[n]) || (
            var l1pt := d[addrspace.l1ptnr];
            l1pt.PageDbEntryTyped? && l1pt.entry.L1PTable? && l1pt.addrspace == n
        ))
}

predicate addrspaceL1Unique(d: PageDb, n: PageNr)
    requires isAddrspace(d, n)
{
    var a := d[n].entry;
    forall p :: validPageNr(p) && p != a.l1ptnr && d[p].PageDbEntryTyped? && d[p].addrspace == n
        ==> !d[p].entry.L1PTable?
}

// taken from ironclad set libraries
function SetOfNumbersInRightExclusiveRange(a:int, b:int):set<int>
    requires a <= b;
    ensures forall opn :: a <= opn < b ==> opn in SetOfNumbersInRightExclusiveRange(a, b);
    ensures forall opn :: opn in SetOfNumbersInRightExclusiveRange(a, b) ==> a <= opn < b;
    ensures |SetOfNumbersInRightExclusiveRange(a, b)| == b-a;
    decreases b-a;
{
    if a == b then {} else {a} + SetOfNumbersInRightExclusiveRange(a+1, b)
}

function {:opaque} validPageNrs(): set<PageNr>
    ensures forall n :: n in validPageNrs() <==> validPageNr(n)
{
    SetOfNumbersInRightExclusiveRange(0, KEVLAR_SECURE_NPAGES())
}

// returns the set of references to an addrspace page with the given index
function addrspaceRefs(d: PageDb, addrspacePageNr: PageNr): set<PageNr>
    requires wellFormedPageDb(d) && validPageNr(addrspacePageNr)
{
    (set n | n in validPageNrs()
        && d[n].PageDbEntryTyped?
        && n != addrspacePageNr
        && d[n].addrspace == addrspacePageNr)
}

predicate validL1PTable(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
    requires closedRefsPageDbEntry(d[n])
    requires d[n].PageDbEntryTyped? && d[n].entry.L1PTable?
{
    var l1pt := d[n].entry.l1pt;
    var a := d[n].addrspace;
    stoppedAddrspace(d[a]) || (
        // each non-zero entry is a valid L2PT belonging to this address space
        forall pte :: pte in l1pt && pte.Just? ==> (
            var pteE := fromJust(pte);
            d[pteE].PageDbEntryTyped? && d[pteE].addrspace == a && validL1PTE(d, pteE))
        // no L2PT is referenced twice
        && forall i, j :: 0 <= i < |l1pt| && 0 <= j < |l1pt| && l1pt[i].Just? && i != j
            ==> l1pt[i] != l1pt[j]
    )
}

predicate validL1PTE(d: PageDb, pte: PageNr)
    requires wellFormedPageDb(d)
{
    validPageNr(pte)
        && d[pte].PageDbEntryTyped?
        && d[pte].entry.L2PTable?
}

predicate validL2PTable(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
    requires closedRefsPageDbEntry(d[n])
    requires d[n].PageDbEntryTyped? && d[n].entry.L2PTable?
{
    var a := d[n].addrspace;
    stoppedAddrspace(d[a]) || (
        forall pte :: pte in d[n].entry.l2pt && pte.SecureMapping? ==> (
        // Not needed when addrspace is stopped 
        // each secure entry is a valid data page belonging to this address space
            var pg := pte.page;
            d[pg].PageDbEntryTyped? && d[pg].addrspace == a && validL2PTE(d, pg))
    )
}

predicate validL2PTE(d: PageDb, pte: PageNr)
    requires wellFormedPageDb(d)
{
    validPageNr(pte)
        && d[pte].PageDbEntryTyped?
        && d[pte].entry.DataPage?
}

predicate closedRefsPageDbEntry(e: PageDbEntry)
{
    e.PageDbEntryFree? ||
        (e.PageDbEntryTyped?
        && validPageNr(e.addrspace)
        && closedRefsPageDbEntryTyped(e.entry))
}

predicate closedRefsPageDbEntryTyped(e: PageDbEntryTyped)
{
    (e.Addrspace? && validPageNr(e.l1ptnr) )
    || (e.L1PTable? && closedRefsL1PTable(e))
    || (e.L2PTable? && closedRefsL2PTable(e))
    || (e.Dispatcher? )
    || (e.DataPage? )
}

predicate closedRefsL1PTable(e: PageDbEntryTyped)
    requires e.L1PTable?
{
    var l1pt := e.l1pt;
    |l1pt| == NR_L1PTES()
    && forall pte :: pte in l1pt && pte.Just? ==> validPageNr(fromJust(pte))
}

predicate closedRefsL2PTable(e: PageDbEntryTyped)
    requires e.L2PTable?
{
    var l2pt := e.l2pt;
    |l2pt| == NR_L2PTES()
    && forall pte :: pte in l2pt ==> closedRefsL2PTE(pte)
}

predicate closedRefsL2PTE(pte: L2PTE)
{
    match pte
        case SecureMapping(p, w, e) => validPageNr(p)
        case InsecureMapping(p, w)
            => 0 <= p < KEVLAR_PHYSMEM_LIMIT() / KEVLAR_PAGE_SIZE()
        case NoMapping => true
}

/*
function initialPageDb(): PageDb
  ensures validPageDb(initialPageDb())
{
  imap n: PageNr | validPageNr(n) :: PageDbEntryFree
}
*/
