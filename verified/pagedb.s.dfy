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
    | InsecureMapping(insecurePage: InsecurePageNr)
    | NoMapping

datatype PageDbEntry
    = PageDbEntryFree
    | PageDbEntryTyped(addrspace: PageNr, entry: PageDbEntryTyped)

type PageDb = imap<PageNr, PageDbEntry>

predicate wellFormedPageDb(d: PageDb)
{
    forall n {:trigger validPageNr(n)} :: validPageNr(n) <==> n in d
}

predicate {:opaque} validPageDb(d: PageDb)
{
    wellFormedPageDb(d)
    && pageDbEntriesValidRefs(d)
    && pageDbEntriesValid(d)
}

// this is a weak predicate that simply says the page number refs are valid
predicate {:opaque} pageDbClosedRefs(d: PageDb)
{
    wellFormedPageDb(d) && (forall n {:trigger validPageNr(n)} :: (validPageNr(n) && d[n].PageDbEntryTyped?)
        ==> (validPageNr(d[n].addrspace) && closedRefsPageDbEntry(d[n].entry)))
}

lemma validPageDbImpliesClosedRefs(d: PageDb)
    requires validPageDb(d)
    ensures pageDbClosedRefs(d)
    {reveal_validPageDb(); reveal_pageDbClosedRefs();}

predicate pageDbEntriesValid(d:PageDb)
    requires wellFormedPageDb(d)
{
    forall n :: validPageNr(n) ==> validPageDbEntry(d, n)
}

predicate pageDbEntriesValidRefs(d: PageDb)
    requires wellFormedPageDb(d)
{
    forall n :: validPageNr(n) && d[n].PageDbEntryTyped? ==> 
        pageDbEntryValidRefs(d, n)
}

// Free pages and non-addrspace entries should have a refcount of 0
predicate pageDbEntryValidRefs(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
{
    var e := d[n];
    (e.PageDbEntryTyped? && e.entry.Addrspace?) ||
        forall m : PageNr :: validPageNr(m) ==>
            |addrspaceRefs(d, n)| == 0
}

predicate validPageDbEntry(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
{
    var e := d[n];
    e.PageDbEntryFree? ||
    (e.PageDbEntryTyped? && validPageDbEntryTyped(d, n))
}

predicate validPageDbEntryTyped(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
    requires d[n].PageDbEntryTyped?
{
    var e := d[n].entry;
    closedRefsPageDbEntry(e) && pageDbEntryOk(d, n)
}

predicate isAddrspace(d: PageDb, n: PageNr)
{
    wellFormedPageDb(d) && validPageNr(n) && d[n].PageDbEntryTyped? && d[n].entry.Addrspace?
}

// The addrspace of the thing pointed to by n is stopped
predicate stoppedAddrspace(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
    requires d[n].PageDbEntryTyped?
{
    var a := d[n].addrspace;
    isAddrspace(d, a) && d[a].entry.state == StoppedState
}

predicate pageDbEntryOk(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
    requires d[n].PageDbEntryTyped?
{
    var entry := d[n].entry;
    var addrspace := d[n].addrspace;
    isAddrspace(d, addrspace)
    // Type-specific requirements
    && ( (entry.Addrspace? && validAddrspace(d, n))
       || (entry.L1PTable? && validL1PTable(d, n))
       || (entry.L2PTable? && validL2PTable(d, n))
       || (entry.Dispatcher?)
       || (entry.DataPage?) )
    
}

predicate validAddrspace(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
    requires d[n].PageDbEntryTyped? && d[n].entry.Addrspace?
    requires var a:= d[n].addrspace; isAddrspace(d, a)
{
        var a := d[n].addrspace;
        var addrspace := d[a].entry;
        n == a
        && addrspaceL1Unique(d, a)
        && addrspace.refcount == |addrspaceRefs(d, a)|
        && (stoppedAddrspace(d, n) ||  (
            d[addrspace.l1ptnr].PageDbEntryTyped? &&
            d[addrspace.l1ptnr].entry.L1PTable? &&
            d[addrspace.l1ptnr].addrspace == n
        ))
}

predicate addrspaceL1Unique(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
    requires d[n].PageDbEntryTyped? && d[n].entry.Addrspace?
{
    var a := d[n].entry;
    a.l1ptnr in d &&
    forall p :: validPageNr(p) && p != a.l1ptnr &&
        d[p].PageDbEntryTyped? && d[p].addrspace == n ==>
        !d[p].entry.L1PTable?
}

// returns the set of references to an addrspace page with the given index
function addrspaceRefs(d: PageDb, addrspacePageNr: PageNr): set<PageNr>
    requires wellFormedPageDb(d) && validPageNr(addrspacePageNr)
{
    // XXX: inlined validPageNr(n) to help dafny see that this set is bounded
    (set n | validPageNr(n) && 0 <= n < KEVLAR_SECURE_NPAGES()
        && d[n].PageDbEntryTyped?
        && n != addrspacePageNr
        && d[n].addrspace == addrspacePageNr)
}

predicate validL1PTable(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d) && validPageNr(n)
    requires d[n].PageDbEntryTyped? && d[n].entry.L1PTable?
    requires var a:= d[n].addrspace; isAddrspace(d, a)
{
    var e := d[n];
    var l1pt := e.entry.l1pt;
    var a := d[n].addrspace;
    stoppedAddrspace(d, n) || (
        forall pte :: pte in l1pt && pte.Just? ==> ( var pteE := fromJust(pte);
            pteE in d && d[pteE].PageDbEntryTyped? && d[pteE].addrspace == a )
        // each non-zero entry is a valid L2PT belonging to this address space
        && forall pte :: pte in l1pt && pte.Just? ==> validL1PTE(d, fromJust(pte))
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
    requires d[n].PageDbEntryTyped? && d[n].entry.L2PTable?
    requires var a:= d[n].addrspace; isAddrspace(d, a)
{
    var e := d[n];
    var l2pt := e.entry.l2pt;
    var a:= d[n].addrspace;
    stoppedAddrspace(d, n) || (
        forall pte :: pte in l2pt && pte.SecureMapping? ==> (
            var ptePg := pte.page;
            ptePg in d && d[ptePg].PageDbEntryTyped? && d[ptePg].addrspace == a)
        // Not needed when addrspace is stopped 
        // each secure entry is a valid data page belonging to this address space
        && forall pte :: pte in l2pt && pte.SecureMapping?
            ==> validL2PTE(d, pte.page)
    )
}

predicate validL2PTE(d: PageDb, pte: PageNr)
    requires wellFormedPageDb(d)
{
    validPageNr(pte)
        && d[pte].PageDbEntryTyped?
        && d[pte].entry.DataPage?
}

predicate closedRefsPageDbEntry(e: PageDbEntryTyped)
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
    // && forall pte :: pte in l2pt ==> (match pte
    //     case SecureMapping(p, w, e) => validPageNr(p)
    //     case InsecureMapping(p) => true
    //     case NoMapping => true)
}

/*
function initialPageDb(): PageDb
  ensures validPageDb(initialPageDb())
{
  imap n: PageNr | validPageNr(n) :: PageDbEntryFree
}
*/
