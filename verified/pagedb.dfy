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
    | Dispatcher(entered: bool)
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

predicate validPageDb(d: PageDb)
{
    // the domain of d must equal all valid pages
    forall n :: validPageNr(n) <==> n in d
        // all entries are valid
        && forall n :: n in d ==> validPageDbEntry(d, n)
}

predicate validPageDbEntry(d: PageDb, n: PageNr)
    requires n in d
{
    var e := d[n];
    e.PageDbEntryFree? || (e.PageDbEntryTyped? && validPageDbEntryTyped(d, n))
}

predicate validPageDbEntryTyped(d: PageDb, n: PageNr)
    requires n in d && d[n].PageDbEntryTyped?
{
    var e := d[n];
    // check that the addrspace ref is to a page of the right type
    // (we'll check its validity when we check that entry)
    e.addrspace in d && (
    var addrspace := d[e.addrspace];
    addrspace.PageDbEntryTyped? && addrspace.entry.Addrspace?
    // type-specific checks
    && (
        var addrspaceIsStopped := addrspace.entry.state == StoppedState;
        (e.entry.Addrspace? && validAddrspace(d, n))
        || (e.entry.L1PTable? && (addrspaceIsStopped || validL1PTable(d, n)))
        || (e.entry.L2PTable? && (addrspaceIsStopped || validL2PTable(d, n)))
        || (e.entry.Dispatcher?)
        || (e.entry.DataPage?)
    ))
}

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

predicate validAddrspace(d: PageDb, n: PageNr)
    requires n in d && d[n].PageDbEntryTyped? && d[n].entry.Addrspace?
{
    var a := d[n].entry;
    // valid L1PT page
    validPageNr(a.l1ptnr)
        && a.l1ptnr in d
        && d[a.l1ptnr].PageDbEntryTyped?
        && d[a.l1ptnr].entry.L1PTable?
        // correct refcount
        && a.refcount == addrspaceRefcount(d, n)
}

// returns the number of references to an addrspace page with the given index
function addrspaceRefcount(d: PageDb, addrspacePageNr: PageNr): nat
    requires addrspacePageNr in d
{
    // XXX: inlined validPageNr(n) to help dafny see that this set is bounded
    |(set n | 0 <= n < KEVLAR_SECURE_NPAGES() && n in d
        && d[n].PageDbEntryTyped? && n != addrspacePageNr
        && d[n].addrspace == addrspacePageNr)|
}

function initialPageDb(): PageDb
  ensures validPageDb(initialPageDb())
{
  imap n: PageNr | validPageNr(n) :: PageDbEntryFree
}
