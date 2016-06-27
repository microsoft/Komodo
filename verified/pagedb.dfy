// -*- dafny-prover-local-args: ("/noNLarith") -*-

include "kev_constants.dfy"

type PageNr = int

predicate validPageNr(p: PageNr)
{
  0 <= p < KEVLAR_SECURE_NPAGES()
}

datatype AddrspaceState = InitState | FinalState | StoppedState

datatype PageDbEntryTyped
  = Addrspace(l1pt: PageNr, refcount: nat, state: AddrspaceState)
  | Dispatcher(entered: bool)
  | L1PTable
  | L2PTable
  | DataPage

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
  e.addrspace in d
  && d[e.addrspace].PageDbEntryTyped?
  && d[e.addrspace].entry.Addrspace?
  // type-specific checks
  && (
    (e.entry.Addrspace? && validAddrspace(d, n))
    || (e.entry.Dispatcher?)
    || (e.entry.L1PTable? && d[e.addrspace].entry.l1pt == n)
    || (e.entry.L2PTable?)
    || (e.entry.DataPage?)
  )
}

predicate validAddrspace(d: PageDb, n: PageNr)
  requires n in d && d[n].PageDbEntryTyped?
{
  var a := d[n].entry;
  a.Addrspace? && (
    // valid L1PT page
    validPageNr(a.l1pt) && a.l1pt in d && d[a.l1pt].PageDbEntryTyped?
    && d[a.l1pt].entry.L1PTable?
    // correct refcount
    && a.refcount == addrspaceRefcount(d, n)
    )
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
