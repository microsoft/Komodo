include "kev_constants.dfy"

type PageNr = int

datatype AddrspaceState = InitState | FinalState | StoppedState
datatype Addrspace = Addrspace(l1pt: PageNr, refcount: nat, state: AddrspaceState)

datatype PageType = AddrspacePage | DispatcherPage
  | L1PTablePage | L2PTablePage | DataPage

datatype PageDbEntry = PageDbFree | PageDbTyped(t: PageType, a: Addrspace)
type PageDb = map<PageNr, PageDbEntry>

predicate validPageNr(p: PageNr)
{
  0 <= p < KEVLAR_SECURE_NPAGES()
}

predicate validPageDb(d: PageDb)
{
  true // TODO!
}

function initialPageDb(): PageDb
  ensures validPageDb(initialPageDb())
{
  map n: PageNr | 0 <= n < KEVLAR_SECURE_NPAGES() :: PageDbFree
}
