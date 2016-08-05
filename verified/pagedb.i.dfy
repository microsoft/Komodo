include "pagedb.s.dfy"
include "kev_common.i.dfy"

//-----------------------------------------------------------------------------
// Data Structures
//-----------------------------------------------------------------------------
// computes byte offset of a specific pagedb entry
function method G_PAGEDB_ENTRY(pageno:int):int 
    requires 0 <= pageno < KEVLAR_SECURE_NPAGES();
    ensures G_PAGEDB_ENTRY(pageno) == pageno * PAGEDB_ENTRY_SIZE();
    ensures WordAligned(G_PAGEDB_ENTRY(pageno))
{
    assert WordAligned(PAGEDB_ENTRY_SIZE());
    pageno * PAGEDB_ENTRY_SIZE()
}

// entry = start offset of pagedb entry
function method PAGEDB_ENTRY_TYPE():int { 0 }
function method PAGEDB_ENTRY_ADDRSPACE():int { 4 }

// addrspc = start address of address space metadata
function method ADDRSPACE_L1PT():int    { 0 }
function method ADDRSPACE_L1PT_PHYS():int { 4 }
function method ADDRSPACE_REF():int     { 8 }
function method ADDRSPACE_STATE():int   { 12 }
function method ADDRSPACE_SIZE():int    { 16 }

//-----------------------------------------------------------------------------
// Page Types
//-----------------------------------------------------------------------------
function method KEV_PAGE_FREE():int
    ensures KEV_PAGE_FREE() == 0; { 0 }
function method KEV_PAGE_ADDRSPACE():int
    ensures KEV_PAGE_ADDRSPACE() == 1; { 1 }
function method KEV_PAGE_DISPATCHER():int
    ensures KEV_PAGE_DISPATCHER() == 2; { 2 }
function method KEV_PAGE_L1PTABLE():int
    ensures KEV_PAGE_L1PTABLE() == 3; { 3 }
function method KEV_PAGE_L2PTABLE():int
    ensures KEV_PAGE_L2PTABLE() == 4; { 4 }
function method KEV_PAGE_DATA():int
    ensures KEV_PAGE_DATA() == 5; { 5 }

//-----------------------------------------------------------------------------
// Address Space States
//-----------------------------------------------------------------------------
function method KEV_ADDRSPACE_INIT():int
    ensures KEV_ADDRSPACE_INIT() == 0; { 0 }
function method KEV_ADDRSPACE_FINAL():int              { 1 }
function method KEV_ADDRSPACE_STOPPED():int            { 2 }

//-----------------------------------------------------------------------------
//
//-----------------------------------------------------------------------------

predicate addrInPage(m:mem, p:PageNr)
    requires validPageNr(p)
{
    WordAligned(m) && page_monvaddr(p) <= m < page_monvaddr(p) + KEVLAR_PAGE_SIZE()
}

predicate memContainsPage(memmap: map<mem, int>, p:PageNr)
    requires validPageNr(p)
{
    forall m :: addrInPage(m,p) ==> m in memmap
}

function extractPage(s:memstate, p:PageNr): map<mem, int>
    requires SaneMem(s)
    requires validPageNr(p)
    ensures memContainsPage(extractPage(s,p), p)
{
    // XXX: expanded addrInPage() to help Dafny see a bounded set
    (map m | WordAligned(m)
        && page_monvaddr(p) <= m < page_monvaddr(p) + KEVLAR_PAGE_SIZE()
        :: s.addresses[m])
}

function extractPageDbEntry(s:memstate, p:PageNr): seq<int>
    requires SaneMem(s)
    requires validPageNr(p)
    ensures |extractPageDbEntry(s,p)| == BytesToWords(PAGEDB_ENTRY_SIZE())
    ensures forall o :: WordAligned(o) && 0 <= o < PAGEDB_ENTRY_SIZE()
        ==> GlobalWord(s, PageDb(), G_PAGEDB_ENTRY(p) + o)
            == extractPageDbEntry(s,p)[BytesToWords(o)]
{
    var fulldb := GlobalFullContents(s, PageDb());
    assert |fulldb| == BytesToWords(G_PAGEDB_SIZE());
    var entrylen := BytesToWords(PAGEDB_ENTRY_SIZE());
    fulldb[p*entrylen..p*entrylen+entrylen]
}

predicate pageDbCorresponds(s:memstate, pagedb:PageDb)
    requires SaneMem(s)
    requires pageDbClosedRefs(pagedb)
{
    reveal_pageDbClosedRefs();
    // XXX: unpack the entry and page contents here to help dafny see
    // that we have no other dependencies on the state
    var db := (map p | 0 <= p < KEVLAR_SECURE_NPAGES() :: extractPageDbEntry(s,p));
    var secpages := (map p | 0 <= p < KEVLAR_SECURE_NPAGES() :: extractPage(s,p));
    forall p {:trigger validPageNr(p)} :: validPageNr(p)
        ==> (pageDbEntryCorresponds(p, pagedb[p], db[p])
            && pageContentsCorresponds(p, pagedb[p], secpages[p]))
}

predicate pageDbCorrespondsExcluding(s:memstate, pagedb:PageDb, modifiedPage:PageNr)
    requires SaneMem(s)
    requires pageDbClosedRefs(pagedb)
{
    reveal_pageDbClosedRefs();
    forall p {:trigger validPageNr(p)} :: validPageNr(p) && p != modifiedPage
        ==> (pageDbEntryCorresponds(p, pagedb[p], extractPageDbEntry(s, p))
            && pageContentsCorresponds(p, pagedb[p], extractPage(s, p)))
}

predicate pageDbCorrespondsOnly(s:memstate, pagedb:PageDb, p:PageNr)
    requires SaneMem(s)
    requires pageDbClosedRefs(pagedb)
    requires validPageNr(p)
{
    reveal_pageDbClosedRefs();
    pageDbEntryCorresponds(p, pagedb[p], extractPageDbEntry(s, p))
    && pageContentsCorresponds(p, pagedb[p], extractPage(s, p))
}

predicate {:opaque} pageDbEntryCorresponds(p:PageNr, e:PageDbEntry, entryWords:seq<int>)
    requires validPageNr(p)
    requires |entryWords| == BytesToWords(PAGEDB_ENTRY_SIZE())
    requires e.PageDbEntryTyped?
        ==> validPageNr(e.addrspace) && closedRefsPageDbEntry(e.entry)
{
    pageDbEntryTypeVal(e) == entryWords[BytesToWords(PAGEDB_ENTRY_TYPE())]
    && match e {
        case PageDbEntryFree => true
        case PageDbEntryTyped(addrspace, entry) =>
            entryWords[BytesToWords(PAGEDB_ENTRY_ADDRSPACE())]
                == page_monvaddr(addrspace)
    }
}

predicate {:opaque} pageContentsCorresponds(p:PageNr, e:PageDbEntry, page:map<mem, int>)
    requires validPageNr(p)
    requires memContainsPage(page, p)
    requires e.PageDbEntryFree? || closedRefsPageDbEntry(e.entry)
{
    e.PageDbEntryFree? || (e.PageDbEntryTyped? && (
        var et := e.entry;
        (et.Addrspace? && pageDbAddrspaceCorresponds(p, et, page))
        || (et.Dispatcher? && pageDbDispatcherCorresponds(p, et, page))
        || (et.L1PTable? /* && pageDbL1PTableCorresponds(p, et, page) */)
        || (et.L2PTable? /* && pageDbL2PTableCorresponds(p, et, page) */)
        || et.DataPage?))
}

predicate pageDbAddrspaceCorresponds(p:PageNr, e:PageDbEntryTyped, page:map<mem, int>)
    requires validPageNr(p)
    requires memContainsPage(page, p)
    requires e.Addrspace?
    requires closedRefsPageDbEntry(e)
{
    var base := page_monvaddr(p);
    assert base in page;
    page[base + ADDRSPACE_L1PT()] == page_monvaddr(e.l1ptnr)
    && page[base + ADDRSPACE_L1PT_PHYS()] == page_paddr(e.l1ptnr)
    && page[base + ADDRSPACE_REF()] == e.refcount
    && page[base + ADDRSPACE_STATE()] == pageDbAddrspaceStateVal(e.state)
}

predicate pageDbDispatcherCorresponds(p:PageNr, e:PageDbEntryTyped, page:map<mem, int>)
    requires validPageNr(p)
    requires memContainsPage(page, p)
    requires e.Dispatcher?
    requires closedRefsPageDbEntry(e)
{
    var base := page_monvaddr(p);
    // TODO: concrete representation of dispatcher fields
    true
}

function pageDbEntryTypeVal(e: PageDbEntry): int
    ensures isUInt32(pageDbEntryTypeVal(e))
{
    if e.PageDbEntryFree? then KEV_PAGE_FREE()
    else match e.entry {
        case Addrspace(l1pt, ref, state) => KEV_PAGE_ADDRSPACE()
        case Dispatcher(ep, entered, ctxt) => KEV_PAGE_DISPATCHER()
        case L1PTable(pt) => KEV_PAGE_L1PTABLE()
        case L2PTable(pt) => KEV_PAGE_L2PTABLE()
        case DataPage => KEV_PAGE_DATA()
    }
}

function pageDbAddrspaceStateVal(s: AddrspaceState): int
    ensures isUInt32(pageDbAddrspaceStateVal(s))
{
    match s {
    case InitState => KEV_ADDRSPACE_INIT()
    case FinalState => KEV_ADDRSPACE_FINAL()
    case StoppedState => KEV_ADDRSPACE_STOPPED()
    }
}
