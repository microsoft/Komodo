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
function method PAGEDB_ENTRY_ADDRSPACE():int
    ensures PAGEDB_ENTRY_ADDRSPACE() == 4 
    ensures WordAligned(PAGEDB_ENTRY_ADDRSPACE())
    {4}

//-----------------------------------------------------------------------------
// Addrspace Fields
//-----------------------------------------------------------------------------
// addrspc = start address of address space metadata
// TODO requires that this thing is an addrspce?
function method ADDRSPACE_L1PT():int      { 0  }
function method ADDRSPACE_L1PT_PHYS():int { 4  }
function method ADDRSPACE_REF():int       { 8  }
function method ADDRSPACE_STATE():int
    ensures ADDRSPACE_STATE() == 12       { 12 }
function method ADDRSPACE_SIZE():int      { 16 }

//-----------------------------------------------------------------------------
// Dispatcher Fields
//-----------------------------------------------------------------------------
function method DISPATCHER_ENTERED():int { 0 }
function method DISPATCHER_ENTRYPOINT():int { 4 }
// TODO context
// psr
// 16 regs

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
function method KEV_ADDRSPACE_FINAL():int
    ensures KEV_ADDRSPACE_FINAL() == 1; { 1 }
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
        ==> (pageDbEntryCorresponds(pagedb[p], db[p])
            && pageContentsCorresponds(p, pagedb[p], secpages[p]))
}

predicate pageDbCorrespondsExcluding(s:memstate, pagedb:PageDb, modifiedPage:PageNr)
    requires SaneMem(s)
    requires pageDbClosedRefs(pagedb)
{
    reveal_pageDbClosedRefs();
    forall p {:trigger validPageNr(p)} :: validPageNr(p) && p != modifiedPage
        ==> (pageDbEntryCorresponds(pagedb[p], extractPageDbEntry(s, p))
            && pageContentsCorresponds(p, pagedb[p], extractPage(s, p)))
}

predicate pageDbCorrespondsOnly(s:memstate, pagedb:PageDb, p:PageNr)
    requires SaneMem(s)
    requires pageDbClosedRefs(pagedb)
    requires validPageNr(p)
{
    reveal_pageDbClosedRefs();
    pageDbEntryCorresponds(pagedb[p], extractPageDbEntry(s, p))
    && pageContentsCorresponds(p, pagedb[p], extractPage(s, p))
}

predicate {:opaque} pageDbEntryCorresponds(e:PageDbEntry, entryWords:seq<int>)
    requires |entryWords| == BytesToWords(PAGEDB_ENTRY_SIZE())
    requires closedRefsPageDbEntry(e)
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
    requires closedRefsPageDbEntry(e)
{
    e.PageDbEntryFree? || (e.PageDbEntryTyped? && (
        var et := e.entry;
        (et.Addrspace? && pageDbAddrspaceCorresponds(p, et, page))
        || (et.Dispatcher? && pageDbDispatcherCorresponds(p, et, page))
        || (et.L1PTable? && pageDbL1PTableCorresponds(p, et, page))
        || (et.L2PTable? && pageDbL2PTableCorresponds(p, et, page))
        || et.DataPage?))
}

predicate {:opaque} pageDbAddrspaceCorresponds(p:PageNr, e:PageDbEntryTyped, page:map<mem, int>)
    requires validPageNr(p)
    requires memContainsPage(page, p)
    requires e.Addrspace? && closedRefsPageDbEntryTyped(e)
{
    var base := page_monvaddr(p);
    assert base in page;
    page[base + ADDRSPACE_L1PT()] == page_monvaddr(e.l1ptnr)
    && page[base + ADDRSPACE_L1PT_PHYS()] == page_paddr(e.l1ptnr)
    && page[base + ADDRSPACE_REF()] == e.refcount
    && page[base + ADDRSPACE_STATE()] == pageDbAddrspaceStateVal(e.state)
}

function  to_i(b:bool):int { if(b) then 1 else 0 }
predicate {:opaque} pageDbDispatcherCorresponds(p:PageNr, e:PageDbEntryTyped, page:map<mem, int>)
    requires validPageNr(p)
    requires memContainsPage(page, p)
    requires e.Dispatcher? && closedRefsPageDbEntryTyped(e)
{
    var base := page_monvaddr(p);
    assert base in page;
    page[base + DISPATCHER_ENTERED()] == to_i(e.entered)
    && page[base + DISPATCHER_ENTRYPOINT()] == e.entrypoint
    // TODO: finish concrete representation of dispatcher fields
}

// TODO: refactor; some of this is a trusted spec for ARM's PTE format!
function method ARM_L2PT_BYTES(): int { 0x400 }
function ARM_L1PTE(paddr: int): int
    requires isUInt32(paddr) && (paddr % ARM_L2PT_BYTES() == 0)
    ensures isUInt32(ARM_L1PTE(paddr))
{
    //or32(paddr, 1) // type = 1, pxn = 0, ns = 0, domain = 0
    paddr + 1
}


function ARM_L2PTE_CONST_BITS(): int
{
    0x2 /* type */
        + 0x4 /* B */
        + 0x30 /* AP0, AP1 */
        + 0x140 /* TEX */
        + 0x400 /* S */
        + 0x800 /* NG */
}

function ARM_L2PTE_NX_BITS(): int
{
    0x1 // XN
}

function ARM_L2PTE_RO_BITS(): int
{
    0x200 // AP2
}

function ARM_L2PTE(paddr: int, write: bool, exec: bool): int
    requires isUInt32(paddr) && PageAligned(paddr)
    ensures isUInt32(ARM_L2PTE(paddr, write, exec))
{
    var nxbits := if exec then 0 else ARM_L2PTE_NX_BITS();
    var robits := if write then 0 else ARM_L2PTE_RO_BITS();
    var ptebits := ARM_L2PTE_CONST_BITS() + nxbits + robits;
    //or32(ARM_L2PTE_CONST_BITS(), or32(nxbits, robits))
    paddr + ptebits //or32(paddr, ptebits)
}

function mkL1Pte(e: Maybe<PageNr>, subpage:int): int
    requires e.Just? ==> validPageNr(fromJust(e))
    requires 0 <= subpage < 4
{
    match e
        case Nothing => 0
        case Just(pgNr) =>
            assert ARM_L2PT_BYTES() == 0x400; // grumble
            ARM_L1PTE(page_paddr(pgNr) + subpage * ARM_L2PT_BYTES())
}

function l1pteoffset(base: mem, i: int, j: int): int
{
    base + 4 * (i * 4 + j)
}

predicate {:opaque} pageDbL1PTableCorresponds(p:PageNr, e:PageDbEntryTyped, page:map<mem, int>)
    requires validPageNr(p)
    requires memContainsPage(page, p)
    requires e.L1PTable? && closedRefsL1PTable(e)
{
    var base := page_monvaddr(p);
    forall i, j :: 0 <= i < NR_L1PTES() && 0 <= j < 4
        ==> page[l1pteoffset(base, i, j)] == mkL1Pte(e.l1pt[i], j)
}

function mkL2Pte(pte: L2PTE): int
    requires closedRefsL2PTE(pte)
{
    match pte
        case SecureMapping(pg, w, x) => ARM_L2PTE(page_paddr(pg), w, x)
        case InsecureMapping(ipg, w) => (
            assert KEVLAR_PAGE_SIZE() == 0x1000; // sigh
            var pa := ipg * KEVLAR_PAGE_SIZE();
            assert PageAligned(pa); // double sigh
            ARM_L2PTE(pa, w, false))
        case NoMapping => 0
}

predicate {:opaque} pageDbL2PTableCorresponds(p:PageNr, e:PageDbEntryTyped, page:map<mem, int>)
    requires validPageNr(p)
    requires memContainsPage(page, p)
    requires e.L2PTable? && closedRefsL2PTable(e)
{
    var base := page_monvaddr(p);
    forall i :: 0 <= i < NR_L2PTES() ==>
        var a := base + WordsToBytes(i);
        assert a in page;
        page[a] == mkL2Pte(e.l2pt[i])
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

//-----------------------------------------------------------------------------
// Common lemmas
//-----------------------------------------------------------------------------

lemma ValidPageDbImpliesValidAddrspace(d:PageDb, n:PageNr)
    requires validPageDb(d)
    requires isAddrspace(d, n)
    ensures closedRefsPageDbEntry(d[n]) && validAddrspace(d, n)
{
    reveal_validPageDb();
    assert validPageDbEntryTyped(d, n);
}

lemma PageDbCorrespondsImpliesEntryCorresponds(s:memstate, d:PageDb, n:PageNr)
    requires SaneMem(s)
    requires pageDbClosedRefs(d)
    requires pageDbCorresponds(s, d)
    requires validPageNr(n)
    ensures closedRefsPageDbEntry(d[n])
    ensures pageDbEntryCorresponds(d[n], extractPageDbEntry(s, n))
{
    reveal_pageDbClosedRefs();
}

lemma AllButOnePagePreserving(n:PageNr,s:state,r:state)
    requires validPageNr(n)
    requires SaneState(s) && SaneState(r) && AlwaysInvariant(s,r)
    requires MemPreservingExcept(s, r, page_monvaddr(n), page_monvaddr(n) + KEVLAR_PAGE_SIZE())
    ensures forall p :: validPageNr(p) && p != n ==> extractPage(s.m, p) == extractPage(r.m, p)
{
}
