include "kom_common.s.dfy"
include "Maybe.dfy"
include "Sets.s.dfy"
include "ARMdef.s.dfy"
include "sha/sha_common.s.dfy"
include "sha/sha256.s.dfy"

type PageNr = x | validPageNr(x)
type InsecurePageNr = x | validInsecurePageNr(x)

const NR_L1PTES: int := 256;
const NR_L2PTES: int := 1024;

predicate validPageNr(p: int)
{
    0 <= p < KOM_SECURE_NPAGES
}

predicate validInsecurePageNr(p: int)
{
    0 <= p < KOM_PHYSMEM_LIMIT / PAGESIZE
}

function page_paddr(p: PageNr): addr
    requires validPageNr(p)
    ensures PageAligned(page_paddr(p))
    ensures SecurePhysBase() <= page_paddr(p) < SecurePhysBase() + KOM_SECURE_RESERVE
{
    reveal PageAligned();
    assert PageAligned(PAGESIZE);
    assert PageAligned(SecurePhysBase());
    SecurePhysBase() + p * PAGESIZE
}

function page_monvaddr(p: PageNr): addr
    requires validPageNr(p)
    ensures PageAligned(page_monvaddr(p))
    ensures address_is_secure(page_monvaddr(p))
{
    assert p < KOM_SECURE_NPAGES;
    var pa := page_paddr(p);
    assert pa < SecurePhysBase() + KOM_SECURE_RESERVE;
    reveal PageAligned();
    pa + KOM_DIRECTMAP_VBASE
}

predicate addrInPage(m:addr, p:PageNr)
{
    page_monvaddr(p) <= m < page_monvaddr(p) + PAGESIZE
}

predicate physPageIsInsecureRam(physPage: int)
{
    0 <= physPage * PAGESIZE < MonitorPhysBase()
}

predicate physPageIsSecure(physPage: int)
{
    var paddr := physPage * PAGESIZE;
    SecurePhysBase() <= paddr < SecurePhysBase() + KOM_SECURE_RESERVE
}


datatype PageDbEntryTyped
    = Addrspace(l1ptnr: PageNr, refcount: nat, state: AddrspaceState,
                measurement: seq<word>,
                // XXX: shatrace is untrusted ghost state... shouldn't be here
                shatrace:SHA256Trace)
    | Dispatcher(entrypoint:word, entered:bool, ctxt:DispatcherContext,
                verify_words:seq<word>, verify_measurement:seq<word>)
    | L1PTable(l1pt: seq<Maybe<PageNr>>)
    | L2PTable(l2pt: seq<L2PTE>)
    | DataPage(contents: seq<word>)
    | SparePage // allocated to an addrspace, but not mapped/typed

datatype AddrspaceState = InitState | FinalState | StoppedState

datatype DispatcherContext
    = DispatcherContext(regs:map<ARMReg,word>, pc:word, cpsr:word)

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
    forall n {:trigger validPageNr(n)} ::
        validPageNr(n) <==> n in d && wellFormedPageDbEntry(d[n])
}

predicate wellFormedPageDbEntry(e: PageDbEntry)
{
    e.PageDbEntryTyped? ==> wellFormedPageDbEntryTyped(e.entry)
}

predicate wellFormedPageDbEntryTyped(e: PageDbEntryTyped)
{
    (e.L1PTable? ==> |e.l1pt| == NR_L1PTES)
    && (e.L2PTable? ==> |e.l2pt| == NR_L2PTES)
    && (e.Dispatcher? ==> wellformedDispatcherContext(e.ctxt) 
                      && |e.verify_words| == 8 
                      && |e.verify_measurement| == 8)
    && (e.DataPage? ==> |e.contents| == PAGESIZE / WORDSIZE)
    && (e.Addrspace? ==>
        |e.measurement| % SHA_BLOCKSIZE == 0
        && |e.shatrace.H| > 0
        && WordsToBytes(|e.measurement|) < MaxBytesForSHA())
}

predicate {:opaque} validPageDb(d: PageDb)
    ensures validPageDb(d) ==> wellFormedPageDb(d)
{
    wellFormedPageDb(d) && pageDbEntriesValid(d) && pageDbEntriesValidRefs(d)
}

predicate wellformedDispatcherContext(dc:DispatcherContext)
{
    forall r :: r in USER_REGS() <==> r in dc.regs
}

predicate validDispatcherContext(dc:DispatcherContext)
{
    wellformedDispatcherContext(dc)
    && decode_mode'(psr_mask_mode(dc.cpsr)) == Just(User)
    && psr_mask_fiq(dc.cpsr) == 0
    && psr_mask_irq(dc.cpsr) == 0
}

predicate pageDbEntriesValid(d:PageDb)
    requires wellFormedPageDb(d)
{
    forall n | validPageNr(n) :: validPageDbEntry(d, n)
}

predicate pageDbEntriesValidRefs(d: PageDb)
    requires wellFormedPageDb(d)
{
    forall n | validPageNr(n) && d[n].PageDbEntryTyped? :: pageDbEntryValidRefs(d, n)
}

// Free pages and non-addrspace entries should have a refcount of 0
predicate pageDbEntryValidRefs(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
{
    var e := d[n];
    (e.PageDbEntryTyped? && e.entry.Addrspace?) ||
        |addrspaceRefs(d, n)| == 0
}

predicate validPageDbEntry(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
{
    d[n].PageDbEntryTyped? ==> validPageDbEntryTyped(d, n)
}

predicate validPageDbEntryTyped(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
    requires d[n].PageDbEntryTyped?
{
    var asPg := d[n].addrspace;
    var stoppedAS := hasStoppedAddrspace(d, n);
    isAddrspace(d, asPg) && match d[n].entry
        case Addrspace(_, _, _, _, _) => validAddrspace(d, n)
        case L1PTable(l1pt) => stoppedAS || validL1PTable(d, asPg, l1pt)
        case L2PTable(l2pt) => stoppedAS || (
            referencedL2PTable(d, asPg, n) && validL2PTable(d, asPg, l2pt))
        case Dispatcher(_, entered, ctxt, _, _) =>
            (entered ==> validDispatcherContext(ctxt))
        case DataPage(_) => (stoppedAS || |dataPageRefs(d, asPg, n)| <= 1)
        case SparePage => true
}

predicate isAddrspace(d: PageDb, n: int)
{
    wellFormedPageDb(d)
        && validPageNr(n)
        && d[n].PageDbEntryTyped?
        && d[n].entry.Addrspace?
}

predicate stoppedAddrspace(e: PageDbEntry)
{
    e.PageDbEntryTyped? && e.entry.Addrspace? && e.entry.state.StoppedState?
}

// The addrspace of the thing pointed to by n is stopped
predicate hasStoppedAddrspace(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
    requires d[n].PageDbEntryTyped?
{
    stoppedAddrspace(d[d[n].addrspace])
}

predicate validAddrspace(d: PageDb, n: PageNr)
    requires isAddrspace(d, n)
{
    var addrspace := d[n].entry;
    n == d[n].addrspace
        // && addrspaceL1Unique(d, n)
        && addrspace.refcount == |addrspaceRefs(d, n)|
        && (addrspace.state.StoppedState? ||
            (isL1PTable(d, addrspace.l1ptnr) && d[addrspace.l1ptnr].addrspace == n))
        // XXX: sha trace invariants don't need to be trusted... move out of spec
        && IsCompleteSHA256Trace(addrspace.shatrace)
        && SHA256TraceIsCorrect(addrspace.shatrace)
        && (addrspace.state.InitState? ==>
            |addrspace.shatrace.M| <= addrspace.refcount * (1 + PAGESIZE / (WORDSIZE * SHA_BLOCKSIZE)))
        && ConcatenateSeqs(addrspace.shatrace.M) == addrspace.measurement
}

predicate isL1PTable(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
{
    d[n].PageDbEntryTyped? && d[n].entry.L1PTable?
}

/*
predicate addrspaceL1Unique(d: PageDb, n: PageNr)
    requires isAddrspace(d, n)
{
    var a := d[n].entry;
    forall p | validPageNr(p) && d[p].PageDbEntryTyped? && d[p].addrspace == n
        :: d[p].entry.L1PTable? ==> p == a.l1ptnr
}
*/

function {:opaque} validPageNrs(): set<PageNr>
    ensures forall n :: n in validPageNrs() <==> validPageNr(n)
{
    SetOfNumbersInRightExclusiveRange(0, KOM_SECURE_NPAGES)
}

// returns the set of references to an addrspace page with the given index
function addrspaceRefs(d: PageDb, addrspacePageNr: PageNr): set<PageNr>
    requires wellFormedPageDb(d)
{
    (set n | n in validPageNrs()
        && d[n].PageDbEntryTyped?
        && n != addrspacePageNr
        && d[n].addrspace == addrspacePageNr)
}

predicate validL1PTable(d: PageDb, asPg: PageNr, l1pt: seq<Maybe<PageNr>>)
    requires wellFormedPageDb(d)
{
    // each non-zero entry is a valid L2PT belonging to this address space
    forall pte :: pte in l1pt && pte.Just? ==> (
        d[pte.v].PageDbEntryTyped?
        && d[pte.v].addrspace == asPg
        && validL1PTE(d, pte.v))
    // no L2PT is referenced twice
    && forall i, j :: 0 <= i < |l1pt| && 0 <= j < |l1pt| && l1pt[i].Just? && i != j
        ==> l1pt[i] != l1pt[j]
}

predicate validL1PTE(d: PageDb, pte: PageNr)
    requires wellFormedPageDb(d)
{
    d[pte].PageDbEntryTyped? && d[pte].entry.L2PTable?
}

predicate referencedL2PTable(d: PageDb, asPg: PageNr, l2ptnr: PageNr)
    requires wellFormedPageDb(d)
{
    isAddrspace(d, asPg) &&
    var l1ptnr := d[asPg].entry.l1ptnr;
    d[l1ptnr].PageDbEntryTyped? && d[l1ptnr].entry.L1PTable? &&
    var l1pt := d[l1ptnr].entry.l1pt;
    exists i | 0 <= i < NR_L1PTES :: l1pt[i] == Just(l2ptnr)
}

predicate validL2PTable(d: PageDb, asPg: PageNr, l2pt: seq<L2PTE>)
    requires wellFormedPageDb(d)
{
    // Not needed when addrspace is stopped: valid PTEs
    forall pte | pte in l2pt :: validL2PTE(d, asPg, pte)
}

predicate validL2PTE(d: PageDb, addrspace: PageNr, pte: L2PTE)
    requires wellFormedPageDb(d)
{
    match pte
        // each secure entry is a valid data page belonging to this address space
        case SecureMapping(pg, w, x)
            => d[pg].PageDbEntryTyped? && d[pg].addrspace == addrspace
                && d[pg].PageDbEntryTyped? && d[pg].entry.DataPage?
        // each insecure entry points to non-secure RAM
        case InsecureMapping(pg, w) => physPageIsInsecureRam(pg)
        case NoMapping => true
}

// returns the set of secure mappings of a given data page
function dataPageRefs(d: PageDb, asPg:PageNr, p: PageNr): set<(int, int)>
    requires wellFormedPageDb(d) && isAddrspace(d, asPg)
{
    var l1ptnr := d[asPg].entry.l1ptnr;
    (set i1, i2 {:trigger d[d[l1ptnr].entry.l1pt[i1].v].entry.l2pt[i2]} |
        d[l1ptnr].PageDbEntryTyped? && d[l1ptnr].entry.L1PTable?
        && 0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
        && var l1e := d[l1ptnr].entry.l1pt[i1]; l1e.Just?
        && d[l1e.v].PageDbEntryTyped? && d[l1e.v].entry.L2PTable?
        && var l2e := d[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
        && l2e.page == p :: (i1, i2))
}

//-----------------------------------------------------------------------------
// Utilities 
//-----------------------------------------------------------------------------
predicate pageIsFree(d:PageDb, pg:PageNr)
{
    wellFormedPageDb(d) && d[pg].PageDbEntryFree?
}

predicate validL1PTPage(d:PageDb, p:PageNr)
{
    validPageDb(d) && d[p].PageDbEntryTyped? && d[p].entry.L1PTable?
}

predicate validL2PTPage(d:PageDb, p:PageNr)
{
    validPageDb(d) && d[p].PageDbEntryTyped? && d[p].entry.L2PTable?
}

predicate validDispatcherPage(d:PageDb, p:PageNr)
{
    validPageDb(d) && d[p].PageDbEntryTyped? && d[p].entry.Dispatcher?
}

// TODO: delete this redundant alias
predicate validAddrspacePage(d: PageDb, a: int)
{
    isAddrspace(d, a)
}

predicate nonStoppedL1(d:PageDb, l1:PageNr)
{
    validL1PTPage(d, l1) && !hasStoppedAddrspace(d, l1)
}

predicate nonStoppedDispatcher(d:PageDb, p:PageNr)
{
    validDispatcherPage(d,p) && !hasStoppedAddrspace(d,p)
}

predicate finalDispatcher(d:PageDb, p:PageNr)
{
    validDispatcherPage(d,p) && (var a := d[p].addrspace;
        isAddrspace(d, a) && d[a].entry.state == FinalState)
}

function l1pOfDispatcher(d:PageDb, p:PageNr) : PageNr
    requires nonStoppedDispatcher(d, p)
    ensures nonStoppedL1(d, l1pOfDispatcher(d,p))
{
    reveal validPageDb();
    var a := d[p].addrspace;
    d[a].entry.l1ptnr
}

//=============================================================================
// Mapping
//=============================================================================
datatype Mapping = Mapping(l1index: word, l2index: word, perm: Perm)
datatype Perm = Perm(r: bool, w: bool, x: bool)

predicate validMapping(m:Mapping, d:PageDb, a:PageNr)
{
    && 0 <= m.l1index < NR_L1PTES
    && 0 <= m.l2index < NR_L2PTES
    && isAddrspace(d, a) && var asp := d[a].entry; asp.state != StoppedState
    && isL1PTable(d, asp.l1ptnr)
    && d[asp.l1ptnr].entry.l1pt[m.l1index].Just?
}

function l1indexFromMapping(arg:word) : word
    { RightShift(arg,20) }

function l2indexFromMapping(arg:word) : word
    { BitwiseAnd(RightShift(arg,12),0xff) }

function permFromMapping(arg:word) : Perm
{
    Perm(BitwiseAnd(arg,KOM_MAPPING_R) != 0,
        BitwiseAnd(arg,KOM_MAPPING_W) != 0,
        BitwiseAnd(arg,KOM_MAPPING_X) != 0)
}

function {:opaque} wordToMapping(arg:word) : Mapping
{
    Mapping(l1indexFromMapping(arg),l2indexFromMapping(arg),
        permFromMapping(arg))
}

//=============================================================================
// Representation in physical memory
//=============================================================================

predicate memContainsPage(page: memmap, p:PageNr)
{
    forall m:addr :: addrInPage(m,p) ==> m in page
}

function extractPage(s:memstate, p:PageNr): memmap
    requires SaneConstants() && ValidMemState(s)
    ensures memContainsPage(extractPage(s,p), p)
{
    reveal ValidMemState();
    // XXX: expanded addrInPage() to help Dafny see a bounded set
    var res := (map m:addr {:trigger addrInPage(m, p)} {:trigger MemContents(s, m)}
        | page_monvaddr(p) <= m < page_monvaddr(p) + PAGESIZE
        :: MemContents(s, m));
    res
}

predicate dataPagesCorrespond(s:memstate, pagedb:PageDb)
    requires SaneConstants() && ValidMemState(s)
    requires wellFormedPageDb(pagedb)
{
    // XXX: unpack the page contents here to help dafny see
    // that we have no other dependencies on the state
    var secpages := (map p | 0 <= p < KOM_SECURE_NPAGES :: extractPage(s,p));
    forall p {:trigger validPageNr(p)} | validPageNr(p)
        && pagedb[p].PageDbEntryTyped? && pagedb[p].entry.DataPage?
        :: pageDbDataCorresponds(p, pagedb[p].entry, secpages[p])
}

predicate {:opaque} pageDbDataCorresponds(p: PageNr, e: PageDbEntryTyped, page:memmap)
    requires memContainsPage(page, p)
    requires e.DataPage?
    requires wellFormedPageDbEntryTyped(e)
{
    var base := page_monvaddr(p);
    forall i | 0 <= i < PAGESIZE / WORDSIZE ::
        (assert base + i*WORDSIZE in page;
        e.contents[i] == page[base + i*WORDSIZE])
}
