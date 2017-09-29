include "pagedb.s.dfy"
include "kom_common.i.dfy"
include "sha/Seqs.s.dfy"

//-----------------------------------------------------------------------------
// Data Structures
//-----------------------------------------------------------------------------
// computes byte offset of a specific pagedb entry
function method G_PAGEDB_ENTRY(pageno:PageNr): addr
{
    assert WordAligned(PAGEDB_ENTRY_SIZE);
    pageno * PAGEDB_ENTRY_SIZE
}

// entry = start offset of pagedb entry
const PAGEDB_ENTRY_TYPE:addr    := 0;
const PAGEDB_ENTRY_ADDRSPACE:addr:= WORDSIZE;

//-----------------------------------------------------------------------------
// Addrspace Fields
//-----------------------------------------------------------------------------
const ADDRSPACE_L1PT:addr              := 0;
const ADDRSPACE_L1PT_PHYS:addr         := 1*WORDSIZE;
const ADDRSPACE_REF:addr               := 2*WORDSIZE;
const ADDRSPACE_STATE:addr             := 3*WORDSIZE;
const ADDRSPACE_HASH:addr              := 4*WORDSIZE;   // Requires 8 words, hence the bump for block count
const ADDRSPACE_HASHED_BLOCK_COUNT:addr:= 12*WORDSIZE;
const ADDRSPACE_SIZE:addr              := 13*WORDSIZE;

//-----------------------------------------------------------------------------
// Dispatcher Fields
//-----------------------------------------------------------------------------
const DISPATCHER_ENTERED:addr   := 0;
const DISPATCHER_ENTRYPOINT:addr:= 1*WORDSIZE;

const DISP_CTXT_R0:addr         := 2*WORDSIZE;
const DISP_CTXT_R1:addr         := 3*WORDSIZE;
const DISP_CTXT_R2:addr         := 4*WORDSIZE;
const DISP_CTXT_R3:addr         := 5*WORDSIZE;
const DISP_CTXT_R4:addr         := 6*WORDSIZE;
const DISP_CTXT_R5:addr         := 7*WORDSIZE;
const DISP_CTXT_R6:addr         := 8*WORDSIZE;
const DISP_CTXT_R7:addr         := 9*WORDSIZE;
const DISP_CTXT_R8:addr         := 10*WORDSIZE;
const DISP_CTXT_R9:addr         := 11*WORDSIZE;
const DISP_CTXT_R10:addr        := 12*WORDSIZE;
const DISP_CTXT_R11:addr        := 13*WORDSIZE;
const DISP_CTXT_R12:addr        := 14*WORDSIZE;
const DISP_CTXT_LR:addr         := 15*WORDSIZE;
const DISP_CTXT_SP:addr         := 16*WORDSIZE;
const DISP_CTXT_PC:addr         := 17*WORDSIZE;
const DISP_CTXT_PSR:addr        := 18*WORDSIZE;
const DISP_CTXT_USER_WORDS:addr := 19*WORDSIZE;     // Requires 8 words, hence bump for next entry
const DISP_CTXT_VERIFY_MEASUREMENT:addr := 27*WORDSIZE;     // Requires 8 words, hence bump for block count
const DISP_SIZE:addr            := 35*WORDSIZE;

//-----------------------------------------------------------------------------
// Page Types
//-----------------------------------------------------------------------------
const KOM_PAGE_FREE:int         := 0;
const KOM_PAGE_ADDRSPACE:int    := 1;
const KOM_PAGE_DISPATCHER:int   := 2;
const KOM_PAGE_L1PTABLE:int     := 3;
const KOM_PAGE_L2PTABLE:int     := 4;
const KOM_PAGE_DATA:int         := 5;
const KOM_PAGE_SPARE:int        := 6;

//-----------------------------------------------------------------------------
// Address Space States
//-----------------------------------------------------------------------------
const KOM_ADDRSPACE_INIT:int    := 0;
const KOM_ADDRSPACE_FINAL:int   := 1;
const KOM_ADDRSPACE_STOPPED:int := 2;

//-----------------------------------------------------------------------------
//
//-----------------------------------------------------------------------------

function extractPageDbEntry(s:memstate, p:PageNr): seq<word>
    requires SaneMem(s)
    ensures |extractPageDbEntry(s,p)| == BytesToWords(PAGEDB_ENTRY_SIZE)
    // ensures forall o | WordAligned(o) && 0 <= o < PAGEDB_ENTRY_SIZE ::
    //    GlobalWord(s, PageDb(), G_PAGEDB_ENTRY(p) + o)
    //        == extractPageDbEntry(s,p)[BytesToWords(o)]
{
    var fulldb := GlobalFullContents(s, PageDb());
    assert |fulldb| == BytesToWords(G_PAGEDB_SIZE);
    var entrylen := BytesToWords(PAGEDB_ENTRY_SIZE);
    //fulldb[p*entrylen..p*entrylen+entrylen]
    fulldb[p*BytesToWords(PAGEDB_ENTRY_SIZE)..(p+1)*BytesToWords(PAGEDB_ENTRY_SIZE)]
}

predicate pageDbCorresponds(s:memstate, pagedb:PageDb)
    requires SaneMem(s)
    requires wellFormedPageDb(pagedb)
{
    // XXX: unpack the entry and page contents here to help dafny see
    // that we have no other dependencies on the state
    var db := (map p | 0 <= p < KOM_SECURE_NPAGES :: extractPageDbEntry(s,p));
    var secpages := (map p | 0 <= p < KOM_SECURE_NPAGES :: extractPage(s,p));
    forall p {:trigger validPageNr(p)} | validPageNr(p) :: 
        pageDbEntryCorresponds(pagedb[p], db[p])
            && pageContentsCorresponds(p, pagedb[p], secpages[p])
}

predicate pageDbCorrespondsExcluding(s:memstate, pagedb:PageDb, modifiedPage:PageNr)
    requires SaneMem(s)
    requires wellFormedPageDb(pagedb)
{
    forall p {:trigger validPageNr(p)} :: validPageNr(p) && p != modifiedPage
        ==> (pageDbEntryCorresponds(pagedb[p], extractPageDbEntry(s, p))
            && pageContentsCorresponds(p, pagedb[p], extractPage(s, p)))
}

predicate pageDbCorrespondsExcludingSet(s:memstate, pagedb:PageDb, 
    trashed:set<PageNr>)
    requires SaneMem(s)
    requires wellFormedPageDb(pagedb)
{
    forall p {:trigger validPageNr(p)} | validPageNr(p) && p !in trashed  ::
        (pageDbEntryCorresponds(pagedb[p], extractPageDbEntry(s, p))
            && pageContentsCorresponds(p, pagedb[p], extractPage(s, p)))
}

predicate pageDbCorrespondsOnly(s:memstate, pagedb:PageDb, p:PageNr)
    requires SaneMem(s)
    requires wellFormedPageDb(pagedb)
{
    pageDbEntryCorresponds(pagedb[p], extractPageDbEntry(s, p))
    && pageContentsCorresponds(p, pagedb[p], extractPage(s, p))
}

predicate {:opaque} pageDbEntryCorresponds(e:PageDbEntry, entryWords:seq<word>)
    requires |entryWords| == BytesToWords(PAGEDB_ENTRY_SIZE)
    requires wellFormedPageDbEntry(e)
{
    pageDbEntryTypeVal(e) == entryWords[BytesToWords(PAGEDB_ENTRY_TYPE)]
    && match e {
        case PageDbEntryFree => true
        case PageDbEntryTyped(addrspace, entry) =>
            entryWords[BytesToWords(PAGEDB_ENTRY_ADDRSPACE)]
                == page_monvaddr(addrspace)
    }
}

predicate {:opaque} pageContentsCorresponds(p:PageNr, e:PageDbEntry, page:memmap)
    requires memContainsPage(page, p)
    requires wellFormedPageDbEntry(e)
{
    e.PageDbEntryFree? || (e.PageDbEntryTyped? && (
        var et := e.entry;
        assert wellFormedPageDbEntryTyped(et);
        (et.Addrspace? && pageDbAddrspaceCorresponds(p, et, page))
        || (et.Dispatcher? && pageDbDispatcherCorresponds(p, et, page))
        || (et.L1PTable? && pageDbL1PTableCorresponds(p, et, page))
        || (et.L2PTable? && pageDbL2PTableCorresponds(p, et, page))
        || (et.DataPage? && pageDbDataCorresponds(p, et, page))
        || et.SparePage?))
}

predicate {:opaque} pageDbAddrspaceCorresponds(p:PageNr, e:PageDbEntryTyped, page:memmap)
    requires memContainsPage(page, p)
    requires wellFormedPageDbEntryTyped(e) && e.Addrspace?
{
    var base := page_monvaddr(p);
    assert base in page;
    var hashbase := WordAlignedAdd(base, ADDRSPACE_HASH);
    var addr_space_hash := [page[WordOffset(hashbase, 0)],
                            page[WordOffset(hashbase, 1)],
                            page[WordOffset(hashbase, 2)],
                            page[WordOffset(hashbase, 3)],
                            page[WordOffset(hashbase, 4)],
                            page[WordOffset(hashbase, 5)],
                            page[WordOffset(hashbase, 6)],
                            page[WordOffset(hashbase, 7)]];
    page[WordAlignedAdd(base, ADDRSPACE_L1PT)] == page_monvaddr(e.l1ptnr)
    && page[WordAlignedAdd(base, ADDRSPACE_L1PT_PHYS)] == page_paddr(e.l1ptnr)
    && page[WordAlignedAdd(base, ADDRSPACE_REF)] == e.refcount
    && page[WordAlignedAdd(base, ADDRSPACE_STATE)] == pageDbAddrspaceStateVal(e.state)
    && page[WordAlignedAdd(base, ADDRSPACE_HASHED_BLOCK_COUNT)] == |e.shatrace.M|
    && (e.state.InitState? ==> addr_space_hash == last(e.shatrace.H))
    && (e.state.FinalState? ==> addr_space_hash == SHA256(WordSeqToBytes(e.measurement)))
}

function  to_i(b:bool):int { if(b) then 1 else 0 }

predicate {:opaque} pageDbDispatcherContextCorresponds(p:PageNr,
                                          ctxt:DispatcherContext, page:memmap)
    requires memContainsPage(page, p)
    requires wellformedDispatcherContext(ctxt)
{
    var base := page_monvaddr(p);
    assert base in page;
      page[WordAlignedAdd(base, DISP_CTXT_PC)] == ctxt.pc
    && page[WordAlignedAdd(base, DISP_CTXT_PSR)] == ctxt.cpsr
    && page[WordAlignedAdd(base, DISP_CTXT_LR)]  == ctxt.regs[LR(User)]
    && page[WordAlignedAdd(base, DISP_CTXT_SP)]  == ctxt.regs[SP(User)]
    && page[WordAlignedAdd(base, DISP_CTXT_R0)]  == ctxt.regs[R0]
    && page[WordAlignedAdd(base, DISP_CTXT_R1)]  == ctxt.regs[R1]
    && page[WordAlignedAdd(base, DISP_CTXT_R2)]  == ctxt.regs[R2]
    && page[WordAlignedAdd(base, DISP_CTXT_R3)]  == ctxt.regs[R3]
    && page[WordAlignedAdd(base, DISP_CTXT_R4)]  == ctxt.regs[R4]
    && page[WordAlignedAdd(base, DISP_CTXT_R5)]  == ctxt.regs[R5]
    && page[WordAlignedAdd(base, DISP_CTXT_R6)]  == ctxt.regs[R6]
    && page[WordAlignedAdd(base, DISP_CTXT_R7)]  == ctxt.regs[R7]
    && page[WordAlignedAdd(base, DISP_CTXT_R8)]  == ctxt.regs[R8]
    && page[WordAlignedAdd(base, DISP_CTXT_R9)]  == ctxt.regs[R9]
    && page[WordAlignedAdd(base, DISP_CTXT_R10)] == ctxt.regs[R10]
    && page[WordAlignedAdd(base, DISP_CTXT_R11)] == ctxt.regs[R11]
    && page[WordAlignedAdd(base, DISP_CTXT_R12)] == ctxt.regs[R12]
}

predicate {:opaque} pageDbDispatcherVerifyStateCorresponds(p:PageNr,
                                        e:PageDbEntryTyped, page:memmap)
    requires memContainsPage(page, p)
    requires wellFormedPageDbEntryTyped(e) && e.Dispatcher?
{
    var base := page_monvaddr(p);
    assert base in page;
    var user_words := WordAlignedAdd(base, DISP_CTXT_USER_WORDS);
    var verify_measurement := WordAlignedAdd(base, DISP_CTXT_VERIFY_MEASUREMENT);
      page[WordOffset(user_words, 0)] == e.verify_words[0]
    && page[WordOffset(user_words, 1)] == e.verify_words[1]
    && page[WordOffset(user_words, 2)] == e.verify_words[2]
    && page[WordOffset(user_words, 3)] == e.verify_words[3]
    && page[WordOffset(user_words, 4)] == e.verify_words[4]
    && page[WordOffset(user_words, 5)] == e.verify_words[5]
    && page[WordOffset(user_words, 6)] == e.verify_words[6]
    && page[WordOffset(user_words, 7)] == e.verify_words[7]
    && page[WordOffset(verify_measurement, 0)] == e.verify_measurement[0]
    && page[WordOffset(verify_measurement, 1)] == e.verify_measurement[1]
    && page[WordOffset(verify_measurement, 2)] == e.verify_measurement[2]
    && page[WordOffset(verify_measurement, 3)] == e.verify_measurement[3]
    && page[WordOffset(verify_measurement, 4)] == e.verify_measurement[4]
    && page[WordOffset(verify_measurement, 5)] == e.verify_measurement[5]
    && page[WordOffset(verify_measurement, 6)] == e.verify_measurement[6]
    && page[WordOffset(verify_measurement, 7)] == e.verify_measurement[7]
}

predicate {:opaque} pageDbDispatcherCorresponds(p:PageNr, e:PageDbEntryTyped, page:memmap)
    requires memContainsPage(page, p)
    requires wellFormedPageDbEntryTyped(e) && e.Dispatcher?
{
    var base := page_monvaddr(p);
    assert base in page;
    page[WordAlignedAdd(base, DISPATCHER_ENTERED)] == to_i(e.entered)
    && page[WordAlignedAdd(base, DISPATCHER_ENTRYPOINT)] == e.entrypoint
    && (e.entered ==> pageDbDispatcherContextCorresponds(p, e.ctxt, page))
    && pageDbDispatcherVerifyStateCorresponds(p, e, page)
}

function method L1PTE_CONST_BITS(): bv32
    { ARM_L1PTE_CONST_BITS | 0x1 } // type = 1

function method L1PTE_CONST_WORD(): word
    { L1PTE_CONST_BITS() as word }

function ARM_L1PTE(paddr: word): word
    //requires paddr % ARM_L2PTABLE_BYTES == 0
    //ensures ValidAbsL1PTEWord(ARM_L1PTE(paddr))
{
    BitwiseOr(paddr, L1PTE_CONST_WORD())
}

function ARM_L2PTE(paddr: word, write: bool, exec: bool): word
    requires PageAligned(paddr)
    //ensures ValidAbsL2PTEWord(ARM_L2PTE(paddr, write, exec))
{
    var nxbits:bv32 := if exec then 0 else ARM_L2PTE_NX_BIT;
    var robits:bv32 := if write then 0 else ARM_L2PTE_RO_BIT;
    BitsAsWord(BitOr(WordAsBits(paddr), BitOr(
        BitOr(ARM_L2PTE_CONST_BITS | 0x2, nxbits), robits)))
}

function mkL1Pte(e: Maybe<PageNr>, subpage:int): int
    requires 0 <= subpage < 4
    //ensures ValidAbsL1PTEWord(mkL1Pte(e, subpage))
{
    match e
        case Nothing => 0
        case Just(pgNr) =>
            assert ARM_L2PTABLE_BYTES == 0x400; // grumble
            ARM_L1PTE(page_paddr(pgNr) + subpage * ARM_L2PTABLE_BYTES)
}

function l1pteoffset(base: addr, i: int, j: int): addr
    requires base < 0xfffff000
    requires 0 <= i < NR_L1PTES && 0 <= j < 4
{
    base + 4 * (i * 4 + j)
}

predicate {:opaque} pageDbL1PTableCorresponds(p:PageNr, e:PageDbEntryTyped,
                                              page:memmap)
    requires memContainsPage(page, p)
    requires e.L1PTable? && wellFormedPageDbEntryTyped(e)
{
    var base := page_monvaddr(p);
    forall i, j :: 0 <= i < NR_L1PTES && 0 <= j < 4
        ==> page[l1pteoffset(base, i, j)] == mkL1Pte(e.l1pt[i], j)
}

function mkL2Pte(pte: L2PTE): word
    //ensures ValidAbsL2PTEWord(mkL2Pte(pte))
{
    match pte
        case SecureMapping(pg, w, x) => ARM_L2PTE(page_paddr(pg), w, x)
        case InsecureMapping(ipg, w) => (
            assert validInsecurePageNr(ipg);
            assert PAGESIZE == 0x1000; // sigh
            var pa := ipg * PAGESIZE;
            assert PageAligned(pa) by { reveal_PageAligned(); }
            ARM_L2PTE(pa, w, false))
        case NoMapping => 0
}

predicate {:opaque} pageDbL2PTableCorresponds(p:PageNr, e:PageDbEntryTyped,
                                              page:memmap)
    requires memContainsPage(page, p)
    requires e.L2PTable? && wellFormedPageDbEntryTyped(e)
{
    var base := page_monvaddr(p);
    forall i :: 0 <= i < NR_L2PTES ==>
        var a := base + WordsToBytes(i);
        assert a in page;
        page[a] == mkL2Pte(e.l2pt[i])
}

function pageDbEntryTypeVal(e: PageDbEntry): word
{
    if e.PageDbEntryFree? then KOM_PAGE_FREE
    else match e.entry {
        case Addrspace(l1pt, ref, state, measurement, shatrace) => KOM_PAGE_ADDRSPACE
        case Dispatcher(ep, entered, ctxt, verify_words, verify_measurement) => KOM_PAGE_DISPATCHER
        case L1PTable(pt) => KOM_PAGE_L1PTABLE
        case L2PTable(pt) => KOM_PAGE_L2PTABLE
        case DataPage(cont) => KOM_PAGE_DATA
        case SparePage() => KOM_PAGE_SPARE
    }
}

function pageDbAddrspaceStateVal(s: AddrspaceState): word
{
    match s {
    case InitState => KOM_ADDRSPACE_INIT
    case FinalState => KOM_ADDRSPACE_FINAL
    case StoppedState => KOM_ADDRSPACE_STOPPED
    }
}

//-----------------------------------------------------------------------------
// Common lemmas
//-----------------------------------------------------------------------------

lemma globalUnmodifiedImpliesCorrespondingPreserved(d:PageDb,m:memstate,m':memstate)
    requires SaneMem(m) && SaneMem(m') && validPageDb(d)
    requires (reveal ValidMemState();
        m.globals[PageDb()] == m'.globals[PageDb()] &&
        m.addresses == m'.addresses)
    requires pageDbCorresponds(m,  d)
    ensures  pageDbCorresponds(m', d)
{
    reveal PageDb();
    reveal ValidMemState();
    reveal pageDbEntryCorresponds();
    reveal pageContentsCorresponds();
   
    forall ( p | validPageNr(p) )
        ensures pageDbEntryCorresponds(d[p], extractPageDbEntry(m',p));
        ensures pageContentsCorresponds(p, d[p], extractPage(m', p));
    {
        assert extractPageDbEntry(m, p) == extractPageDbEntry(m', p);
        PageDbCorrespondsImpliesEntryCorresponds(m, d, p);
        assert pageDbEntryCorresponds(d[p], extractPageDbEntry(m, p));
        
        assert extractPage(m, p) == extractPage(m', p);
        assert pageContentsCorresponds(p, d[p], extractPage(m, p));
    }

}

lemma ValidPageDbImpliesValidAddrspace(d:PageDb, n:PageNr)
    requires validPageDb(d)
    requires isAddrspace(d, n)
    ensures validAddrspace(d, n)
{
    reveal validPageDb();
    assert validPageDbEntryTyped(d, n);
}

lemma PageDbCorrespondsImpliesEntryCorresponds(s:memstate, d:PageDb, n:PageNr)
    requires SaneMem(s)
    requires wellFormedPageDb(d)
    requires pageDbCorresponds(s, d)
    ensures pageDbEntryCorresponds(d[n], extractPageDbEntry(s, n))
{
}

lemma AllButOnePagePreserving(n:PageNr,s:state,r:state)
    requires SaneState(s) && SaneState(r)
    requires MemPreservingExcept(s, r, page_monvaddr(n),
                                 page_monvaddr(n) + PAGESIZE)
    ensures forall p :: validPageNr(p) && p != n
        ==> extractPage(s.m, p) == extractPage(r.m, p)
{
    forall (p, a:addr | validPageNr(p) && p != n && addrInPage(a, p))
        ensures MemContents(s.m, a) == MemContents(r.m, a)
        {}
}


lemma extractPageDbToAbstract(s:memstate, p:PageNr)
    requires SaneMem(s)
    ensures forall o | WordAligned(o) && 0 <= o < PAGEDB_ENTRY_SIZE ::
        GlobalWord(s, PageDb(), WordAlignedAdd(G_PAGEDB_ENTRY(p), o))
            == extractPageDbEntry(s,p)[BytesToWords(o)]
{
}

lemma extractPageDbToAbstractOne(s:memstate, p:PageNr, o:int)
    requires SaneMem(s)
    requires WordAligned(o) && 0 <= o < PAGEDB_ENTRY_SIZE
    ensures GlobalWord(s, PageDb(), WordAlignedAdd(G_PAGEDB_ENTRY(p), o))
        == extractPageDbEntry(s,p)[BytesToWords(o)]
{}

/*
lemma lemma_validPageDbEntry_equivalence(d:PageDb, d':PageDb, n:PageNr)
    requires wellFormedPageDb(d) && wellFormedPageDb(d');
    requires n in d && n in d';
    requires d[n] == d'[n];
    requires validPageDbEntry(d, n);
    ensures  validPageDbEntry(d', n);
{
    var e := d[n];
    if e.PageDbEntryFree? {
        assert validPageDbEntry(d', n);
    } else if (e.PageDbEntryTyped? && validPageDbEntryTyped(d, n)) {


        assert wellFormedPageDbEntry(d[n]) && isAddrspace(d, d[n].addrspace);
        assert d[d[n].addrspace].entry.Addrspace?;
        assert d'[n].entry == d[n].entry;


        assert wellFormedPageDb(d')
        && validPageNr(d'[n].addrspace)
        && d'[d'[n].addrspace].PageDbEntryTyped?
        && d'[d'[n].addrspace].entry.Addrspace?;

        assert wellFormedPageDbEntry(d'[n]) && isAddrspace(d', d'[n].addrspace);

        var entry := d[n].entry;
        assert (entry.Addrspace? && validAddrspace(d, n))
       || (entry.L1PTable? && validL1PTable(d, n))
       || (entry.L2PTable? && validL2PTable(d, n))
       || (entry.Dispatcher? && (entry.entered ==>
            validDispatcherContext(entry.ctxt)))
       // AFAIK the only requirements we need to specify about data pages are 
       // covered by wellFormedPageDbTyped
       || (entry.DataPage?);
        var entry' := d'[n].entry;
        assert (entry'.Addrspace? && validAddrspace(d', n))
       || (entry'.L1PTable? && validL1PTable(d', n))
       || (entry'.L2PTable? && validL2PTable(d', n))
       || (entry'.Dispatcher? && (entry'.entered ==>
            validDispatcherContext(entry'.ctxt)))
       // AFAIK the only requirements we need to specify about data pages are 
       // covered by wellFormedPageDbTyped
       || (entry'.DataPage?);

        assert validPageDbEntry(d', n);
    }

}
*/

/*
lemma allOnlyCorrespondImpliesCorresponds(s:memstate,d:PageDb)
    requires SaneMem(s)
    ensures pageDbCorresponds(s,d)
{
    reveal pageDbEntryCorresponds
}
*/

/*
lemma lemma_ModifiedUserWordsPreservesPageDb(s:state, s':state, pagedb:PageDb, pagedb':PageDb,
                                             dispPg:PageNr, base:nat, user_words:seq<word>)
    requires ValidState(s) && SaneMem(s.m) && ValidState(s') && SaneMem(s'.m)
    requires validPageDb(pagedb)
    requires pageDbCorresponds(s.m, pagedb)
    requires |user_words| == 8;
    requires base == page_monvaddr(dispPg);
    requires extractPage(s.m, dispPg)[base + DISP_CTXT_USER_WORDS + 0 * WORDSIZE] == user_words[0];
    requires extractPage(s.m, dispPg)[base + DISP_CTXT_USER_WORDS + 1 * WORDSIZE] == user_words[1];
    requires extractPage(s.m, dispPg)[base + DISP_CTXT_USER_WORDS + 2 * WORDSIZE] == user_words[2];
    requires extractPage(s.m, dispPg)[base + DISP_CTXT_USER_WORDS + 3 * WORDSIZE] == user_words[3];
    requires extractPage(s.m, dispPg)[base + DISP_CTXT_USER_WORDS + 4 * WORDSIZE] == user_words[4];
    requires extractPage(s.m, dispPg)[base + DISP_CTXT_USER_WORDS + 5 * WORDSIZE] == user_words[5];
    requires extractPage(s.m, dispPg)[base + DISP_CTXT_USER_WORDS + 6 * WORDSIZE] == user_words[6];
    requires extractPage(s.m, dispPg)[base + DISP_CTXT_USER_WORDS + 7 * WORDSIZE] == user_words[7];
    ensures  wellFormedPageDb(pagedb');
    ensures  pageDbCorresponds(s'.m, pagedb')
*/


lemma lemma_SameMemAndGlobalsPreservesPageDb(s:state, s':state, pagedb:PageDb)
    requires ValidState(s) && SaneMem(s.m) && ValidState(s') && SaneMem(s'.m)
    requires validPageDb(pagedb)
    requires pageDbCorresponds(s.m, pagedb)
    requires NonStackMemPreserving(s,s')
    requires GlobalFullContents(s.m, PageDb()) == GlobalFullContents(s'.m, PageDb())
    ensures pageDbCorresponds(s'.m, pagedb)
{
    assert forall p :: validPageNr(p) ==> extractPage(s.m, p) == extractPage(s'.m, p);
}

// TODO: delete this alias
lemma lemma_SameMemAndGlobalsPreservesPageDb'(s:state, s':state, pagedb:PageDb)
    requires ValidState(s) && SaneMem(s.m) && ValidState(s') && SaneMem(s'.m)
    requires validPageDb(pagedb)
    requires pageDbCorresponds(s.m, pagedb)
    requires NonStackMemPreserving(s,s')
    requires GlobalFullContents(s.m, PageDb()) == GlobalFullContents(s'.m, PageDb())
    ensures pageDbCorresponds(s'.m, pagedb)
{
    lemma_SameMemAndGlobalsPreservesPageDb(s, s', pagedb);
}
