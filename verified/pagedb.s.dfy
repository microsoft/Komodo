include "kom_common.s.dfy"
include "Maybe.dfy"
include "Sets.dfy"
include "ARMdef.dfy"

type PageNr = x | validPageNr(x)
type InsecurePageNr = x | validInsecurePageNr(x)

// allow PageNr type decls in spartan procedures.
// unfortunately, we can't return a PageNr, because spartan can't
// propagate the constraints, so this is mostly just window-dressing
function sp_eval_op_PageNr(s:state, o:operand): word
    requires ValidState(s)
    requires ValidOperand(o)
    { OperandContents(s,o) }

function method NR_L1PTES(): int { 256 }
function NR_L2PTES(): int { 1024 }

predicate validPageNr(p: int)
{
    0 <= p < KOM_SECURE_NPAGES()
}

predicate validInsecurePageNr(p: int)
{
    0 <= p < KOM_PHYSMEM_LIMIT() / PAGESIZE()
}

function page_paddr(p: PageNr): addr
    requires validPageNr(p)
    ensures PageAligned(page_paddr(p))
    ensures SecurePhysBase() <= page_paddr(p) < SecurePhysBase() + KOM_SECURE_RESERVE()
{
    assert PageAligned(PAGESIZE());
    assert PageAligned(SecurePhysBase());
    SecurePhysBase() + p * PAGESIZE()
}

function page_monvaddr(p: PageNr): addr
    requires validPageNr(p)
    ensures PageAligned(page_monvaddr(p))
    ensures address_is_secure(page_monvaddr(p))
{
    assert p < KOM_SECURE_NPAGES();
    var pa := page_paddr(p);
    assert pa < SecurePhysBase() + KOM_SECURE_RESERVE();
    pa + KOM_DIRECTMAP_VBASE()
}

predicate addrInPage(m:addr, p:PageNr)
{
    page_monvaddr(p) <= m < page_monvaddr(p) + PAGESIZE()
}

predicate physPageIsInsecureRam(physPage: int)
{
    physPage * PAGESIZE() < SecurePhysBase()
}

predicate physPageIsSecure(physPage: int)
{
    var paddr := physPage * PAGESIZE();
    SecurePhysBase() <= paddr < SecurePhysBase() + KOM_SECURE_RESERVE()
}

datatype PageDbEntryTyped
    = Addrspace(l1ptnr: PageNr, refcount: nat, state: AddrspaceState)
    | Dispatcher(entrypoint:int, entered:bool, ctxt:DispatcherContext)
    | L1PTable(l1pt: seq<Maybe<PageNr>>)
    | L2PTable(l2pt: seq<L2PTE>)
    | DataPage

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
    (e.L1PTable? ==> |e.l1pt| == NR_L1PTES())
    && (e.L2PTable? ==> |e.l2pt| == NR_L2PTES())
}

predicate {:opaque} validPageDb(d: PageDb)
    ensures validPageDb(d) ==> wellFormedPageDb(d)
{
    wellFormedPageDb(d) && pageDbEntriesValid(d) && pageDbEntriesValidRefs(d)
}

// Keep this so that we can leave validPageDb opaque
// and not reveal all of it if we just need WellFormed
lemma validPageDbImpliesWellFormed(d:PageDb)
    requires validPageDb(d)
    ensures wellFormedPageDb(d)
    { reveal_validPageDb(); }

predicate validDispatcherContext(dc:DispatcherContext)
{
      R0  in dc.regs && R1  in dc.regs && R2  in dc.regs && R3  in dc.regs
    && R4  in dc.regs && R5  in dc.regs && R6  in dc.regs && R7  in dc.regs
    && R8  in dc.regs && R9  in dc.regs && R10 in dc.regs && R11 in dc.regs
    && R12 in dc.regs && LR(User) in dc.regs && SP(User) in dc.regs
}

predicate pageDbEntriesValid(d:PageDb)
    requires wellFormedPageDb(d)
{
    forall n :: validPageNr(n) ==> validPageDbEntry(d, n)
}

predicate pageDbEntriesValidRefs(d: PageDb)
    requires wellFormedPageDb(d)
{
    forall n :: validPageNr(n) && d[n].PageDbEntryTyped? ==>  pageDbEntryValidRefs(d, n)
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
    var e := d[n];
    e.PageDbEntryFree? ||
    (e.PageDbEntryTyped? && validPageDbEntryTyped(d, n))
}

predicate validPageDbEntryTyped(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
    requires d[n].PageDbEntryTyped?
{
    wellFormedPageDbEntry(d[n]) && isAddrspace(d, d[n].addrspace)
    // Type-specific requirements
    && (var entry := d[n].entry;
         (entry.Addrspace? && validAddrspace(d, n))
       || (entry.L1PTable? && validL1PTable(d, n))
       || (entry.L2PTable? && validL2PTable(d, n))
       || (entry.Dispatcher? && (entry.entered ==>
            validDispatcherContext(entry.ctxt)))
       || (entry.DataPage?) )
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
    e.PageDbEntryTyped? && e.entry.Addrspace? && e.entry.state == StoppedState
}

// The addrspace of the thing pointed to by n is stopped
predicate hasStoppedAddrspace(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
    requires d[n].PageDbEntryTyped?
{
    var a := d[n].addrspace;
    isAddrspace(d, a) && d[a].entry.state == StoppedState
}


predicate validAddrspace(d: PageDb, n: PageNr)
    requires isAddrspace(d, n)
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

function {:opaque} validPageNrs(): set<PageNr>
    ensures forall n :: n in validPageNrs() <==> validPageNr(n)
{
    SetOfNumbersInRightExclusiveRange(0, KOM_SECURE_NPAGES())
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

predicate validL1PTable(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
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
    d[pte].PageDbEntryTyped? && d[pte].entry.L2PTable?
}

predicate validL2PTable(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
    requires d[n].PageDbEntryTyped? && d[n].entry.L2PTable?
{
    var a := d[n].addrspace;
    stoppedAddrspace(d[a]) ||
        // Not needed when addrspace is stopped: valid PTEs
        forall pte | pte in d[n].entry.l2pt :: validL2PTE(d, a, pte)
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
        case InsecureMapping(pg, w)
            => physPageIsInsecureRam(pg)
        case NoMapping => true
}

/*
function initialPageDb(): PageDb
  ensures validPageDb(initialPageDb())
{
  imap n: PageNr | validPageNr(n) :: PageDbEntryFree
}
*/

//-----------------------------------------------------------------------------
// Utilities 
//-----------------------------------------------------------------------------
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

// a points to an address space and it is closed
predicate validAddrspacePage(d: PageDb, a: int)
{
    wellFormedPageDb(d) && isAddrspace(d, a)
}
