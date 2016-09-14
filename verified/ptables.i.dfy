include "pagedb.i.dfy"
include "entry.s.dfy"

function mkAbsPTE(pte: L2PTE): Maybe<AbsPTE>
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    ensures var r := mkAbsPTE(pte); r.Just? ==> WellformedAbsPTE(r.v)
{
    match pte {
        case SecureMapping(p, w, x) => Just(
            var pa := page_paddr(p);
            assert PageAligned(pa) && isUInt32(pa + PhysBase());
            AbsPTE(pa, w, x))
        case InsecureMapping(p, w) => Just(
            assert validInsecurePageNr(p);
            var pa := p * PAGESIZE();
            assert 0 <= pa < KOM_PHYSMEM_LIMIT();
            assert PageAligned(pa) && isUInt32(pa + PhysBase());
            AbsPTE(pa, w, false))
        case NoMapping => Nothing
    }
}

lemma {:axiom} lemma_l2ptesmatch(pte: L2PTE)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    ensures ExtractAbsL2PTE(mkL2Pte(pte)) == Just(mkAbsPTE(pte))
/* FIXME: this is really gross right now (and contains several
 * assumes!), largely due to problems in Boogie/Dafny's bitvector
 * support. It's also hopelessly unstable.
{
    var pteword := mkL2Pte(pte);
    var ptebv := IntAsBits(pteword);
    var extracted := ExtractAbsL2PTE(pteword);
    if pte.NoMapping? {
        assert ptebv == 0;
        assert extracted == Just(Nothing) by {reveal_BitAnd();}
    } else {
        var pa, w, x;
        match pte {
            case SecureMapping(p, ws, xs) =>
                pa, w, x := page_paddr(p), ws, xs;
            case InsecureMapping(p, wi) =>
                pa, w, x := p * PAGESIZE(), wi, false;
        }
        assert pteword == ARM_L2PTE(pa, w, x);
        var pabv := IntAsBits(pa);
        assert PAGESIZE() == 0x1000 == pow2(12) by { reveal_pow2(); }
        assert pa % PAGESIZE() == 0;
        assert BitmaskLow(12) == 0xfff by { reveal_BitmaskLow(); assume 1 as bv32 << 12 == 0x1000; }
        reveal_BitAnd();
        assert BitAnd(pabv, 0xfff) == 0 by { lemma_Bitmask(pabv, 12); lemma_BitModEquiv(pabv, 0x1000); }
        var nxbit:bv32 := if x then 0 else ARM_L2PTE_NX_BIT();
        var robit:bv32 := if w then 0 else ARM_L2PTE_RO_BIT();
        assert ARM_L2PTE_NX_BIT() == 1 && ARM_L2PTE_RO_BIT() == 0x200;
        assert ptebv == pabv | ARM_L2PTE_CONST_BITS() | 0x2 | nxbit | robit;
        assert BitAnd(ptebv, 0x3) == 2;
        assert BitAnd(ptebv, 0xfdfc) == ARM_L2PTE_CONST_BITS();
        assert BitAnd(ptebv, 0xfffff000) == IntAsBits(pa);
        assert pa == BitwiseMaskHigh(pteword, 12) by { reveal_BitmaskHigh(); reveal_BitNot(); assume 1 as bv32 << 12 == 0x1000; }
        assert ptebv & ARM_L2PTE_NX_BIT() == nxbit;
        assert ptebv & ARM_L2PTE_RO_BIT() == robit;
        assert isUInt32(pa + PhysBase());
        assert extracted == Just(mkAbsPTE(pte));
    }
} */

/*
function getAbsPTE(d:PageDb, l2:PageNr, i:int, j:int): Maybe<AbsPTE>
    requires validPageDb(d)
    requires validL2PTPage(d, l2) && !hasStoppedAddrspace(d, l2)
    requires 0 <= i < 4 && 0 <= j < ARM_L2PTES()
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    ensures var r := getAbsPTE(d, l2, i, j); r.Just? ==> WellformedAbsPTE(r.v)
{
    mkAbsPTE(d[l2].entry.l2pt[i * 4 + j])
}
*/

function mkAbsL2PTable(e:PageDbEntryTyped, i:int): AbsL2PTable
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires e.L2PTable? && wellFormedPageDbEntryTyped(e)
    requires 0 <= i < 4
    ensures WellformedAbsL2PTable(mkAbsL2PTable(e, i))
{
    var l2ptes := e.l2pt[i*ARM_L2PTES()..(i+1)*ARM_L2PTES()];
    var res := MapSeqToSeq(l2ptes, mkAbsPTE);
    assert |res| == ARM_L2PTES();
    res
}

function mkAbsPTable'(d:PageDb, l1:PageNr, idx:int): AbsPTable
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires validPageDb(d)
    requires nonStoppedL1(d, l1)
    requires 0 <= idx <= NR_L1PTES()
    decreases NR_L1PTES() - idx
    ensures var r := mkAbsPTable'(d, l1, idx);
        |r| == (NR_L1PTES() - idx) * 4
        && forall i :: 0 <= i < |r| && r[i].Just? ==> WellformedAbsL2PTable(fromJust(r[i]))
{
    if idx == NR_L1PTES() then [] else
        var l2e := d[l1].entry.l1pt[idx];
        var first :=
            if l2e.Nothing?
            then [Nothing, Nothing, Nothing, Nothing]
            else
                assert validL1PTable(d, l1) by { reveal_validPageDb(); }
                var e' := d[fromJust(l2e)];
                assert e'.PageDbEntryTyped?;
                var e := e'.entry;
                assert e.L2PTable? && wellFormedPageDbEntryTyped(e);
                [Just(mkAbsL2PTable(e, 0)), Just(mkAbsL2PTable(e, 1)),
                 Just(mkAbsL2PTable(e, 2)), Just(mkAbsL2PTable(e, 3))];
        first + mkAbsPTable'(d, l1, idx + 1)
}

lemma lemma_memstatecontainspage(s:memstate, p:PageNr)
    requires SaneMem(s)
    ensures memContainsPage(s.addresses, p)
{
    var va := page_monvaddr(p);
    assert ValidMemRange(va, va + PAGESIZE());
    reveal_ValidMemState();
}

predicate l2tablesmatch(s:memstate, p:PageNr, e:PageDbEntryTyped)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires ValidMemState(s)
    requires e.L2PTable? && wellFormedPageDbEntryTyped(e)
{
    var vbase := page_monvaddr(p);
    ValidMemRange(vbase, vbase + PAGESIZE())
    && forall i | 0 <= i < 4 :: ExtractAbsL2PTable(s, vbase + i * ARM_L2PTABLE_BYTES(), 0)
        == Just(mkAbsL2PTable(e, i))
}

lemma lemma_ExtractAbsL2PTable(m:memstate, vbase:addr, i:nat)
    requires ValidMemState(m)
    requires WordAligned(vbase)
        && ValidMemRange(vbase, vbase + ARM_L2PTABLE_BYTES())
    requires 0 <= i <= ARM_L2PTES()
    requires forall j | 0 <= j < ARM_L2PTES() :: ExtractAbsL2PTE(MemContents(m, vbase + WordsToBytes(j))).Just?
    ensures ExtractAbsL2PTable(m, vbase, i).Just?
    ensures forall j | 0 <= j < ARM_L2PTES() - i :: ExtractAbsL2PTable(m, vbase, i).v[j] == ExtractAbsL2PTE(MemContents(m, vbase + WordsToBytes(j+i))).v
    decreases ARM_L2PTES() - i
{
    if (i != ARM_L2PTES()) {
        var r := ExtractAbsL2PTable(m, vbase, i);
        var rest := ExtractAbsL2PTable(m, vbase, i + 1);
        var pte := ExtractAbsL2PTE(MemContents(m, vbase + WordsToBytes(i)));
        assert pte.Just?;
        lemma_ExtractAbsL2PTable(m, vbase, i + 1);
        assert rest.Just?;
        assert r == Just([fromJust(pte)] + fromJust(rest));
    }
}

lemma lemma_l2tablesmatch(s:memstate, p:PageNr, e:PageDbEntryTyped)
    requires SaneMem(s)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires e.L2PTable? && wellFormedPageDbEntryTyped(e)
    requires pageDbL2PTableCorresponds(p, e, extractPage(s, p))
    ensures l2tablesmatch(s, p, e)
{
    var l2pt := e.l2pt;
    var base := page_monvaddr(p);

    assert ARM_L2PTES() * 4 == NR_L2PTES();
    forall i, j | 0 <= i < 4 && 0 <= j < ARM_L2PTES()
        ensures ExtractAbsL2PTE(MemContents(s, base + WordsToBytes(i * ARM_L2PTES() + j))) == Just(mkAbsPTE(l2pt[i * ARM_L2PTES() + j])) {
        var idx := i * ARM_L2PTES() + j;
        var pte := l2pt[idx];
        lemma_memstatecontainspage(s, p);
        reveal_pageDbL2PTableCorresponds();
        assert MemContents(s, base + WordsToBytes(idx)) == mkL2Pte(pte);
        assert i * ARM_L2PTABLE_BYTES() + WordsToBytes(j) == WordsToBytes(idx);
        lemma_l2ptesmatch(pte);
    }

    forall i | 0 <= i < 4
        ensures ExtractAbsL2PTable(s, base + i * ARM_L2PTABLE_BYTES(), 0)
        == Just(mkAbsL2PTable(e, i)) {
        assert forall j | 0 <= j < ARM_L2PTES() ::
            mkAbsL2PTable(e, i)[j] == mkAbsPTE(l2pt[i * ARM_L2PTES() + j]) == ExtractAbsL2PTE(MemContents(s, base + i * ARM_L2PTABLE_BYTES() + WordsToBytes(j))).v;
        lemma_ExtractAbsL2PTable(s, base + i * ARM_L2PTABLE_BYTES(), 0);
        assert |mkAbsL2PTable(e, i)| == |ExtractAbsL2PTable(s, base + i * ARM_L2PTABLE_BYTES(), 0).v| == ARM_L2PTES();
        assert forall j | 0 <= j < ARM_L2PTES() :: base + i * ARM_L2PTABLE_BYTES() + WordsToBytes(j) == base + WordsToBytes(j + i*ARM_L2PTES());
    }
}

function mkAbsPTable(d:PageDb, l1:PageNr): AbsPTable
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires validPageDb(d)
    requires nonStoppedL1(d, l1)
    ensures WellformedAbsPTable(mkAbsPTable(d, l1))
{
    mkAbsPTable'(d, l1, 0)
}

lemma lemma_ptablesmatch(s:memstate, d:PageDb, l1p:PageNr)
    requires SaneMem(s)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires validPageDb(d)
    requires nonStoppedL1(d, l1p)
    requires pageDbCorresponds(s, d)
    ensures ExtractAbsL1PTable(s, page_monvaddr(l1p), 0) == Just(mkAbsPTable(d, l1p))
{
    assume false; // TODO
}

lemma UserExecutionMemInvariant(s:state, s':state, d:PageDb, l1:PageNr)
    requires ValidState(s) && SaneMem(s.m)
    requires evalUserspaceExecution(s, s')
    requires validPageDb(d)
    requires pageDbCorresponds(s.m, d)
    requires nonStoppedL1(d, l1)
    requires s.conf.ttbr0.ptbase == page_paddr(l1)
    ensures WSMemInvariantExceptAddrspaceAtPage(s, s', d, l1)
{
    var l1pg := extractPage(s.m, l1);
    var e := d[l1].entry;
    assert e.L1PTable? && wellFormedPageDbEntryTyped(e);
    assert pageContentsCorresponds(l1, d[l1], l1pg);
    reveal_pageContentsCorresponds();
    assert pageDbL1PTableCorresponds(l1, e, l1pg);
    assume false; // TODO
}
