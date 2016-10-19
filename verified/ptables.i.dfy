include "entry.s.dfy"
include "pagedb.i.dfy"
include "bitvectors.i.dfy"

// XXX: this is placed at the top of the file to work around timeout
// instability when verifying it later in the file
lemma lemma_ptablesmatch(s:memstate, d:PageDb, l1p:PageNr)
    requires SaneMem(s)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires validPageDb(d)
    requires nonStoppedL1(d, l1p)
    requires pageDbCorresponds(s, d)
    ensures ValidAbsL1PTable(s, page_monvaddr(l1p))
    ensures ExtractAbsL1PTable(s, page_monvaddr(l1p)) == mkAbsPTable(d, l1p)
{
    var l1pt := d[l1p].entry.l1pt;
    var l1base := page_monvaddr(l1p);

    assert validL1PTable(d, l1p) by {reveal_validPageDb();}
    lemma_memstatecontainspage(s, l1p);

    assert ARM_L1PTES() == 4 * NR_L1PTES();

    forall k | 0 <= k < ARM_L1PTES()
        ensures ValidAbsL1PTEWord(MemContents(s, l1base + WordsToBytes(k)))
        ensures ExtractAbsL1PTE(MemContents(s, l1base + WordsToBytes(k)))
            == mkAbsL1PTE(l1pt[k / 4], k % 4)
    {
        assert pageDbL1PTableCorresponds(l1p, d[l1p].entry, extractPage(s, l1p))
            by { reveal_pageContentsCorresponds(); }
        reveal_pageDbL1PTableCorresponds();
        lemma_l1ptesmatch(l1pt[k / 4], k % 4);
    }

    forall k | 0 <= k < ARM_L1PTES() && l1pt[k/4].Just?
        ensures l2tablesmatch_opaque(s, l1pt[k/4].v, d[l1pt[k/4].v].entry)
        ensures ValidAbsL2PTable(s, mkAbsL1PTE(l1pt[k/4], k%4).v + PhysBase())
    {
        var i := k/4;
        var j := k%4;
        var l1e := l1pt[i];
        var l2p := l1e.v;
        assert validL1PTE(d, l2p);
        assert pageDbL2PTableCorresponds(l2p, d[l2p].entry, extractPage(s, l2p))
            by { reveal_pageContentsCorresponds(); }
        lemma_l2tablesmatch(s, l2p, d[l2p].entry);
        reveal_l2tablesmatch_opaque();

        assert 4 * ARM_L2PTABLE_BYTES() == PAGESIZE();
        assert page_paddr(l2p) < SecurePhysBase() + KOM_SECURE_RESERVE();
        assert mkAbsL1PTE(l1e, j) == Just(page_paddr(l2p) + j * ARM_L2PTABLE_BYTES());
        calc {
            mkAbsL1PTE(l1e, j).v + PhysBase();
            page_paddr(l2p) + j * ARM_L2PTABLE_BYTES() + PhysBase();
            page_monvaddr(l2p) + j * ARM_L2PTABLE_BYTES();
        }
    }

    assert forall k | 0 <= k < ARM_L1PTES() ::
        ValidAbsL1PTEWord(MemContents(s, l1base + WordsToBytes(k)));
    assert ValidAbsL1PTable(s, l1base);

    forall k | 0 <= k < ARM_L1PTES()
        ensures ExtractAbsL1PTable(s, l1base)[k] == mkAbsPTable(d, l1p)[k]
    {
        var i := k / 4;
        var j := k % 4;
        var l1e := l1pt[i];
        var absl1pte := ExtractAbsL1PTE(MemContents(s, l1base + WordsToBytes(k)));
        assert absl1pte == mkAbsL1PTE(l1e, j);
        if l1e.Just? {
            var l2p := l1e.v;
            assert validL1PTE(d, l2p);
            assert l2tablesmatch(s, l2p, d[l2p].entry)
                by {reveal_l2tablesmatch_opaque();}
            assert absl1pte.Just?;
            calc {
                ExtractAbsL1PTable(s, l1base)[k];
                Just(ExtractAbsL2PTable(s, absl1pte.v + PhysBase()));
                Just(mkAbsL2PTable(d[l2p].entry, j));
                mkAbsPTable(d, l1p)[k];
            }
        } else {
            assert mkAbsL1PTE(l1e, j) == Nothing;
            assert mkAbsPTable(d, l1p)[k] == Nothing;
        }
    }
}

function mkAbsPTE(pte: L2PTE): Maybe<AbsPTE>
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    ensures WellformedAbsPTE(mkAbsPTE(pte))
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

function mkAbsL1PTE(e: Maybe<PageNr>, subpage:int): Maybe<addr>
    requires 0 <= subpage < 4
{
    match e
        case Nothing => Nothing
        case Just(pgNr) =>
            Just(page_paddr(pgNr) + subpage * ARM_L2PTABLE_BYTES())
}

lemma lemma_ARM_L2PTE(pa: word, w: bool, x: bool)
    requires PageAligned(pa) && isUInt32(pa + PhysBase())
    ensures ValidAbsL2PTEWord(ARM_L2PTE(pa, w, x))
    ensures ExtractAbsL2PTE(ARM_L2PTE(pa, w, x)) == Just(AbsPTE(pa, w, x))
{
    lemma_Bitmask12();

    var ptew := ARM_L2PTE(pa, w, x);
    var nxbit:bv32 := if x then 0 else ARM_L2PTE_NX_BIT();
    var robit:bv32 := if w then 0 else ARM_L2PTE_RO_BIT();
    var extrabits := BitOr(BitOr(0xd76, nxbit), robit);
    var pteb := BitOr(WordAsBits(pa), extrabits);

    if x {
        if w {
            assert extrabits == 0xd76 by { reveal_BitOr(); }
        } else {
            assert extrabits == 0xf76 by { reveal_BitOr(); }
        }
    } else {
        if w {
            assert extrabits == 0xd77 by { reveal_BitOr(); }
        } else {
            assert extrabits == 0xf77 by { reveal_BitOr(); }
        }
    }

    assert ptew == BitsAsWord(pteb) by {
        calc {
            ptew;
            ARM_L2PTE(pa, w, x);
            BitsAsWord(BitOr(WordAsBits(pa), BitOr(BitOr(ARM_L2PTE_CONST_BITS() | 0x2, nxbit), robit)));
            { assert ARM_L2PTE_CONST_BITS() | 0x2 == 0xd76; }
            BitsAsWord(BitOr(WordAsBits(pa), BitOr(BitOr(0xd76, nxbit), robit)));
            BitsAsWord(BitOr(WordAsBits(pa), extrabits));
        }
    }
    lemma_WordBitEquiv(ptew, pteb);

    assert BitAnd(extrabits, 0xfffff000) == 0 by {
        reveal_BitOr(); reveal_BitAnd();
    }

    assert BitAnd(WordAsBits(pa), 0xfff) == 0 by {
        assert BitwiseMaskLow(pa, 12) == 0;
        calc {
            BitwiseMaskLow(pa, 12);
            { reveal_BitwiseMaskLow(); }
            BitsAsWord(BitAnd(WordAsBits(pa), BitmaskLow(12)));
            BitsAsWord(BitAnd(WordAsBits(pa), 0xfff));
        }
    }

    calc {
        BitwiseMaskHigh(ptew, 12);
        { reveal_BitwiseMaskHigh(); }
        BitsAsWord(BitAnd(WordAsBits(ptew), BitmaskHigh(12)));
        BitsAsWord(BitAnd(pteb, 0xfffff000));
        BitsAsWord(BitAnd(BitOr(WordAsBits(pa), extrabits), 0xfffff000));
        {
            calc {
                BitAnd(BitOr(WordAsBits(pa), extrabits), 0xfffff000);
                { lemma_BitOrAndRelation(WordAsBits(pa), extrabits, 0xfffff000); }
                BitOr(BitAnd(WordAsBits(pa), 0xfffff000), BitAnd(extrabits, 0xfffff000));
                { assert BitAnd(extrabits, 0xfffff000) == 0 by { reveal_BitAnd(); } }
                BitOr(BitAnd(WordAsBits(pa), 0xfffff000), 0);
                { reveal_BitOr(); }
                BitAnd(WordAsBits(pa), 0xfffff000);
                { assert BitAnd(WordAsBits(pa), 0xfff) == 0; reveal_BitAnd(); }
                WordAsBits(pa);
            }
        }
        BitsAsWord(WordAsBits(pa));
        { lemma_WordAsBitsAsWord(pa); }
        pa;
    }
    assert BitwiseMaskHigh(ptew, 12) == pa;

    assert BitAnd(pteb, 0x3) == 2 || BitAnd(pteb, 0x3) == 3 by {
        calc {
            BitAnd(pteb, 0x3);
            BitAnd(BitOr(WordAsBits(pa), extrabits), 0x3);
            { lemma_BitOrAndRelation(WordAsBits(pa), extrabits, 0x3); }
            BitOr(BitAnd(WordAsBits(pa), 0x3), BitAnd(extrabits, 0x3));
            { calc {
                BitAnd(WordAsBits(pa), 0x3);
                { assert BitAnd(WordAsBits(pa), 0xfff) == 0; reveal_BitAnd(); }
                0;
            } }
            BitOr(0, BitAnd(extrabits, 0x3));
            { reveal_BitOr(); }
            BitAnd(extrabits, 0x3);
        }
        reveal_BitAnd();
    }

    assert BitAnd(pteb, 0xdfc) == ARM_L2PTE_CONST_BITS() by {
        calc {
            BitAnd(pteb, 0xdfc);
            BitAnd(BitOr(WordAsBits(pa), extrabits), 0xdfc);
            { lemma_BitOrAndRelation(WordAsBits(pa), extrabits, 0xdfc); }
            BitOr(BitAnd(WordAsBits(pa), 0xdfc), BitAnd(extrabits, 0xdfc));
            { calc {
                BitAnd(WordAsBits(pa), 0xdfc);
                { assert BitAnd(WordAsBits(pa), 0xfff) == 0; reveal_BitAnd(); }
                0;
            } }
            BitOr(0, BitAnd(extrabits, 0xdfc));
            { reveal_BitOr(); }
            BitAnd(extrabits, 0xdfc);
            { reveal_BitAnd(); }
            0xd74;
            ARM_L2PTE_CONST_BITS();
        }
    }

    assert x == (BitAnd(pteb, ARM_L2PTE_NX_BIT()) == 0) by {
        calc {
            BitAnd(pteb, ARM_L2PTE_NX_BIT());
            BitAnd(BitOr(WordAsBits(pa), extrabits), 1);
            { lemma_BitOrAndRelation(WordAsBits(pa), extrabits, 1); }
            BitOr(BitAnd(WordAsBits(pa), 1), BitAnd(extrabits, 1));
            { calc {
                BitAnd(WordAsBits(pa), 1);
                { assert BitAnd(WordAsBits(pa), 0xfff) == 0; reveal_BitAnd(); }
                0;
            } }
            BitOr(0, BitAnd(extrabits, 1));
            { reveal_BitOr(); }
            BitAnd(extrabits, 1);
            { reveal_BitAnd(); }
            nxbit;
        }
    }

    assert w == (BitAnd(pteb, ARM_L2PTE_RO_BIT()) == 0) by {
        calc {
            BitAnd(pteb, ARM_L2PTE_RO_BIT());
            BitAnd(BitOr(WordAsBits(pa), extrabits), 0x200);
            { lemma_BitOrAndRelation(WordAsBits(pa), extrabits, 0x200); }
            BitOr(BitAnd(WordAsBits(pa), 0x200), BitAnd(extrabits, 0x200));
            { calc {
                BitAnd(WordAsBits(pa), 0x200);
                { assert BitAnd(WordAsBits(pa), 0xfff) == 0; reveal_BitAnd(); }
                0;
            } }
            BitOr(0, BitAnd(extrabits, 0x200));
            { reveal_BitOr(); }
            BitAnd(extrabits, 0x200);
            { reveal_BitAnd(); }
            robit;
        }
    }
}

lemma lemma_l2ptesmatch(pte: L2PTE)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    ensures ValidAbsL2PTEWord(mkL2Pte(pte))
    ensures ExtractAbsL2PTE(mkL2Pte(pte)) == mkAbsPTE(pte)
{
    lemma_Bitmask12();

    var ptew := mkL2Pte(pte);
    var pteb := WordAsBits(ptew);
    lemma_WordBitEquiv(ptew, pteb);
    var extracted := if ValidAbsL2PTEWord(ptew) then Just(ExtractAbsL2PTE(ptew)) else Nothing;

    if pte.NoMapping? {
        assert pteb == 0;
        assert BitAnd(pteb, 0x3) == 0 by { reveal_BitAnd(); }
        assert extracted == Just(Nothing);
    } else {
        var pa, w, x;
        match pte {
            case SecureMapping(p, ws, xs) =>
                pa, w, x := page_paddr(p), ws, xs;
            case InsecureMapping(p, wi) =>
                assert validInsecurePageNr(p);
                pa, w, x := p * PAGESIZE(), wi, false;
        }
        assert ptew == ARM_L2PTE(pa, w, x);
        lemma_ARM_L2PTE(pa, w, x);
        assert isUInt32(pa + PhysBase());
        assert extracted == Just(mkAbsPTE(pte));
    }
}

lemma lemma_l1ptesmatch(e: Maybe<PageNr>, subpage:int)
    requires 0 <= subpage < 4
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    ensures ValidAbsL1PTEWord(mkL1Pte(e, subpage))
    ensures ExtractAbsL1PTE(mkL1Pte(e, subpage)) == mkAbsL1PTE(e, subpage)
{
    var ptew := mkL1Pte(e, subpage);
    var pteb := WordAsBits(ptew);
    lemma_WordBitEquiv(ptew, pteb);

    assert WordAsBits(0x3fc) == 0x3fc && WordAsBits(0x3) == 0x3
        && WordAsBits(1) == 1 by { reveal_WordAsBits(); }

    match e {
    case Nothing => assert ptew == 0; reveal_BitAnd();
    case Just(pg) => {
        var pa := page_paddr(pg) + subpage * ARM_L2PTABLE_BYTES();
        assert pa % ARM_L2PTABLE_BYTES() == 0;
        assert ptew == ARM_L1PTE(pa);

        calc {
            1;
            { lemma_BitOrOneIsLikePlus(pa); }
            BitwiseMaskLow(ptew, 10);
            { reveal_BitwiseMaskLow(); }
            BitsAsWord(BitAnd(WordAsBits(ptew), BitmaskLow(10)));
            { lemma_Bitmask10(); }
            BitsAsWord(BitAnd(WordAsBits(ptew), 0x3ff));
            BitsAsWord(BitAnd(pteb, 0x3ff));
        }
        calc {
            1;
            WordAsBits(BitsAsWord(BitAnd(pteb, 0x3ff)));
            { lemma_BitsAsWordAsBits(BitAnd(pteb, 0x3ff)); }
            BitAnd(pteb, 0x3ff);
        }

        assert BitwiseAnd(ptew, 0x3) == 1 && BitwiseAnd(ptew, 0x3fc) == 0 by {
            assert BitAnd(pteb, 0x3) == 1 && BitAnd(pteb, 0x3fc) == 0 by {
                reveal_BitAnd();
            }
        }

        calc {
            BitwiseMaskHigh(ptew, 10);
            { reveal_BitwiseMaskHigh(); }
            BitsAsWord(BitAnd(WordAsBits(ptew), BitmaskHigh(10)));
            { calc {
                BitAnd(WordAsBits(ptew), BitmaskHigh(10));
                { lemma_Bitmask10(); }
                BitAnd(pteb, 0xfffffc00);
                BitAnd(WordAsBits(ARM_L1PTE(pa)), 0xfffffc00);
                BitAnd(WordAsBits(BitwiseOr(pa, 1)), 0xfffffc00);
                BitAnd(WordAsBits(BitsAsWord(BitOr(WordAsBits(pa), WordAsBits(1)))),
                    0xfffffc00);
                { lemma_BitsAsWordAsBits(BitOr(WordAsBits(pa), WordAsBits(1)));
                  assert WordAsBits(1) == 1 by { reveal_WordAsBits(); } }
                BitAnd(BitOr(WordAsBits(pa), 1), 0xfffffc00);
                BitAnd(BitOr(WordAsBits(pa), 1), 0xfffffc00);
                { lemma_BitOrAndRelation(WordAsBits(pa), 1, 0xfffffc00); }
                BitOr(BitAnd(WordAsBits(pa), 0xfffffc00), BitAnd(1, 0xfffffc00));
                { reveal_BitAnd(); }
                BitOr(BitAnd(WordAsBits(pa), 0xfffffc00), 0);
                { reveal_BitOr(); }
                BitAnd(WordAsBits(pa), 0xfffffc00);
                { calc {
                    0;
                    BitwiseMaskLow(pa, 10);
                    { reveal_BitwiseMaskLow(); }
                    BitsAsWord(BitAnd(WordAsBits(pa), BitmaskLow(10)));
                    { lemma_Bitmask10(); }
                    BitsAsWord(BitAnd(WordAsBits(pa), 0x3ff));
                } assert BitAnd(WordAsBits(pa), 0x3ff) == 0; reveal_BitAnd(); }
                WordAsBits(pa);
            } }
            BitsAsWord(WordAsBits(pa));
            { lemma_WordAsBitsAsWord(pa); }
            pa;
        }
    } }
}

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
    && forall i | 0 <= i < 4 ::
        ValidAbsL2PTable(s, vbase + i * ARM_L2PTABLE_BYTES())
        && ExtractAbsL2PTable(s, vbase + i * ARM_L2PTABLE_BYTES()) == mkAbsL2PTable(e, i)
}

predicate {:opaque} l2tablesmatch_opaque(s:memstate, p:PageNr, e:PageDbEntryTyped)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires ValidMemState(s)
    requires e.L2PTable? && wellFormedPageDbEntryTyped(e)
{
    l2tablesmatch(s, p, e)
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

    forall i | 0 <= i < 4
        ensures ValidAbsL2PTable(s, base + i * ARM_L2PTABLE_BYTES())
        ensures ExtractAbsL2PTable(s, base + i * ARM_L2PTABLE_BYTES()) == mkAbsL2PTable(e, i) {

        var subbase := base + i * ARM_L2PTABLE_BYTES();

        forall j | 0 <= j < ARM_L2PTES()
            ensures ValidAbsL2PTEWord(MemContents(s, subbase + WordsToBytes(j)))
            ensures mkAbsPTE(l2pt[i * ARM_L2PTES() + j]) == mkAbsL2PTable(e, i)[j]
                    == ExtractAbsL2PTE(MemContents(s, subbase + WordsToBytes(j))) {

            var idx := i * ARM_L2PTES() + j;
            var pte := l2pt[idx];
            var a1 := base + WordsToBytes(i * ARM_L2PTES() + j);
            var a2 := subbase + WordsToBytes(j);
            assert a1 == a2;
            var w := MemContents(s, a2);

            assert ValidAbsL2PTEWord(w) && ExtractAbsL2PTE(w) == mkAbsPTE(pte) by {
                lemma_memstatecontainspage(s, p);
                reveal_pageDbL2PTableCorresponds();
                assert w == mkL2Pte(pte);
                assert i * ARM_L2PTABLE_BYTES() + WordsToBytes(j) == WordsToBytes(idx);
                lemma_l2ptesmatch(pte);
            }
        }

        assert ValidAbsL2PTable(s, subbase);
        assert |mkAbsL2PTable(e, i)| == |ExtractAbsL2PTable(s, subbase)| == ARM_L2PTES();
    }
}

// concat a sequence of sequences, where all the subsequences have length 4
function {:opaque} SeqConcat4<T>(s:seq<seq<T>>): seq<T>
    requires forall i | 0 <= i < |s| :: |s[i]| == 4
    ensures |SeqConcat4<T>(s)| == 4 * |s|
    ensures forall i | 0 <= i < 4 * |s| :: SeqConcat4<T>(s)[i] == s[i / 4][i % 4]
{
    if |s| == 0 then []
    else s[0] + SeqConcat4(s[1..])
}

function mkAbsPTable'(d:PageDb, l1e:Maybe<PageNr>): seq<Maybe<AbsL2PTable>>
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires validPageDb(d)
    requires l1e.Just? ==> d[l1e.v].PageDbEntryTyped? && d[l1e.v].entry.L2PTable?
        && wellFormedPageDbEntryTyped(d[l1e.v].entry)
    ensures var r := mkAbsPTable'(d, l1e);
        |r| == 4 && forall i :: 0 <= i < |r| && r[i].Just? ==> WellformedAbsL2PTable(r[i].v)
{
    if l1e.Nothing? then [Nothing, Nothing, Nothing, Nothing]
    else
        var e := d[l1e.v].entry;
        [Just(mkAbsL2PTable(e, 0)), Just(mkAbsL2PTable(e, 1)),
         Just(mkAbsL2PTable(e, 2)), Just(mkAbsL2PTable(e, 3))]
}

function mkAbsPTable(d:PageDb, l1:PageNr): AbsPTable
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires validPageDb(d)
    requires nonStoppedL1(d, l1)
    ensures WellformedAbsPTable(mkAbsPTable(d, l1))
{
    assert validL1PTable(d, l1) by { reveal_validPageDb(); }
    var l1pt := d[l1].entry.l1pt;
    var fn := imap l1e:Maybe<PageNr> | l1e in l1pt :: mkAbsPTable'(d, l1e);
    SeqConcat4(IMapSeqToSeq(l1pt, fn))
}

lemma lemma_PageAlignedAdd(x:int, y:int)
    requires x % 0x1000 == y % 0x1000 == 0
    ensures (x + y) % 0x1000 == 0
{
    // sigh. why do I need a lemma to prove this??
}

lemma lemma_WritablePages(d:PageDb, l1p:PageNr, pagebase:addr)
    requires PhysBase() == KOM_DIRECTMAP_VBASE()
    requires validPageDb(d)
    requires nonStoppedL1(d, l1p)
    requires PageAligned(pagebase) && address_is_secure(pagebase)
    requires pagebase in WritablePagesInTable(mkAbsPTable(d, l1p))
    ensures pageSWrInAddrspace(d, l1p, monvaddr_page(pagebase))
{
    assert validL1PTable(d, l1p) by { reveal_validPageDb(); }
    var abspt := mkAbsPTable(d, l1p);
    var l1pt := d[l1p].entry.l1pt;
    var i, j :| 0 <= i < ARM_L1PTES() && 0 <= j < ARM_L2PTES()
        && abspt[i].Just? && abspt[i].v[j].Just? && abspt[i].v[j].v.write
        && pagebase == abspt[i].v[j].v.phys + PhysBase();
    var p := monvaddr_page(pagebase);
    assert p == (abspt[i].v[j].v.phys - SecurePhysBase()) / PAGESIZE();
    var n := i / 4;
    assert l1pt[n].Just?;
    var l2p := l1pt[n].v;
    assert d[l2p].PageDbEntryTyped? && d[l2p].entry.L2PTable?
        && wellFormedPageDbEntry(d[l2p]) && validL2PTable(d, l2p)
        by { reveal_validPageDb(); }
    var l2pt := d[l2p].entry.l2pt;
    var pte := l2pt[(i%4)*ARM_L2PTES() + j];
    assert validL2PTE(d, d[l2p].addrspace, pte);
    assert mkAbsPTE(pte) == abspt[i].v[j];
    assert pte.SecureMapping? && pte.write;
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
    var abspt := mkAbsPTable(d, l1);
    lemma_ptablesmatch(s.m, d, l1);
    assert ExtractAbsPageTable(s) == Just(abspt);
    assert forall a | ValidMem(a)
        && BitwiseMaskHigh(a, 12) !in WritablePagesInTable(abspt)
        :: MemContents(s'.m, a) == MemContents(s.m, a);
    forall a | ValidMem(a) && address_is_secure(a)
        && BitwiseMaskHigh(a, 12) in WritablePagesInTable(abspt)
        ensures memSWrInAddrspace(d, l1, a)
    {
        // sigh. there's a surprising amount of cruft here to prove
        // that the page base is secure and on the same page as 'a'
        var pagebase := BitwiseMaskHigh(a, 12);
        lemma_bitMaskAddrInPage(a, pagebase, l1);
        lemma_WritablePages(d, l1, pagebase);
    }
}


lemma lemma_bitMaskAddrInPage(a:addr, pagebase:addr, p:PageNr)
    requires address_is_secure(a);
    requires pagebase == BitwiseMaskHigh(a, 12);
    ensures addrInPage(a, p) <==> addrInPage(pagebase, p);
    ensures PageAligned(pagebase) && address_is_secure(pagebase)
{
    // sigh. there's a surprising amount of cruft here to prove
    // that the page base is secure and on the same page as 'a'
    var pagebase := BitwiseMaskHigh(a, 12);
    var securebase := KOM_DIRECTMAP_VBASE() + SecurePhysBase();
    assert PageAligned(pagebase);
    assert pagebase == a / PAGESIZE() * PAGESIZE();
    lemma_PageAlignedAdd(KOM_DIRECTMAP_VBASE(), SecurePhysBase());
    assert PageAligned(securebase);
    assert pagebase == a - a % PAGESIZE();
    if (a / 0x1000 == securebase / 0x1000) {
        assert pagebase / 0x1000 == securebase / 0x1000;
    }
    assert securebase <= pagebase <= a;
    assert address_is_secure(pagebase);
}
