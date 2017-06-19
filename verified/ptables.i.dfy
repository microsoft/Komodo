include "entry.s.dfy"
include "ptables.s.dfy"
include "pagedb.i.dfy"
include "ptebits.i.dfy"

// XXX: this is placed at the top of the file to work around timeout
// instability when verifying it later in the file
lemma lemma_PageAlignedAdd(x:nat, y:nat)
    requires PageAligned(x) && PageAligned(y)
    ensures PageAligned(x + y)
{
    // sigh. why do I need a lemma to prove this??
    reveal PageAligned();
}

// XXX: this is placed at the top of the file to work around timeout
// instability when verifying it later in the file
lemma lemma_ptablesmatch(s:memstate, d:PageDb, l1p:PageNr)
    requires SaneMem(s)
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires validPageDb(d)
    requires nonStoppedL1(d, l1p)
    requires pageDbCorresponds(s, d)
    ensures ValidAbsL1PTable(s, page_monvaddr(l1p))
    ensures ExtractAbsL1PTable(s, page_monvaddr(l1p)) == mkAbsPTable(d, l1p)
{
    var l1pt := d[l1p].entry.l1pt;
    var l1base := page_monvaddr(l1p);

    assert validL1PTable(d, l1p) by { reveal_validPageDb(); }
    lemma_memstatecontainspage(s, l1p);

    assert ARM_L1PTES == 4 * NR_L1PTES;

    forall k | 0 <= k < ARM_L1PTES
        ensures ValidAbsL1PTEWord(MemContents(s, WordOffset(l1base, k)))
        ensures ExtractAbsL1PTE(MemContents(s, WordOffset(l1base, k)))
            == mkAbsL1PTE(l1pt[k / 4], k % 4)
    {
        assert pageDbL1PTableCorresponds(l1p, d[l1p].entry, extractPage(s, l1p))
            by { reveal_pageContentsCorresponds(); }
        reveal pageDbL1PTableCorresponds();
        lemma_l1ptesmatch(l1pt[k / 4], k % 4);
    }

    forall k | 0 <= k < ARM_L1PTES && l1pt[k/4].Just?
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
        reveal l2tablesmatch_opaque();

        assert 4 * ARM_L2PTABLE_BYTES == PAGESIZE;
        assert page_paddr(l2p) < SecurePhysBase() + KOM_SECURE_RESERVE;
        assert mkAbsL1PTE(l1e, j) == Just(page_paddr(l2p) + j * ARM_L2PTABLE_BYTES);
        calc {
            mkAbsL1PTE(l1e, j).v + PhysBase();
            page_paddr(l2p) + j * ARM_L2PTABLE_BYTES + PhysBase();
            page_monvaddr(l2p) + j * ARM_L2PTABLE_BYTES;
        }
    }

    assert forall k | 0 <= k < ARM_L1PTES ::
        ValidAbsL1PTEWord(MemContents(s, WordOffset(l1base, k)));
    assert {:split_here} ValidAbsL1PTable(s, l1base);

    forall k | 0 <= k < ARM_L1PTES
        ensures ExtractAbsL1PTable(s, l1base)[k] == mkAbsPTable(d, l1p)[k]
    {
        var i := k / 4;
        var j := k % 4;
        var l1e := l1pt[i];
        var absl1pte := ExtractAbsL1PTE(MemContents(s, WordOffset(l1base, k)));
        assert absl1pte == mkAbsL1PTE(l1e, j);
        reveal ExtractAbsL1PTable();
        if l1e.Just? {
            var l2p := l1e.v;
            assert validL1PTE(d, l2p);
            calc {
                ExtractAbsL1PTable(s, l1base)[k];
                { assert absl1pte.Just?; }
                Just(ExtractAbsL2PTable(s, absl1pte.v + KOM_DIRECTMAP_VBASE));
                {
                    assert absl1pte.v + KOM_DIRECTMAP_VBASE
                            == page_monvaddr(l2p) + j * ARM_L2PTABLE_BYTES;
                    reveal l2tablesmatch_opaque();
                }
                Just(mkAbsL2PTable(d[l2p].entry, j));
                { reveal mkAbsPTable(); }
                mkAbsPTable(d, l1p)[k];
            }
        } else {
            reveal mkAbsPTable();
            assert mkAbsL1PTE(l1e, j) == Nothing;
            assert mkAbsPTable(d, l1p)[k] == Nothing;
        }
    }
}

lemma lemma_l2ptesmatch(pte: L2PTE)
    requires PhysBase() == KOM_DIRECTMAP_VBASE
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
                pa, w, x := p * PAGESIZE, wi, false;
                assert PageAligned(pa) by { reveal_PageAligned(); }
        }
        assert ptew == ARM_L2PTE(pa, w, x);
        lemma_ARM_L2PTE(pa, w, x);
        assert isUInt32(pa + PhysBase());
        assert extracted == Just(mkAbsPTE(pte));
    }
}

lemma lemma_memstatecontainspage(s:memstate, p:PageNr)
    requires SaneMem(s)
    ensures memContainsPage(s.addresses, p)
{
    var va := page_monvaddr(p);
    assert ValidMemRange(va, va + PAGESIZE);
    reveal ValidMemState();
}

predicate {:opaque} l2tablesmatch_opaque(s:memstate, p:PageNr, e:PageDbEntryTyped)
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires ValidMemState(s)
    requires e.L2PTable? && wellFormedPageDbEntryTyped(e)
{
    l2tablesmatch(s, p, e)
}

lemma lemma_l2tablesmatch(s:memstate, p:PageNr, e:PageDbEntryTyped)
    requires SaneMem(s)
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires e.L2PTable? && wellFormedPageDbEntryTyped(e)
    requires pageDbL2PTableCorresponds(p, e, extractPage(s, p))
    ensures l2tablesmatch_opaque(s, p, e)
{
    var l2pt := e.l2pt;
    var base := page_monvaddr(p);
    reveal l2tablesmatch_opaque();

    assert ARM_L2PTES * 4 == NR_L2PTES;

    forall i | 0 <= i < 4
        ensures ValidAbsL2PTable(s, base + i * ARM_L2PTABLE_BYTES)
        ensures ExtractAbsL2PTable(s, base + i * ARM_L2PTABLE_BYTES) == mkAbsL2PTable(e, i) {

        var subbase := base + i * ARM_L2PTABLE_BYTES;

        forall j | 0 <= j < ARM_L2PTES
            ensures ValidAbsL2PTEWord(MemContents(s, WordOffset(subbase, j)))
            ensures mkAbsPTE(l2pt[i * ARM_L2PTES + j]) == mkAbsL2PTable(e, i)[j]
                    == ExtractAbsL2PTE(MemContents(s, WordOffset(subbase, j))) {

            var idx := i * ARM_L2PTES + j;
            var pte := l2pt[idx];
            var a1 := base + WordsToBytes(i * ARM_L2PTES + j);
            var a2 := subbase + WordsToBytes(j);
            assert a1 == a2;
            var w := MemContents(s, a2);

            assert ValidAbsL2PTEWord(w) && ExtractAbsL2PTE(w) == mkAbsPTE(pte) by {
                lemma_memstatecontainspage(s, p);
                reveal pageDbL2PTableCorresponds();
                assert w == mkL2Pte(pte);
                assert i * ARM_L2PTABLE_BYTES + WordsToBytes(j) == WordsToBytes(idx);
                lemma_l2ptesmatch(pte);
            }
        }

        assert ValidAbsL2PTable(s, subbase);
        assert |mkAbsL2PTable(e, i)| == |ExtractAbsL2PTable(s, subbase)| == ARM_L2PTES;
    }
}

lemma lemma_WritablePages(d:PageDb, l1p:PageNr, pagebase:addr)
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires validPageDb(d)
    requires nonStoppedL1(d, l1p)
    requires PageAligned(pagebase) && address_is_secure(pagebase)
    requires pagebase in WritablePagesInTable(mkAbsPTable(d, l1p))
    ensures pageSWrInAddrspace(d, l1p, monvaddr_page(pagebase))
{
    assert validL1PTable(d, l1p) by { reveal_validPageDb(); }
    var abspt := mkAbsPTable(d, l1p);
    var l1pt := d[l1p].entry.l1pt;
    var i, j :| 0 <= i < ARM_L1PTES && 0 <= j < ARM_L2PTES
        && abspt[i].Just? && abspt[i].v[j].Just? && abspt[i].v[j].v.write
        && pagebase == abspt[i].v[j].v.phys + PhysBase();
    var p := monvaddr_page(pagebase);
    reveal mkAbsPTable();
    assert p == (abspt[i].v[j].v.phys - SecurePhysBase()) / PAGESIZE;
    var n := i / 4;
    assert l1pt[n].Just?;
    var l2p := l1pt[n].v;
    assert d[l2p].PageDbEntryTyped? && d[l2p].entry.L2PTable?
        && wellFormedPageDbEntry(d[l2p]) && validL2PTable(d, l2p)
        by { reveal_validPageDb(); }
    var l2pt := d[l2p].entry.l2pt;
    var pte := l2pt[(i%4)*ARM_L2PTES + j];
    assert validL2PTE(d, d[l2p].addrspace, pte);
    assert mkAbsPTE(pte) == abspt[i].v[j];
    assert pte.SecureMapping? && pte.write;
}

lemma UserExecutionMemInvariant(s:state, s':state, d:PageDb, l1:PageNr)
    requires ValidState(s) && SaneMem(s.m)
    requires mode_of_state(s) == User && ExtractAbsPageTable(s).Just?
    requires exists pc:word :: s' == userspaceExecutionFn(s, pc).0
    requires validPageDb(d)
    requires pageDbCorresponds(s.m, d)
    requires nonStoppedL1(d, l1)
    requires s.conf.ttbr0.ptbase == page_paddr(l1)
    ensures WSMemInvariantExceptAddrspaceAtPage(s, s', d, l1)
{
    var abspt := mkAbsPTable(d, l1);
    lemma_ptablesmatch(s.m, d, l1);
    assert ExtractAbsPageTable(s) == Just(abspt);
    forall a | ValidMem(a) && address_is_secure(a)
        ensures memSWrInAddrspace(d, l1, a)
            || MemContents(s.m, a) == MemContents(s'.m, a)
    {
        var pagebase := PageBase(a);
        if pagebase !in WritablePagesInTable(abspt) {
            assert MemContents(s'.m, a) == MemContents(s.m, a)
                by { reveal_userspaceExecutionFn(); }
        } else {
            var page := lemma_secure_addrInPage(a);
            lemma_WritablePages(d, l1, pagebase);
            assert memSWrInAddrspace(d, l1, a);
        }
    }
}

lemma lemma_secure_addrInPage(a:addr) returns (p:PageNr)
    requires address_is_secure(a)
    ensures address_is_secure(PageBase(a))
    ensures p == monvaddr_page(PageBase(a))
    ensures addrInPage(a, p)
{
    var pagebase := PageBase(a);
    var dummy:PageNr;
    lemma_bitMaskAddrInPage(a, dummy);
    p := monvaddr_page(pagebase);
    lemma_bitMaskAddrInPage(a, p);
    assert addrInPage(a, p);
}

lemma lemma_bitMaskAddrInPage(a:addr, p:PageNr)
    requires address_is_secure(a);
    ensures addrInPage(a, p) <==> addrInPage(PageBase(a), p);
    ensures PageAligned(PageBase(a)) && address_is_secure(PageBase(a))
{
    var pagebase := BitwiseMaskHigh(a, 12);
    assert pagebase == PageBase(a) by { reveal_PageBase(); }

    // sigh. there's a surprising amount of cruft here to prove
    // that the page base is secure and on the same page as 'a'
    var securebase := KOM_DIRECTMAP_VBASE + SecurePhysBase();
    assert PageAligned(pagebase) by { reveal_PageAligned(); }
    assert PageAligned(KOM_DIRECTMAP_VBASE) by { reveal_PageAligned(); }
    lemma_PageAlignedAdd(KOM_DIRECTMAP_VBASE, SecurePhysBase());
    assert PageAligned(securebase);

    calc {
        pagebase;
        { reveal PageAligned(); }
        a / PAGESIZE * PAGESIZE;
    }

    if (a / PAGESIZE == securebase / PAGESIZE) {
        assert pagebase / PAGESIZE == securebase / PAGESIZE;
    }
    assert securebase <= pagebase <= a by { reveal_PageAligned(); }
    assert address_is_secure(pagebase);
}
