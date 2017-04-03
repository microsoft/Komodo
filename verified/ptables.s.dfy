include "pagedb.s.dfy"

function mkAbsPTE(pte: L2PTE): Maybe<AbsPTE>
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    ensures WellformedAbsPTE(mkAbsPTE(pte))
{
    match pte {
        case SecureMapping(p, w, x) => Just(
            var pa := page_paddr(p);
            assert PageAligned(pa) && isUInt32(pa + PhysBase());
            AbsPTE(pa, w, x))
        case InsecureMapping(p, w) => Just(
            assert validInsecurePageNr(p);
            var pa := p * PAGESIZE;
            assert 0 <= pa < KOM_PHYSMEM_LIMIT;
            assert isUInt32(pa + PhysBase());
            assert PageAligned(pa) by { reveal_PageAligned(); }
            AbsPTE(pa, w, false))
        case NoMapping => Nothing
    }
}

function mkAbsL2PTable(e:PageDbEntryTyped, i:int): AbsL2PTable
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires e.L2PTable? && wellFormedPageDbEntryTyped(e)
    requires 0 <= i < 4
    ensures WellformedAbsL2PTable(mkAbsL2PTable(e, i))
{
    var l2ptes := e.l2pt[i*ARM_L2PTES..(i+1)*ARM_L2PTES];
    var res := MapSeqToSeq(l2ptes, mkAbsPTE);
    assert |res| == ARM_L2PTES;
    res
}

predicate l2tablesmatch(s:memstate, p:PageNr, e:PageDbEntryTyped)
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires ValidMemState(s)
    requires e.L2PTable? && wellFormedPageDbEntryTyped(e)
{
    var vbase := page_monvaddr(p);
    ValidMemRange(vbase, vbase + PAGESIZE)
    && forall i | 0 <= i < 4 ::
        ValidAbsL2PTable(s, vbase + i * ARM_L2PTABLE_BYTES)
        && ExtractAbsL2PTable(s, vbase + i * ARM_L2PTABLE_BYTES) == mkAbsL2PTable(e, i)
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
    requires PhysBase() == KOM_DIRECTMAP_VBASE
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

function {:opaque} mkAbsPTable(d:PageDb, l1:PageNr): AbsPTable
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires validPageDb(d)
    requires nonStoppedL1(d, l1)
    ensures WellformedAbsPTable(mkAbsPTable(d, l1))
{
    assert validL1PTable(d, l1) by { reveal_validPageDb(); }
    var l1pt := d[l1].entry.l1pt;
    var fn := imap l1e:Maybe<PageNr> | l1e in l1pt :: mkAbsPTable'(d, l1e);
    SeqConcat4(IMapSeqToSeq(l1pt, fn))
}

predicate pageTablesCorrespond(s:memstate, d:PageDb)
    requires SaneMem(s) && validPageDb(d)
{
    forall l1p:PageNr | nonStoppedL1(d, l1p) :: ValidAbsL1PTable(s, page_monvaddr(l1p))
       && ExtractAbsL1PTable(s, page_monvaddr(l1p)) == mkAbsPTable(d, l1p)
}
