include "pagedb.i.dfy"
include "bitvectors.i.dfy"

function method L2PTE_CONST_BITS(): bv32
    { ARM_L2PTE_CONST_BITS | 0x2 }

function method L2PTE_CONST_WORD(): word
    { L2PTE_CONST_BITS() as word }

lemma lemma_ARM_L2PTE_PageMask(x:bv32)
    requires BitAnd(x, 0xfff) == 0
    ensures BitAnd(x, 1) == 0
    ensures BitAnd(x, 0x3) == 0
    ensures BitAnd(x, 0x200) == 0
    ensures BitAnd(x, 0xdfc) == 0
{ reveal BitAnd(); }

lemma lemma_ARM_L2PTE_helper(pa: word, w: bool, x: bool, ptew: word,
    nxbit: bv32, robit: bv32, extrabits: bv32, pteb: bv32)
    requires PageAligned(pa) && isUInt32(pa + PhysBase())
    requires ptew == ARM_L2PTE(pa, w, x)
    requires nxbit == if x then 0 else ARM_L2PTE_NX_BIT
    requires robit == if w then 0 else ARM_L2PTE_RO_BIT
    requires extrabits == BitOr(BitOr(L2PTE_CONST_BITS(), nxbit), robit)
    requires pteb == BitOr(WordAsBits(pa), extrabits)
    ensures extrabits == (
        if x && w then 0x7e
        else if x && !w then 0x27e
        else if !x && w then 0x7f
        else 0x27f)
    ensures ptew == BitsAsWord(pteb)
    ensures BitAnd(extrabits, 0xfffff000) == 0
    ensures BitAnd(WordAsBits(pa), 0xfff) == 0
    ensures PageBase(ptew) == pa;
    ensures BitAnd(pteb, 0x3) == 2 || BitAnd(pteb, 0x3) == 3
    ensures BitAnd(pteb, 0xdfc) == ARM_L2PTE_CONST_BITS
{
    assert extrabits == (
        if x && w then 0x7e
        else if x && !w then 0x27e
        else if !x && w then 0x7f
        else 0x27f) by { reveal_BitOr(); }

    assert ptew == BitsAsWord(pteb) by {
        calc {
            ptew;
            ARM_L2PTE(pa, w, x);
            BitsAsWord(BitOr(WordAsBits(pa), BitOr(BitOr(ARM_L2PTE_CONST_BITS | 0x2, nxbit), robit)));
            { assert ARM_L2PTE_CONST_BITS | 0x2 == L2PTE_CONST_BITS(); }
            BitsAsWord(BitOr(WordAsBits(pa), BitOr(BitOr(L2PTE_CONST_BITS(), nxbit), robit)));
            BitsAsWord(BitOr(WordAsBits(pa), extrabits));
        }
    }
    lemma_WordBitEquiv(ptew, pteb);

    assert BitAnd(extrabits, 0xfffff000) == 0 by {
        reveal BitAnd();
    }

    assert BitAnd(WordAsBits(pa), 0xfff) == 0 by {
        assert BitwiseMaskLow(pa, 12) == 0 by { reveal_PageAligned(); }
        calc {
            BitwiseMaskLow(pa, 12);
            { reveal BitwiseMaskLow(); }
            BitsAsWord(BitAnd(WordAsBits(pa), BitmaskLow(12)));
            { lemma_Bitmask12(); }
            BitsAsWord(BitAnd(WordAsBits(pa), 0xfff));
        }
    }

    assert {:split_here} true;

    calc {
        PageBase(ptew);
        { reveal PageBase(); }
        BitwiseMaskHigh(ptew, 12);
        { reveal BitwiseMaskHigh(); }
        BitsAsWord(BitAnd(WordAsBits(ptew), BitmaskHigh(12)));
        { lemma_Bitmask12(); }
        BitsAsWord(BitAnd(pteb, 0xfffff000));
        BitsAsWord(BitAnd(BitOr(WordAsBits(pa), extrabits), 0xfffff000));
        {
            calc {
                BitAnd(BitOr(WordAsBits(pa), extrabits), 0xfffff000);
                { lemma_BitOrAndRelation(WordAsBits(pa), extrabits, 0xfffff000); }
                BitOr(BitAnd(WordAsBits(pa), 0xfffff000), BitAnd(extrabits, 0xfffff000));
                { assert BitAnd(extrabits, 0xfffff000) == 0 by { reveal_BitAnd(); } }
                BitOr(BitAnd(WordAsBits(pa), 0xfffff000), 0);
                { reveal BitOr(); }
                BitAnd(WordAsBits(pa), 0xfffff000);
                { assert BitAnd(WordAsBits(pa), 0xfff) == 0; reveal BitAnd(); }
                WordAsBits(pa);
            }
        }
        BitsAsWord(WordAsBits(pa));
        { lemma_WordAsBitsAsWord(pa); }
        pa;
    }

    assert {:split_here} true;

    assert BitAnd(pteb, 0x3) == 2 || BitAnd(pteb, 0x3) == 3 by {
        calc {
            BitAnd(pteb, 0x3);
            BitAnd(BitOr(WordAsBits(pa), extrabits), 0x3);
            { lemma_BitOrAndRelation(WordAsBits(pa), extrabits, 0x3); }
            BitOr(BitAnd(WordAsBits(pa), 0x3), BitAnd(extrabits, 0x3));
            { calc {
                BitAnd(WordAsBits(pa), 0x3);
                { lemma_ARM_L2PTE_PageMask(WordAsBits(pa)); }
                0;
            } }
            BitOr(0, BitAnd(extrabits, 0x3));
            { reveal BitOr(); }
            BitAnd(extrabits, 0x3);
        }
        reveal BitAnd();
    }

    assert {:split_here} true;

    assert BitAnd(pteb, 0xdfc) == ARM_L2PTE_CONST_BITS by {
        calc {
            BitAnd(pteb, 0xdfc);
            BitAnd(BitOr(WordAsBits(pa), extrabits), 0xdfc);
            { lemma_BitOrAndRelation(WordAsBits(pa), extrabits, 0xdfc); }
            BitOr(BitAnd(WordAsBits(pa), 0xdfc), BitAnd(extrabits, 0xdfc));
            { calc {
                BitAnd(WordAsBits(pa), 0xdfc);
                { lemma_ARM_L2PTE_PageMask(WordAsBits(pa)); }
                0;
            } }
            BitOr(0, BitAnd(extrabits, 0xdfc));
            { reveal BitOr(); }
            BitAnd(extrabits, 0xdfc);
            { reveal BitAnd(); }
            ARM_L2PTE_CONST_BITS;
        }
    }
}

lemma lemma_ARM_L2PTE(pa: word, w: bool, x: bool)
    requires PageAligned(pa) && isUInt32(pa + PhysBase())
    ensures ValidAbsL2PTEWord(ARM_L2PTE(pa, w, x))
    ensures ExtractAbsL2PTE(ARM_L2PTE(pa, w, x)) == Just(AbsPTE(pa, w, x))
{
    var ptew := ARM_L2PTE(pa, w, x);
    var nxbit:bv32 := if x then 0 else ARM_L2PTE_NX_BIT;
    var robit:bv32 := if w then 0 else ARM_L2PTE_RO_BIT;
    var extrabits := BitOr(BitOr(0x7e, nxbit), robit);
    var pteb := BitOr(WordAsBits(pa), extrabits);

    lemma_ARM_L2PTE_helper(pa, w, x, ptew, nxbit, robit, extrabits, pteb);
    lemma_WordBitEquiv(ptew, pteb);

    assert x == (BitAnd(pteb, ARM_L2PTE_NX_BIT) == 0) by {
        calc {
            BitAnd(pteb, ARM_L2PTE_NX_BIT);
            BitAnd(BitOr(WordAsBits(pa), extrabits), 1);
            { lemma_BitOrAndRelation(WordAsBits(pa), extrabits, 1); }
            BitOr(BitAnd(WordAsBits(pa), 1), BitAnd(extrabits, 1));
            { /* XXX: for inexplicable Z3 reasons, this step is
               * extremely prone to timeouts. There's something
               * horribly expensive about the number 1! */
              calc {
                BitAnd(WordAsBits(pa), 1);
                { lemma_ARM_L2PTE_PageMask(WordAsBits(pa)); }
                0;
            } }
            BitOr(0, BitAnd(extrabits, 1));
            { reveal BitOr(); }
            BitAnd(extrabits, 1);
            { reveal BitAnd(); }
            nxbit;
        }
    }

    assert {:split_here} true;

    assert w == (BitAnd(pteb, ARM_L2PTE_RO_BIT) == 0) by {
        calc {
            BitAnd(pteb, ARM_L2PTE_RO_BIT);
            BitAnd(BitOr(WordAsBits(pa), extrabits), 0x200);
            { lemma_BitOrAndRelation(WordAsBits(pa), extrabits, 0x200); }
            BitOr(BitAnd(WordAsBits(pa), 0x200), BitAnd(extrabits, 0x200));
            { calc {
                BitAnd(WordAsBits(pa), 0x200);
                { lemma_ARM_L2PTE_PageMask(WordAsBits(pa)); }
                0;
            } }
            BitOr(0, BitAnd(extrabits, 0x200));
            { reveal BitOr(); }
            BitAnd(extrabits, 0x200);
            { reveal BitAnd(); }
            robit;
        }
    }

    assert {:split_here} true;

    assert ValidAbsL2PTEWord(ARM_L2PTE(pa, w, x));
    assert ExtractAbsL2PTE(ARM_L2PTE(pa, w, x)) == Just(AbsPTE(pa, w, x));
}

lemma lemma_l1ptesmatch(e: Maybe<PageNr>, subpage:int)
    requires 0 <= subpage < 4
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    ensures ValidAbsL1PTEWord(mkL1Pte(e, subpage))
    ensures ExtractAbsL1PTE(mkL1Pte(e, subpage)) == mkAbsL1PTE(e, subpage)
{
    var ptew := mkL1Pte(e, subpage);
    var pteb := WordAsBits(ptew);
    lemma_WordBitEquiv(ptew, pteb);

    assert WordAsBits(0x3fc) == 0x3fc && WordAsBits(0x3) == 0x3
        && WordAsBits(ARM_L2PTABLE_BYTES) == 0x400
        && WordAsBits(0x3ff) == 0x3ff && WordAsBits(3) == 3
        && WordAsBits(8) == 8 && WordAsBits(9) == 9
        && WordAsBits(1) == 1 by { reveal_WordAsBits(); }

    match e
    case Just(pg) => {
        var pa := page_paddr(pg) + subpage * ARM_L2PTABLE_BYTES;
        assert pa % ARM_L2PTABLE_BYTES == 0;
        assert ptew == ARM_L1PTE(pa);

        calc {
            BitAnd(pteb, 0x3ff);
            BitAnd(WordAsBits(ARM_L1PTE(pa)), 0x3ff);
            { lemma_BitsAndWordConversions(); }
            BitAnd(BitOr(WordAsBits(pa), 9), 0x3ff);
            { lemma_BitOrAndRelation(WordAsBits(pa), 9, 0x3ff); }
            BitOr(BitAnd(WordAsBits(pa), 0x3ff), BitAnd(9, 0x3ff));
            {
                assert BitAnd(9, 0x3ff) == 9 by { reveal BitAnd(); }
                assert BitAnd(WordAsBits(pa), 0x3ff) == 0
                by {
                    assert pa % ARM_L2PTABLE_BYTES == 0;
                    lemma_BitModEquiv(pa, ARM_L2PTABLE_BYTES);
                    //assert WordAsBits(pa) % 0x400 == 0;
                    reveal BitAnd(); reveal BitMod();
                }
            }
            BitOr(0, 9);
            { reveal BitOr(); }
            9;
        }

        assert BitAnd(pteb, 0x3fc) == 8 by { reveal BitAnd(); }
        assert BitAnd(pteb, 0x3) == 1 by { reveal BitAnd(); }
        assert BitwiseAnd(ptew, 0x3) == 1
            by { lemma_BitsAndWordConversions(); }
        
        assert BitAnd(pteb, ARM_L1PTE_CONST_MASK) == ARM_L1PTE_CONST_BITS
            by { reveal BitAnd(); }

        calc {
            BitwiseMaskHigh(ptew, 10);
            { reveal BitwiseMaskHigh(); }
            BitsAsWord(BitAnd(WordAsBits(ptew), BitmaskHigh(10)));
            { calc {
                BitAnd(WordAsBits(ptew), BitmaskHigh(10));
                { lemma_Bitmask10(); }
                BitAnd(pteb, 0xfffffc00);
                BitAnd(WordAsBits(ARM_L1PTE(pa)), 0xfffffc00);
                BitAnd(WordAsBits(BitwiseOr(pa, 9)), 0xfffffc00);
                BitAnd(WordAsBits(BitsAsWord(BitOr(WordAsBits(pa), 9))),
                    0xfffffc00);
                { lemma_BitsAsWordAsBits(BitOr(WordAsBits(pa), 9)); }
                BitAnd(BitOr(WordAsBits(pa), 9), 0xfffffc00);
                BitAnd(BitOr(WordAsBits(pa), 9), 0xfffffc00);
                { lemma_BitOrAndRelation(WordAsBits(pa), 9, 0xfffffc00); }
                BitOr(BitAnd(WordAsBits(pa), 0xfffffc00), BitAnd(9, 0xfffffc00));
                { reveal BitAnd(); }
                BitOr(BitAnd(WordAsBits(pa), 0xfffffc00), 0);
                { reveal BitOr(); }
                BitAnd(WordAsBits(pa), 0xfffffc00);
                { calc {
                    BitsAsWord(BitAnd(WordAsBits(pa), 0x3ff));
                    { lemma_Bitmask10(); }
                    BitsAsWord(BitAnd(WordAsBits(pa), BitmaskLow(10)));
                    { reveal BitwiseMaskLow(); }
                    BitwiseMaskLow(pa, 10);
                    0;
                } assert BitAnd(WordAsBits(pa), 0x3ff) == 0; reveal BitAnd(); }
                WordAsBits(pa);
            } }
            BitsAsWord(WordAsBits(pa));
            { lemma_WordAsBitsAsWord(pa); }
            pa;
        }
    }
    case Nothing => {
        assert ptew == 0; reveal BitAnd();
    }
}

function nonexec_mapping(mapping: Mapping): Mapping
{
    mapping.(perm := mapping.perm.(x := false))
}

function method NOT_KOM_MAPPING_X(): word
    ensures NOT_KOM_MAPPING_X() == BitwiseNot(KOM_MAPPING_X)
    ensures NOT_KOM_MAPPING_X() == BitsAsWord(0xfffffffb)
{
    assert 0xfffffffb == BitsAsWord(0xfffffffb) by { reveal_BitsAsWord(); }
    assert WordAsBits(KOM_MAPPING_X) == 4 by { reveal_WordAsBits(); }
    reveal BitNot();
    0xfffffffb
}

lemma lemma_nonexec_mapping(mapping: Mapping, x: word)
    requires mapping == wordToMapping(x)
    ensures wordToMapping(BitwiseAnd(x, NOT_KOM_MAPPING_X()))
                == nonexec_mapping(mapping)
{
    var y := BitwiseAnd(x, NOT_KOM_MAPPING_X());
    lemma_WordBitEquiv(NOT_KOM_MAPPING_X(), 0xfffffffb);
    var xb := WordAsBits(x);
    lemma_WordBitEquiv(x, xb);
    var yb := BitAnd(xb, 0xfffffffb);
    assert y == BitsAsWord(yb);
    lemma_WordBitEquiv(y, yb);
    lemma_BitsAsWordAsBits(yb);

    assert l1indexFromMapping(y) == l1indexFromMapping(x) by {
        assert RightShift(y,22) == RightShift(x,22) by {
            reveal BitAnd(); reveal_BitShiftRight();
        }
    }

    assert l2indexFromMapping(y) == l2indexFromMapping(x) by {
        assert RightShift(y,12) == RightShift(x,12) by {
            reveal BitAnd(); reveal_BitShiftRight();
        }
    }

    assert permFromMapping(y) == permFromMapping(x).(x := false) by {
        assert WordAsBits(KOM_MAPPING_R) == 1 && WordAsBits(KOM_MAPPING_W) == 2
            && WordAsBits(KOM_MAPPING_X) == 4 by { reveal_WordAsBits(); }

        calc {
            BitwiseAnd(y, KOM_MAPPING_R);
            BitsAsWord(BitAnd(yb, 1));
            BitsAsWord(BitAnd(BitAnd(xb, 0xfffffffb), 1));
            { lemma_BitAndAssociative(xb, 0xfffffffb, 1); }
            BitsAsWord(BitAnd(xb, BitAnd(0xfffffffb, 1)));
            { assert BitAnd(0xfffffffb, 1) == 1 by { reveal_BitAnd(); } }
            BitsAsWord(BitAnd(xb, 1));
            BitwiseAnd(x, KOM_MAPPING_R);
        }

        calc {
            BitwiseAnd(y, KOM_MAPPING_W);
            BitsAsWord(BitAnd(yb, 2));
            BitsAsWord(BitAnd(BitAnd(xb, 0xfffffffb), 2));
            { lemma_BitAndAssociative(xb, 0xfffffffb, 2); }
            BitsAsWord(BitAnd(xb, BitAnd(0xfffffffb, 2)));
            { assert BitAnd(0xfffffffb, 2) == 2 by { reveal_BitAnd(); } }
            BitsAsWord(BitAnd(xb, 2));
            BitwiseAnd(x, KOM_MAPPING_W);
        }

        calc {
            BitwiseAnd(y, KOM_MAPPING_X);
            BitsAsWord(BitAnd(yb, 4));
            BitsAsWord(BitAnd(BitAnd(xb, 0xfffffffb), 4));
            { lemma_BitAndAssociative(xb, 0xfffffffb, 4); }
            BitsAsWord(BitAnd(xb, BitAnd(0xfffffffb, 4)));
            { assert BitAnd(0xfffffffb, 4) == 0 by { reveal_BitAnd(); } }
            BitsAsWord(BitAnd(xb, 0));
            { reveal BitAnd(); }
            0;
        }
    }

    assert wordToMapping(y) == nonexec_mapping(mapping) by { reveal_wordToMapping(); }
}

lemma lemma_BitOrNineIsLikePlus'(b: bv32)
    requires BitMod(b, 0x10) == 0
    ensures BitAdd(b, 9) == BitOr(b, 9)
{
    reveal BitMod();
    reveal BitOr();
    reveal BitAdd();
}

lemma lemma_BitOrNineIsLikePlus(i: word)
    requires i < 0xffffffff
    requires i % 0x10 == 0
    ensures i + 9 == BitwiseOr(i, 9)
{
    var b := WordAsBits(i);
    reveal WordAsBits();
    reveal BitsAsWord();
    lemma_BitModEquiv(i, 0x10);
    lemma_BitOrNineIsLikePlus'(b);
    lemma_BitAddEquiv(i, 9);
}

lemma lemma_ARM_L1PTE_Dual(paddr: word)
    requires paddr % ARM_L2PTABLE_BYTES == 0
    ensures ARM_L1PTE(paddr) == paddr + 9
{
    calc {
        paddr % 0x400 == 0;
        paddr % 0x10 == 0;
    }
    assert {:split_here} true;
    lemma_BitOrNineIsLikePlus(paddr);
}

function mkAbsL1PTE(e: Maybe<PageNr>, subpage:int): Maybe<addr>
    requires 0 <= subpage < 4
{
    match e
        case Nothing => Nothing
        case Just(pgNr) =>
            Just(page_paddr(pgNr) + subpage * ARM_L2PTABLE_BYTES)
}
