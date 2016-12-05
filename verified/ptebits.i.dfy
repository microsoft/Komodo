include "pagedb.i.dfy"
include "bitvectors.i.dfy"

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

    assert extrabits == (
        if x && w then 0xd76
        else if x && !w then 0xf76
        else if !x && w then 0xd77
        else 0xf77) by { reveal_BitOr(); }

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
        reveal_BitAnd();
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

    assert ValidAbsL2PTEWord(ARM_L2PTE(pa, w, x));
    assert ExtractAbsL2PTE(ARM_L2PTE(pa, w, x)) == Just(AbsPTE(pa, w, x));
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
            BitsAsWord(BitAnd(pteb, 0x3ff));
            BitsAsWord(BitAnd(WordAsBits(ptew), 0x3ff));
            { lemma_Bitmask10(); }
            BitsAsWord(BitAnd(WordAsBits(ptew), BitmaskLow(10)));
            { reveal_BitwiseMaskLow(); }
            BitwiseMaskLow(ptew, 10);
            BitwiseMaskLow(ARM_L1PTE(pa), 10);
            BitwiseMaskLow(BitwiseOr(pa, 1), 10);
            { lemma_BitOrOneIsLikePlus(pa); }
            BitwiseMaskLow(pa + 1, 10);
            (pa + 1) % 0x400;
            1;
        }
        calc {
            BitAnd(pteb, 0x3ff);
            { lemma_BitsAsWordAsBits(BitAnd(pteb, 0x3ff)); }
            WordAsBits(BitsAsWord(BitAnd(pteb, 0x3ff)));
            1;
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

function nonexec_mapping(mapping: Mapping): Mapping
{
    mapping.(perm := mapping.perm.(x := false))
}

function method NOT_KOM_MAPPING_X(): word
    ensures NOT_KOM_MAPPING_X() == BitwiseNot(KOM_MAPPING_X())
    ensures NOT_KOM_MAPPING_X() == BitsAsWord(0xfffffffb)
{
    assert 0xfffffffb == BitsAsWord(0xfffffffb) by { reveal_BitsAsWord(); }
    assert WordAsBits(KOM_MAPPING_X()) == 4 by { reveal_WordAsBits(); }
    reveal_BitNot();
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
        assert RightShift(y,20) == RightShift(x,20) by {
            reveal_BitAnd(); reveal_BitShiftRight();
        }
    }

    assert l2indexFromMapping(y) == l2indexFromMapping(x) by {
        assert RightShift(y,12) == RightShift(x,12) by {
            reveal_BitAnd(); reveal_BitShiftRight();
        }
    }

    assert permFromMapping(y) == permFromMapping(x).(x := false) by {
        assert WordAsBits(KOM_MAPPING_R()) == 1 && WordAsBits(KOM_MAPPING_W()) == 2
            && WordAsBits(KOM_MAPPING_X()) == 4 by { reveal_WordAsBits(); }

        calc {
            BitwiseAnd(y, KOM_MAPPING_R());
            BitsAsWord(BitAnd(yb, 1));
            BitsAsWord(BitAnd(BitAnd(xb, 0xfffffffb), 1));
            { lemma_BitAndAssociative(xb, 0xfffffffb, 1); }
            BitsAsWord(BitAnd(xb, BitAnd(0xfffffffb, 1)));
            { assert BitAnd(0xfffffffb, 1) == 1 by { reveal_BitAnd(); } }
            BitsAsWord(BitAnd(xb, 1));
            BitwiseAnd(x, KOM_MAPPING_R());
        }

        calc {
            BitwiseAnd(y, KOM_MAPPING_W());
            BitsAsWord(BitAnd(yb, 2));
            BitsAsWord(BitAnd(BitAnd(xb, 0xfffffffb), 2));
            { lemma_BitAndAssociative(xb, 0xfffffffb, 2); }
            BitsAsWord(BitAnd(xb, BitAnd(0xfffffffb, 2)));
            { assert BitAnd(0xfffffffb, 2) == 2 by { reveal_BitAnd(); } }
            BitsAsWord(BitAnd(xb, 2));
            BitwiseAnd(x, KOM_MAPPING_W());
        }

        calc {
            BitwiseAnd(y, KOM_MAPPING_X());
            BitsAsWord(BitAnd(yb, 4));
            BitsAsWord(BitAnd(BitAnd(xb, 0xfffffffb), 4));
            { lemma_BitAndAssociative(xb, 0xfffffffb, 4); }
            BitsAsWord(BitAnd(xb, BitAnd(0xfffffffb, 4)));
            { assert BitAnd(0xfffffffb, 4) == 0 by { reveal_BitAnd(); } }
            BitsAsWord(BitAnd(xb, 0));
            { reveal_BitAnd(); }
            0;
        }
    }

    assert wordToMapping(y) == nonexec_mapping(mapping) by { reveal_wordToMapping(); }
}

lemma lemma_ARM_L1PTE_Dual(paddr: word)
    requires paddr % ARM_L2PTABLE_BYTES() == 0
    ensures ARM_L1PTE(paddr) == paddr + 1
{
    assert paddr % 0x400 == 0 && paddr % 2 == 0;
    lemma_BitOrOneIsLikePlus(paddr);
}

function mkAbsL1PTE(e: Maybe<PageNr>, subpage:int): Maybe<addr>
    requires 0 <= subpage < 4
{
    match e
        case Nothing => Nothing
        case Just(pgNr) =>
            Just(page_paddr(pgNr) + subpage * ARM_L2PTABLE_BYTES())
}
