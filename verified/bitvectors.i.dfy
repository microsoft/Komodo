include "bitvectors.s.dfy"
include "ARMdef.dfy"

lemma lemma_BitPos12()
    ensures BitsAsWord(BitAtPos(12)) == 0x1000
{
    lemma_pow2_properties(12);
}

lemma lemma_BitOrOneIsLikePlus'(b: bv32)
    requires BitMod(b, 2) == 0
    ensures BitAdd(b, 1) == BitOr(b, 1)
{
    reveal_BitMod();
    reveal_BitOr();
    reveal_BitAdd();
}

lemma lemma_BitOrOneIsLikePlus(i: word)
    requires i < 0xffffffff
    requires i % 2 == 0
    ensures i + 1 == BitwiseOr(i, 1)
{
    var b := WordAsBits(i);
    reveal_WordAsBits();
    reveal_BitsAsWord();
    lemma_BitModEquiv(i, 2);
    lemma_BitOrOneIsLikePlus'(b);
    lemma_BitAddEquiv(i, 1);
}

lemma lemma_BitShift1(x: bv32)
    requires x < 0x80000000
    ensures BitShiftLeft(x, 1) == BitMul(x, 2)
{
    calc {
        BitShiftLeft(x, 1);
        { reveal_BitShiftLeft(); }
        x << 1;
        x * 2;
        { reveal_BitMul(); }
        BitMul(x, 2);
    }
}

lemma lemma_LeftShift1(x: word)
    requires x < 0x80000000
    ensures LeftShift(x, 1) == x * 2
{
    calc {
        LeftShift(x, 1);
        BitsAsWord(BitShiftLeft(WordAsBits(x), 1));
        { lemma_BitCmpEquiv(x, 0x80000000);
          assert WordAsBits(0x80000000) == 0x80000000 by { reveal_WordAsBits(); }
          lemma_BitShift1(WordAsBits(x)); }
        BitsAsWord(BitMul(WordAsBits(x), 2));
        { assert WordAsBits(2) == 2 by { reveal_WordAsBits(); } }
        BitsAsWord(BitMul(WordAsBits(x), WordAsBits(2)));
        { lemma_BitMulEquiv(x, 2); }
        x * 2;
    }
}

lemma lemma_LeftShiftsAdd(x: word, a: nat, b: nat)
    requires 0 <= a + b < 32
    ensures LeftShift(x, a + b) == LeftShift(LeftShift(x, a), b)
{
    calc {
        LeftShift(x, a + b);
        BitsAsWord(BitShiftLeft(WordAsBits(x), (a + b)));
        { lemma_BitShiftsSum(WordAsBits(x), a, b); }
        BitsAsWord(BitShiftLeft(BitShiftLeft(WordAsBits(x), a), b));
        { lemma_BitsAsWordAsBits(BitShiftLeft(WordAsBits(x), a)); }
        BitsAsWord(BitShiftLeft(WordAsBits(BitsAsWord(BitShiftLeft(WordAsBits(x), a))), b));
        BitsAsWord(BitShiftLeft(WordAsBits(LeftShift(x, a)), b));
        LeftShift(LeftShift(x, a), b);
    }
}

lemma lemma_LeftShift2(x: word)
    requires x < 0x40000000
    ensures LeftShift(x, 2) == x * 4
{
    var x' := LeftShift(x, 1);
    lemma_LeftShift1(x);
    lemma_LeftShift1(x');
    lemma_LeftShiftsAdd(x, 1, 1);
}

lemma lemma_LeftShift4(x: word)
    requires x < 0x10000000
    ensures LeftShift(x, 4) == x * 16
{
    var x' := LeftShift(x, 2);
    lemma_LeftShift2(x);
    lemma_LeftShift2(x');
    lemma_LeftShiftsAdd(x, 2, 2);
}

lemma lemma_LeftShift12(x: word)
    requires x < 0x100000
    ensures LeftShift(x, 12) == x * 4096
{
    var x' := LeftShift(x, 4);
    lemma_LeftShift4(x);
    var x'' := LeftShift(x', 4);
    lemma_LeftShift4(x');
    lemma_LeftShiftsAdd(x, 4, 4);
    assert x'' == LeftShift(x, 8);
    assert x'' == x * 256;
    var x''' := LeftShift(x'', 4);
    lemma_LeftShift4(x'');
    assert x''' == x * 4096;
    lemma_LeftShiftsAdd(x, 8, 4);
    assert x''' == LeftShift(x, 12);
}

function {:opaque} BitwiseMaskLow(i:word, bitpos:int): word
    requires 0 <= bitpos < 32;
    ensures BitwiseMaskLow(i, bitpos) == i % pow2(bitpos)
    ensures pow2_properties(bitpos)
{
    lemma_BitmaskAsWord(i, bitpos);
    lemma_pow2_properties(bitpos);
    BitsAsWord(BitAnd(WordAsBits(i), BitmaskLow(bitpos)))
}

lemma lemma_Bitmask12()
    ensures BitmaskLow(12) == 0xfff
    ensures BitmaskHigh(12) == 0xfffff000
{
    calc {
        BitmaskLow(12);
        BitAtPos(12) - 1;
        { lemma_BitsAsWordAsBits(BitAtPos(12)); }
        WordAsBits(BitsAsWord(BitAtPos(12))) - 1;
        WordAsBits(pow2(12)) - 1;
        { lemma_pow2_properties(12); }
        WordAsBits(0x1000) - 1;
        { assert WordAsBits(0x1000) == 0x1000 by { reveal_WordAsBits(); }
          lemma_BitSubEquiv(0x1000, 1); }
        0xfff;
    }

    calc {
        BitmaskHigh(12);
        BitNot(BitmaskLow(12));
        BitNot(0xfff);
        { reveal_BitNot(); }
        0xfffff000;
    }
}

lemma lemma_Bitmask10()
    ensures BitmaskLow(10) == 0x3ff
    ensures BitmaskHigh(10) == 0xfffffc00
{
    calc {
        BitmaskLow(10);
        BitAtPos(10) - 1;
        { lemma_BitsAsWordAsBits(BitAtPos(10)); }
        WordAsBits(BitsAsWord(BitAtPos(10))) - 1;
        WordAsBits(pow2(10)) - 1;
        { lemma_pow2_properties(10); }
        WordAsBits(0x400) - 1;
        { assert WordAsBits(0x400) == 0x400 by { reveal_WordAsBits(); }
          lemma_BitSubEquiv(0x400, 1); }
        0x3ff;
    }

    calc {
        BitmaskHigh(10);
        BitNot(BitmaskLow(10));
        BitNot(0x3ff);
        { reveal_BitNot(); }
        0xfffffc00;
    }
}
