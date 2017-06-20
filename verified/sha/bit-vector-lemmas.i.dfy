include "sha256.s.dfy"
include "../bitvectors.i.dfy"

lemma  lemma_Maj(x:word, y:word, z:word, result:word)
    requires result == BitwiseXor(BitwiseAnd(BitwiseXor(y, z), BitwiseXor(x, y)), y);
    ensures  result == Maj(x, y, z);
{
    reveal Maj();
    reveal BitXor();
    reveal BitAnd();
    lemma_BitsAndWordConversions();
}

lemma lemma_Ch(x:word, y:word, z:word, result:word)
    requires result == BitwiseXor(BitwiseAnd(BitwiseXor(y, z), x), z);
    ensures  result == Ch(x, y, z);
{
    reveal Ch();
    reveal BitNot();
    reveal BitXor();
    reveal BitAnd();
    lemma_BitsAndWordConversions();
}

lemma lemma_RotateRightCommutesXorSpecific(x:word, y:word, a:shift_amount)
    ensures RotateRight(BitwiseXor(x, y), a) == BitwiseXor(RotateRight(x, a), RotateRight(y, a));
{
    reveal BitXor();
    reveal BitRotateRight();
    lemma_BitsAndWordConversions();
}

// TODO: Dafny's use of int2bv to convert the shift amount prevents this from working
lemma {:axiom} lemma_RotateRightAdds(x:word, a0:shift_amount, a1:shift_amount)
    requires a0 + a1 < 32;
    ensures  RotateRight(RotateRight(x, a0), a1) == RotateRight(x, a0 + a1);
//{
//    reveal BitRotateRight();
//    lemma_BitsAndWordConversions();
//    lemma_BitAddEquiv(a0, a1);
//}

// Used for BSIG calculations
lemma lemma_BSIGOptimization(x:word, amt_0:shift_amount, amt_1:shift_amount, amt_2:shift_amount)
    requires amt_1 - amt_0 >= 0 && amt_2-amt_0 >= 0;
    ensures RotateRight(BitwiseXor(BitwiseXor(x, RotateRight(x, amt_1-amt_0)), RotateRight(x, amt_2-amt_0)), amt_0)
         == BitwiseXor(BitwiseXor(RotateRight(x, amt_0), RotateRight(x, amt_1)), 
                       RotateRight(x, amt_2));
{
    calc {
        RotateRight(BitwiseXor(BitwiseXor(x, RotateRight(x, amt_1-amt_0)), RotateRight(x, amt_2-amt_0)), amt_0);
            { lemma_RotateRightCommutesXorSpecific(BitwiseXor(x, RotateRight(x, amt_1-amt_0)), RotateRight(x, amt_2-amt_0), amt_0); }
        BitwiseXor(RotateRight(BitwiseXor(x, RotateRight(x, amt_1-amt_0)), amt_0), RotateRight(RotateRight(x, amt_2-amt_0), amt_0));
            { lemma_RotateRightCommutesXorSpecific(x, RotateRight(x, amt_1-amt_0), amt_0); }
        BitwiseXor(BitwiseXor(RotateRight(x, amt_0), RotateRight(RotateRight(x, amt_1-amt_0), amt_0)), RotateRight(RotateRight(x, amt_2-amt_0), amt_0));
            { lemma_RotateRightAdds(x, amt_1-amt_0, amt_0); }
        BitwiseXor(BitwiseXor(RotateRight(x, amt_0), RotateRight(x, amt_1)), RotateRight(RotateRight(x, amt_2-amt_0), amt_0));
            { lemma_RotateRightAdds(x, amt_2-amt_0, amt_0); }
        BitwiseXor(BitwiseXor(RotateRight(x, amt_0), RotateRight(x, amt_1)), RotateRight(x, amt_2));
    }
}

lemma lemma_XorSelfIsZero()
    ensures forall x:word :: BitwiseXor(x, x) == 0;
{
    forall x:word 
        ensures BitwiseXor(x, x) == 0;
    {
        reveal BitXor();
        lemma_BitsAndWordConversions();
    }
}

lemma lemma_shift16maskhigh(x:bv32)
    requires 0 <= x <= 0xffffffff
    ensures (x >> 16) << 16 == x & 0xffff0000
{}

lemma lemma_masklow16(c:word)
    ensures BitwiseMaskLow(c % 0x10000, 16) == BitsAsWord(WordAsBits(c) & 0xffff)
{
    ghost var cb := WordAsBits(c);
    assert WordAsBits(0x10000) == 0x10000 by { reveal WordAsBits(); }
    calc {
        BitwiseMaskLow(c % 0x10000, 16);
        { reveal BitwiseMaskLow(); }
        BitsAsWord(BitAnd(WordAsBits(c % 0x10000), BitmaskLow(16)));
        { assert BitmaskLow(16) == 0xffff by { reveal BitAtPos(); } }
        BitsAsWord(BitAnd(WordAsBits(c % 0x10000), 0xffff));
        { lemma_BitModEquiv(c, 0x10000); }
        BitsAsWord(BitAnd(WordAsBits(BitsAsWord(BitMod(cb, 0x10000))), 0xffff));
        { lemma_BitsAsWordAsBits(BitMod(cb, 0x10000)); }
        BitsAsWord(BitAnd(BitMod(cb, 0x10000), 0xffff));
        { reveal BitAnd(); reveal BitMod(); }
        BitsAsWord(cb & 0xffff);
    }
}

lemma lemma_load_32_bit_const(c:word)
    ensures c == UpdateTopBits(c % 0x10000, BitsAsWord(WordAsBits(c) >> 16))
{
    ghost var bottom := c % 0x10000;
    ghost var cb := WordAsBits(c);
    ghost var top := BitsAsWord(cb >> 16);

    assert BitsAsWord(0x10000) == 0x10000 by { reveal BitsAsWord(); }
    lemma_WordBitEquiv(0x10000, 0x10000);

    calc {
        UpdateTopBits(bottom, top);
        { reveal UpdateTopBits(); }
        BitwiseOr(LeftShift(top, 16), BitwiseMaskLow(bottom, 16));
        { calc {
                LeftShift(top, 16);
                { reveal BitShiftLeft(); }
                BitsAsWord(WordAsBits(BitsAsWord(cb >> 16)) << 16);
                { lemma_BitsAsWordAsBits(cb >> 16); lemma_shift16maskhigh(cb); }
                BitsAsWord(cb & 0xffff0000);
        } }
        BitwiseOr(BitsAsWord(cb & 0xffff0000), BitwiseMaskLow(bottom, 16));
        { lemma_masklow16(c); }
        BitwiseOr(BitsAsWord(cb & 0xffff0000), BitsAsWord(cb & 0xffff));
        { lemma_BitsAndWordConversions(); }
        BitsAsWord(BitOr(cb & 0xffff0000, cb & 0xffff));
        { reveal BitOr(); }
        BitsAsWord(cb);
        { lemma_WordAsBitsAsWord(c); }
        c;
    }
}
