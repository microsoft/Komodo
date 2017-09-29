include "ARMdef.s.dfy"
include "bitvectors.i.dfy"
include "entry.i.dfy"

lemma lemma_scr_entry(pre: word, post: word)
    requires post == BitwiseOr(BitwiseAnd(pre, 0xfffffffe), 6)
    ensures decode_scr(post) == SCRT(Secure, true, true)
{
    assert WordAsBits(1) == 1 && WordAsBits(2) == 2 && WordAsBits(4) == 4
           && WordAsBits(6) == 6 && WordAsBits(0xfffffffe) == 0xfffffffe
        by { reveal WordAsBits(); }
    lemma_WordBitEquiv(1,1);

    calc {
        post;
        BitwiseOr(BitwiseAnd(pre, 0xfffffffe), 6);
        { lemma_BitsAndWordConversions(); }
        BitsAsWord(BitOr(BitAnd(WordAsBits(pre), 0xfffffffe), 6));
    }

    calc {
        BitwiseAnd(post, 1);
        { lemma_BitsAndWordConversions(); }
        BitsAsWord(BitAnd(BitOr(BitAnd(WordAsBits(pre), 0xfffffffe), 6), 1));
        { reveal BitAnd(); reveal_BitOr(); }
        BitsAsWord(0);
    }

    var x := BitAnd(WordAsBits(pre), 0xfffffffe);

    calc {
        BitwiseAnd(post, 2);
        { lemma_BitsAndWordConversions(); }
        BitsAsWord(BitAnd(BitOr(BitAnd(WordAsBits(pre), 0xfffffffe), 6), 2));
        BitsAsWord(BitAnd(BitOr(x, 6), 2));
        { lemma_BitOrAndRelation(x, 6, 2); }
        BitsAsWord(BitOr(BitAnd(x, 2), BitAnd(6, 2)));
        { reveal BitAnd(); }
        BitsAsWord(BitOr(BitAnd(x, 2), 2));
        != { reveal BitOr(); }
        BitsAsWord(0);
    }

    calc {
        BitwiseAnd(post, 4);
        { lemma_BitsAndWordConversions(); }
        BitsAsWord(BitAnd(BitOr(BitAnd(WordAsBits(pre), 0xfffffffe), 6), 4));
        BitsAsWord(BitAnd(BitOr(x, 6), 4));
        { lemma_BitOrAndRelation(x, 6, 4); }
        BitsAsWord(BitOr(BitAnd(x, 4), BitAnd(6, 4)));
        { reveal BitAnd(); }
        BitsAsWord(BitOr(BitAnd(x, 4), 4));
        != { reveal BitOr(); }
        BitsAsWord(0);
    }
}

lemma lemma_scr_exit(pre: word, post: word)
    requires post == BitwiseOr(BitwiseAnd(pre, 0xfffffff9), 1)
    ensures decode_scr(post) == SCRT(NotSecure, false, false)
{
    assert WordAsBits(1) == 1 && WordAsBits(2) == 2 && WordAsBits(4) == 4
           && WordAsBits(0xfffffff9) == 0xfffffff9
        by { reveal WordAsBits(); }
    lemma_WordBitEquiv(1,1);

    calc {
        post;
        BitwiseOr(BitwiseAnd(pre, 0xfffffff9), 1);
        { lemma_BitsAndWordConversions(); }
        BitsAsWord(BitOr(BitAnd(WordAsBits(pre), 0xfffffff9), 1));
    }

    calc {
        BitwiseAnd(post, 1);
        { lemma_BitsAndWordConversions(); }
        BitsAsWord(BitAnd(BitOr(BitAnd(WordAsBits(pre), 0xfffffff9), 1), 1));
        { reveal BitAnd(); reveal_BitOr(); }
        BitsAsWord(1);
    }

    calc {
        BitwiseAnd(post, 2);
        { lemma_BitsAndWordConversions(); }
        BitsAsWord(BitAnd(BitOr(BitAnd(WordAsBits(pre), 0xfffffff9), 1), 2));
        { reveal BitAnd(); reveal_BitOr(); }
        BitsAsWord(0);
    }

    calc {
        BitwiseAnd(post, 4);
        { lemma_BitsAndWordConversions(); }
        BitsAsWord(BitAnd(BitOr(BitAnd(WordAsBits(pre), 0xfffffff9), 1), 4));
        { reveal BitAnd(); reveal_BitOr(); }
        BitsAsWord(0);
    }
}

lemma lemma_sp_bit_helper1(x:word, y:word)
    requires OpaqueEven(x)
    requires y == x || y == BitwiseOr(x, 1)
    requires BitwiseAnd(y, 1) == 0
    ensures x == y
{
    assert BitsAsWord(1) == 1 by { reveal BitsAsWord(); }
    lemma_BitsAndWordConversions();
    reveal BitAnd();
    reveal BitOr();
}

lemma lemma_sp_bit_helper(x:word, y:word)
    requires OpaqueEven(x)
    requires y == x || y == BitwiseOr(x, 1)
    requires BitwiseAnd(y, 1) != 0
    ensures y != x && BitwiseXor(y, 1) == x
{
    var xb := WordAsBits(x);
    var yb := WordAsBits(y);

    assert BitsAsWord(1) == 1 && BitsAsWord(2) == 2 by { reveal BitsAsWord(); }
    lemma_BitsAndWordConversions();

    assert BitAnd(yb, 1) == 1 by { reveal BitAnd(); }
    assert BitMod(xb, 2) == 0 by { reveal OpaqueEven(); lemma_BitModEquiv(x, 2); }
    assert BitAnd(xb, 1) == 0 by { reveal BitAnd(); reveal BitMod(); }
    assert yb != xb by { reveal BitAnd(); }
    assert yb == BitOr(xb, 1);
    assert BitAnd(BitXor(yb, 1), 1) == BitAnd(xb, 1) by { reveal BitXor(); reveal BitAnd(); }
    assert BitXor(yb, 1) == xb by { reveal BitXor(); reveal BitOr(); }
}
