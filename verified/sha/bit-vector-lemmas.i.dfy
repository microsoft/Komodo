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
