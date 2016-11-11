include "sha256.s.dfy"
include "../bitvectors.i.dfy"

module bit_vector_lemmas_i {
import opened bit_vector_lemmas_i_sha256_s = sha256_s
import opened bit_vector_lemmas_i_bitvectors_i = bitvectors_i

lemma  lemma_Maj(x:word, y:word, z:word, result:word)
    requires result == BitwiseXor(BitwiseAnd(BitwiseXor(y, z), BitwiseXor(x, y)), y);
    ensures  result == Maj(x, y, z);
{
    reveal_Maj();
    reveal_BitXor();
    reveal_BitAnd();
    lemma_BitsAndWordConversions();
}

lemma lemma_Ch(x:word, y:word, z:word, result:word)
    requires result == BitwiseXor(BitwiseAnd(BitwiseXor(y, z), x), z);
    ensures  result == Ch(x, y, z);
{
    reveal_Ch();
    reveal_BitNot();
    reveal_BitXor();
    reveal_BitAnd();
    lemma_BitsAndWordConversions();
}

lemma lemma_RotateRightCommutesXorSpecific(x:word, y:word, a:shift_amount)
    ensures RotateRight(BitwiseXor(x, y), a) == BitwiseXor(RotateRight(x, a), RotateRight(y, a));
{
    reveal_BitXor();
    reveal_BitRotateRight();
    lemma_BitsAndWordConversions();
}

lemma lemma_RotateRightAddsBvConst(x:bv32)
    ensures  (x.RotateRight(2)).RotateRight(3) == x.RotateRight(5);
{
}

lemma lemma_RotateRightAddsBv(x:bv32, a0:shift_amount, a1:shift_amount)
    requires a0 - a1 >= 0;
    ensures  (x.RotateRight(a0 - a1)).RotateRight(a1) == x.RotateRight(a0);
{
}

function RotateRightBv(x:bv32, a:bv32) : bv32

lemma {:axiom} RotateRightBvAdds(x:bv32, a0:bv32, a1:bv32)
    ensures RotateRightBv(RotateRightBv(x, a0), a1) == RotateRightBv(x, a0 + a1);

function RotateRight'(x:word, a:shift_amount) : word 
{
    RotateRightBv(x as bv32, a as bv32) as word
}
        
lemma lemma_Foo(x:word, a0:shift_amount, a1:shift_amount)
    requires a0 - a1 >= 0;
    ensures  RotateRight'(RotateRight'(x, a0 - a1), a1) == RotateRight'(x, a0);
{
    reveal_BitRotateRight();
    lemma_BitsAndWordConversions();
    lemma_BitAddEquiv(a0, a1);
    lemma_BitSubEquiv(a0, a1);
    RotateRightBvAdds(x as bv32, a0 as bv32, a1 as bv32);
}


//lemma lemma_RotateRightAddsBv(x:bv32, a0:shift_amount, a1:shift_amount)
//    requires a0 - a1 >= 0;
//    ensures  (x.RotateRight(a0 - a1)).RotateRight(a1) == x.RotateRight(a0);
//{
//    lemma_BitsAndWordConversions();
//    lemma_BitAddEquiv(a0, a1);
//    lemma_BitSubEquiv(a0, a1);
//}

lemma lemma_RotateRightAdds(x:word, a0:shift_amount, a1:shift_amount)
    requires a0 - a1 >= 0;
    //ensures  RotateRight(RotateRight(x, a0), a1) == RotateRight(x, a0 + a1);
    ensures  RotateRight(RotateRight(x, a0 - a1), a1) == RotateRight(x, a0);
{
    reveal_BitRotateRight();
    lemma_BitsAndWordConversions();
    lemma_BitAddEquiv(a0, a1);
    lemma_BitSubEquiv(a0, a1);
}
lemma lemma_RotateRightAdds'(x:word, a0:shift_amount, a1:shift_amount)
    requires a0 + a1 < 32;
    ensures  RotateRight(RotateRight(x, a0), a1) == RotateRight(x, a0 + a1);
{
    reveal_BitRotateRight();
    lemma_BitsAndWordConversions();
    lemma_BitAddEquiv(a0, a1);
}

// Used for BSIG calculations
lemma lemma_BSIGOptimization(x:word, amt_0:shift_amount, amt_1:shift_amount, amt_2:shift_amount)
    requires amt_1 - amt_0 >= 0 && amt_2-amt_0 >= 0;
    ensures RotateRight(BitwiseXor(BitwiseXor(x, RotateRight(x, amt_1-amt_0)), RotateRight(x, amt_2-amt_0)), amt_0)
         == BitwiseXor(BitwiseXor(RotateRight(x, amt_0), RotateRight(x, amt_1)), 
                       RotateRight(x, amt_2));
{
//    assume false;
//    reveal_BitXor();
//    reveal_BitRotateRight();
//    lemma_BitsAndWordConversions();

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
        reveal_BitXor();
        lemma_BitsAndWordConversions();
    }
}

}
