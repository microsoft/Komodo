include "sha256.s.dfy"

lemma lemma_BitsAndWordConversions()
    ensures forall w:word :: BitsAsWord(WordAsBits(w)) == w;
    ensures forall b:bv32 :: WordAsBits(BitsAsWord(b)) == b;
{
    forall w:word 
        ensures BitsAsWord(WordAsBits(w)) == w;
    {
        lemma_WordAsBitsAsWord(w);
    }
    forall b:bv32
        ensures WordAsBits(BitsAsWord(b)) == b;
    {
        lemma_BitsAsWordAsBits(b);
    }
}


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

// Used for BSIG calculations
lemma lemma_RotateRightCommutesXor(x:word, amt_0:word, amt_1:word, amt_2:word)
    ensures RotateRight(BitwiseXor(BitwiseXor(x, RotateRight(x, amt_1-amt_0)), RotateRight(x, amt_2-amt_0)), amt_0)
         == BitwiseXor(BitwiseXor(RotateRight(x, amt_0), RotateRight(x, amt_1)), 
                       RotateRight(x, amt_2));
// TODO: Waiting on Dafny to support RotateRight
//{
//    reveal_BitXor();
//    reveal_RotateRight();
//    lemma_BitsAndWordConversions();
//}
