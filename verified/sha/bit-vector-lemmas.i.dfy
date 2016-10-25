include "sha256.s.dfy"

lemma {:axiom} lemma_BitsAndWordConversions()
    ensures forall w:word :: BitsAsWord(WordAsBits(w)) == w;
    ensures forall b:bv32 :: WordAsBits(BitsAsWord(b)) == b;


lemma  lemma_Maj(x:word, y:word, z:word, result:word)
    requires result == BitwiseXor(BitwiseAnd(BitwiseXor(y, z), BitwiseXor(x, y)), y);
    ensures  result == Maj(x, y, z);
{
    reveal_Maj();
    reveal_BitXor();
    reveal_BitAnd();
    lemma_BitsAndWordConversions();
    
//    var x_xor_y := WordAsBits(x) ^ WordAsBits(y);
//    var y_xor_z := WordAsBits(y) ^ WordAsBits(z);
//    calc {
//        BitwiseAnd(BitwiseXor(y, z), BitwiseXor(x, y));
//        BitsAsWord(BitAnd(WordAsBits(BitwiseXor(y, z)), WordAsBits(BitwiseXor(x, y))));
//        BitsAsWord(BitAnd(y_xor_z, x_xor_y));
//    }
//
//    var and_y_xor_z_x_xor_y := BitsAsWord(BitAnd(y_xor_z, x_xor_y));
//
//    calc {
//        BitwiseXor(BitwiseAnd(BitwiseXor(y, z), BitwiseXor(x, y)), y);
//        BitwiseXor(and_y_xor_z_x_xor_y, y);
//        BitsAsWord(BitXor(WordAsBits(and_y_xor_z_x_xor_y), WordAsBits(y)));
//            { assert WordAsBits(and_y_xor_z_x_xor_y) == BitAnd(y_xor_z, x_xor_y); }
//        BitsAsWord(BitXor(BitAnd(y_xor_z, x_xor_y), WordAsBits(y)));
//    }
//    assume false;

//    var x_xor_y := WordAsBits(x) ^ WordAsBits(y);
//    var y_xor_z := WordAsBits(y) ^ WordAsBits(z);
//    calc {
//        BitwiseXor(y, z);
//        BitsAsWord(BitXor(WordAsBits(y), WordAsBits(z)));
//            { reveal_BitXor(); }
//        BitsAsWord(WordAsBits(y) ^ WordAsBits(z));
//            { assert WordAsBits(y) ^ WordAsBits(z) == y_xor_z; }
//        BitsAsWord(y_xor_z);
//    }
//    calc {
//        BitwiseXor(x, y);
//        BitsAsWord(BitXor(WordAsBits(x), WordAsBits(y)));
//            { reveal_BitXor(); }
//        BitsAsWord(WordAsBits(x) ^ WordAsBits(y));
//            { assert WordAsBits(x) ^ WordAsBits(y) == x_xor_y; }
//        BitsAsWord(x_xor_y);
//    }
//
//    calc {
//        BitwiseAnd(BitwiseXor(y, z), BitwiseXor(x, y));
//        BitsAsWord(BitAnd(WordAsBits(BitwiseXor(y, z)), WordAsBits(BitwiseXor(x, y))));
//            { lemma_BitsAsWordAsBits(x_xor_y); lemma_BitsAsWordAsBits(y_xor_z); }
//        BitsAsWord(BitAnd(y_xor_z, x_xor_y));
//
//    }
//    assume false;
//    reveal_BitsAsWord();
//    reveal_WordAsBits();
//    reveal_BitXor();
//    reveal_BitAnd();
}

lemma lemma_Maj_bv32(x:bv32, y:bv32, z:bv32, result:bv32)
    requires result == ((y ^ z) & (x ^ y)) ^ y;
    ensures  result == (x & y) ^ (x & z) ^ (y & z);
{
}
