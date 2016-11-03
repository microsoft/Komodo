include "../ARMspartan.dfy"
include "../words_and_bytes.s.dfy"
include "../kom_common.s.dfy"
include "../sha/sha256.i.dfy"
include "../sha/bit-vector-lemmas.i.dfy"
include "../ARMdecls.gen.dfy"

module sha256_refined_helpers_i {

import opened sha256_refined_helpers_i_ARMspartan = ARMspartan 
import opened sha256_refined_helpers_i_words_and_bytes_s = words_and_bytes_s 
import opened sha256_refined_helpers_i_kom_common_s = kom_common_s 
import opened sha256_refined_helpers_i_sha256_i = sha256_i
import opened sha256_refined_helpers_i_bit_vector_lemmas_i = bit_vector_lemmas_i
import opened sha256_refined_helpers_i_ARMdecls = ARMdecls 

predicate method Even(i:int) { i % 2 == 0 }

type perm_index = i | 0 <= i < 8
function method ApplyPerm(i:int, perm:perm_index) : int
{
    //if i + perm >= 8 then i + perm - 8 else i + perm
    if i - perm >= 0 then i - perm else i - perm + 8
}

lemma lemma_BitwiseAdd32Associates3'(x1:word, x2:word, x3:word)
    ensures BitwiseAdd32(BitwiseAdd32(x1, x2), x3) == BitwiseAdd32(x1, BitwiseAdd32(x2, x3));
{
}

lemma lemma_BitwiseAdd32Associates3(x1:word, x2:word, x3:word)
    ensures BitwiseAdd32(BitwiseAdd32(x1, x2), x3) == BitwiseAdd32(BitwiseAdd32(x1, x3), x2);
{
    calc {
        BitwiseAdd32(BitwiseAdd32(x1, x2), x3);
            { lemma_BitwiseAdd32Associates3'(x1, x2, x3); }
        BitwiseAdd32(x1, BitwiseAdd32(x2, x3));
        BitwiseAdd32(x1, BitwiseAdd32(x3, x2));
            { lemma_BitwiseAdd32Associates3'(x1, x3, x2); }
        BitwiseAdd32(BitwiseAdd32(x1, x3), x2);
    }
}

lemma lemma_BitwiseAdd32Associates5(x1:word, x2:word, x3:word, x4:word, x5:word, result:word)
    requires result == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x2), x3), x4), x5);
    ensures  result == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x5), x4), x2);
{
    calc {
        result;
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x2), x3), x4), x5);
            { lemma_BitwiseAdd32Associates3(x1, x2, x3); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x2), x4), x5);
            { lemma_BitwiseAdd32Associates3(BitwiseAdd32(x1, x3), x2, x4); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x4), x2), x5);
            { lemma_BitwiseAdd32Associates3(BitwiseAdd32(BitwiseAdd32(x1, x3), x4), x2, x5); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x4), x5), x2);
            { lemma_BitwiseAdd32Associates3(BitwiseAdd32(x1, x3), x4, x5); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x5), x4), x2);
    }
}

lemma lemma_BitwiseAdd32Associates4(x1:word, x2:word, x3:word, x4:word, result:word)
    requires result == BitwiseAdd32(BitwiseAdd32(x4, BitwiseAdd32(x1, x3)), x2);
    ensures  result == BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x2), x3), x4);
{
    calc {
        result ;
        BitwiseAdd32(BitwiseAdd32(x4, BitwiseAdd32(x1, x3)), x2);
            { assert BitwiseAdd32(BitwiseAdd32(x1, x3), x4) == BitwiseAdd32(x4, BitwiseAdd32(x1, x3)); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x4), x2);
            { lemma_BitwiseAdd32Associates3(BitwiseAdd32(x1, x3), x4, x2); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x3), x2), x4);
            { lemma_BitwiseAdd32Associates3(x1, x3, x2); }
        BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(x1, x2), x3), x4);
    }
}

lemma lemma_Even_properties(i:int)
    ensures Even(i) == !Even(i + 1);
{
}

lemma lemma_perm_properties(i:int, perm:perm_index)
    ensures 0 <= i < 8 ==> ApplyPerm(i, perm) == (i-perm)%8;
{
}

lemma lemma_perm_implications(i:int)
    ensures ApplyPerm(0, (i+1)%8) == ApplyPerm(7, i%8);
    ensures ApplyPerm(1, (i+1)%8) == ApplyPerm(0, i%8);
    ensures ApplyPerm(2, (i+1)%8) == ApplyPerm(1, i%8);
    ensures ApplyPerm(3, (i+1)%8) == ApplyPerm(2, i%8);
    ensures ApplyPerm(4, (i+1)%8) == ApplyPerm(3, i%8);
    ensures ApplyPerm(5, (i+1)%8) == ApplyPerm(4, i%8);
    ensures ApplyPerm(6, (i+1)%8) == ApplyPerm(5, i%8);
    ensures ApplyPerm(7, (i+1)%8) == ApplyPerm(6, i%8);
{
}

lemma lemma_obvious_WordAligned(i:int)
    requires WordAligned(i);
    ensures  WordAligned(i + 4);
{
}

lemma lemma_obvious_mod_with_constants(i:int)
    requires i == 64 || i == 16;
    ensures i % 8 == 0;
{
}

}
