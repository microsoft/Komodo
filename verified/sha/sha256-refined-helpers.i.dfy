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

}
