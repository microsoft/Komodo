lemma {:axiom} lemma_MulModZero(a:int, b:int)
    requires b > 0
    ensures (a * b) % b == 0
/* FIXME: prove this! */

lemma lemma_DivMulLessThan(a:int, b:int)
    requires b > 0
    ensures (a / b) * b <= a
{}
