include "nlarith.s.dfy"

predicate isUInt32(i:int) { 0 <= i < 0x1_0000_0000 }
type word = x | isUInt32(x)

/* Z3 gets hopelessly lost thinking about bitvectors, so we wrap both
 * the conversions and operations in opaque functions. We also need a
 * large number of axioms in this file, to work around limitations of
 * Z3's reasoning about the conversions between bitvectors and
 * ints. */

/* ================ Conversions ================ */

lemma lemma_WordAsBits(i:word)
    ensures i == 0 ==> i as bv32 == 0

function {:opaque} WordAsBits(i:word): bv32
    ensures i == 0 <==> WordAsBits(i) == 0
{
    lemma_WordAsBits(i);
    i as bv32
}

lemma lemma_BitsAsWord(b:bv32)
    ensures isUInt32(b as int)
    ensures b == 0 ==> b as int == 0

function {:opaque} BitsAsWord(b:bv32): word
    ensures b == 0 <==> BitsAsWord(b) == 0
{
    lemma_BitsAsWord(b);
    (b as int) as word
}

lemma {:axiom} lemma_WordAsBitsAsWord(i:word)
    ensures BitsAsWord(WordAsBits(i)) == i

lemma {:axiom} lemma_BitsAsWordAsBits(b:bv32)
    ensures WordAsBits(BitsAsWord(b)) == b

lemma lemma_WordBitEquiv(i:word, b:bv32)
    requires i == BitsAsWord(b) || b == WordAsBits(i)
    ensures i == BitsAsWord(b) && b == WordAsBits(i)
{
    lemma_WordAsBitsAsWord(i);
    lemma_BitsAsWordAsBits(b);
}

lemma {:axiom} lemma_BitsAreUnique(b1:bv32, b2:bv32)
    requires BitsAsWord(b1) == BitsAsWord(b2)
    ensures b1 == b2

/* ================ Primitives ================ */

function {:opaque} BitAdd(x:bv32, y:bv32): bv32
{
    x + y
}

function {:opaque} BitSub(x:bv32, y:bv32): bv32
{
    x - y
}

function {:opaque} BitAnd(x:bv32, y:bv32): bv32
{
    x & y
}

function {:opaque} BitOr(x:bv32, y:bv32): bv32
{
    x | y
}

function {:opaque} BitXor(x:bv32, y:bv32): bv32
{
    x ^ y
}

function {:opaque} BitMod(x:bv32, y:bv32): bv32
    requires y != 0
{
    x % y
}

function {:opaque} BitDiv(x:bv32, y:bv32): bv32
    requires y != 0
{
    x / y
}

function {:opaque} BitMul(x:bv32, y:bv32): bv32
{
    x * y
}

function {:opaque} BitNot(x:bv32): bv32
{
    !x
}

function {:opaque} BitShiftLeft(x:bv32, amount:int): bv32
    requires 0 <= amount < 32;
{
    x << amount
}

function {:opaque} BitShiftRight(x:bv32, amount:int): bv32
    requires 0 <= amount < 32;
{
    x >> amount
}

/* ================ Axioms relating the primitives ================ */
/* (it would be nice to prove these!) */

lemma {:axiom} lemma_BitAddEquiv(x:word, y:word)
    requires isUInt32(x + y)
    ensures BitsAsWord(BitAdd(WordAsBits(x), WordAsBits(y))) == x + y

lemma {:axiom} lemma_BitSubEquiv(x:word, y:word)
    requires isUInt32(x - y)
    ensures BitsAsWord(BitSub(WordAsBits(x), WordAsBits(y))) == x - y

lemma {:axiom} lemma_BitModEquiv(x:word, y:word)
    requires y != 0
    ensures BitsAsWord(BitMod(WordAsBits(x), WordAsBits(y))) == x % y

lemma {:axiom} lemma_BitDivEquiv(x:word, y:word)
    requires y != 0
    ensures BitsAsWord(BitDiv(WordAsBits(x), WordAsBits(y))) == x / y

lemma {:axiom} lemma_BitMulEquiv(x:word, y:word)
    requires isUInt32(x * y)
    ensures BitsAsWord(BitMul(WordAsBits(x), WordAsBits(y))) == x * y

lemma {:axiom} lemma_BitCmpEquiv(x:word, y:word)
    ensures x > y ==> WordAsBits(x) > WordAsBits(y)
    ensures x < y ==> WordAsBits(x) < WordAsBits(y)
    ensures x == y ==> WordAsBits(x) == WordAsBits(y)

lemma {:axiom} lemma_BitShiftsSum(x: bv32, a: nat, b: nat)
    requires 0 <= a + b < 32
    ensures BitShiftLeft(x, a + b) == BitShiftLeft(BitShiftLeft(x, a), b)
    ensures BitShiftRight(x, a + b) == BitShiftRight(BitShiftRight(x, a), a)

lemma {:axiom} lemma_BitOrCommutative(a: bv32, b:bv32)
    ensures BitOr(a, b) == BitOr(b, a)

lemma {:axiom} lemma_BitOrAssociative(a: bv32, b:bv32, c: bv32)
    ensures BitOr(a, BitOr(b, c)) == BitOr(BitOr(a, b), c)

lemma {:axiom} lemma_BitAndCommutative(a: bv32, b:bv32)
    ensures BitAnd(a, b) == BitAnd(b, a)

lemma {:axiom} lemma_BitAndAssociative(a: bv32, b:bv32, c: bv32)
    ensures BitAnd(a, BitAnd(b, c)) == BitAnd(BitAnd(a, b), c)

lemma {:axiom} lemma_BitOrAndRelation(a: bv32, b:bv32, c: bv32)
    ensures BitAnd(BitOr(a, b), c) == BitOr(BitAnd(a, c), BitAnd(b, c))


/* ================ Higher-level operations (needed for spec) ================ */

function {:opaque} pow2(n:nat): nat
    ensures pow2(n) > 0
{
    if n == 0 then 1 else 2 * pow2(n - 1)
}

function BitAtPos'(bitpos:int): bv32
    requires 0 <= bitpos < 32
{
    (1 as bv32 << bitpos)
}

lemma {:axiom} lemma_BitposPowerOf2(bitpos:int)
    requires 0 <= bitpos < 32
    ensures BitsAsWord(BitAtPos'(bitpos)) == pow2(bitpos)

function {:opaque} BitAtPos(bitpos:int): bv32
    requires 0 <= bitpos < 32
    ensures BitAtPos(bitpos) != 0
    ensures BitsAsWord(BitAtPos(bitpos)) == pow2(bitpos)
{
    lemma_BitposPowerOf2(bitpos); BitAtPos'(bitpos)
}

function BitmaskLow(bitpos:int): bv32
    requires 0 <= bitpos < 32
{
    BitAtPos(bitpos) - 1
}

function BitmaskHigh(bitpos:int): bv32
    requires 0 <= bitpos < 32
{
    BitNot(BitmaskLow(bitpos))
}

lemma {:axiom} lemma_Bitmask(b:bv32, bitpos:int)
    requires 0 <= bitpos < 32
    ensures BitAnd(b, BitmaskLow(bitpos)) == BitMod(b, BitAtPos(bitpos))
    ensures BitAnd(b, BitmaskHigh(bitpos))
        == BitMul(BitDiv(b, BitAtPos(bitpos)), BitAtPos(bitpos))
/* TODO: can't we prove this? */

lemma lemma_BitmaskAsWord(i:word, bitpos:int)
    requires 0 <= bitpos < 32
    ensures BitsAsWord(BitAnd(WordAsBits(i), BitmaskLow(bitpos))) == i % pow2(bitpos)
    ensures BitsAsWord(BitAnd(WordAsBits(i), BitmaskHigh(bitpos))) == i / pow2(bitpos) * pow2(bitpos)
    ensures BitsAsWord(BitAnd(WordAsBits(i), BitmaskHigh(bitpos))) % pow2(bitpos) == 0
{
    var b := WordAsBits(i);
    lemma_WordBitEquiv(i, b);
    var pb := BitAtPos(bitpos);
    var pi := pow2(bitpos);
    lemma_WordBitEquiv(pi, pb);

    lemma_Bitmask(b, bitpos);

    forall ensures BitsAsWord(BitAnd(b, BitmaskLow(bitpos))) == i % pi {
        calc {
            BitsAsWord(BitAnd(b, BitmaskLow(bitpos)));
            BitsAsWord(BitMod(b, pb));
            { lemma_BitModEquiv(i, pi); }
            i % pi;
        }
    }

    forall ensures BitsAsWord(BitAnd(b, BitmaskHigh(bitpos))) == i / pi * pi {
        calc {
            BitsAsWord(BitAnd(b, BitmaskHigh(bitpos)));
            BitsAsWord(BitMul(BitDiv(b, pb), pb));
            { lemma_BitsAsWordAsBits(BitDiv(b, pb)); }
            BitsAsWord(BitMul(WordAsBits(BitsAsWord(BitDiv(b, pb))), pb));
            {
                lemma_BitsAsWordAsBits(BitDiv(b, pb));
                lemma_DivMulLessThan(i, pi);
                assert BitsAsWord(BitDiv(b, pb)) == i / pi by { lemma_BitDivEquiv(i, pi); }
                assert i >= 0 && pi > 0;
                lemma_DivBounds(i, pi); lemma_MulSign(i / pi, pi);
                assert i / pi * pi >= 0;
                lemma_BitMulEquiv(BitsAsWord(BitDiv(b, pb)), pi);
            }
            BitsAsWord(BitDiv(b, pb)) * BitsAsWord(pb);
            { lemma_BitDivEquiv(i, pi); }
            i / pi * pi;
        }
    }

    lemma_MulModZero(i / pi, pi);
}

// useful properties of pow2 needed for spec
predicate pow2_properties(n:nat)
{
    (n >= 2 ==> pow2(n) % 4 == 0)
    && pow2(10) == 0x400
    && pow2(12) == 0x1000
}

lemma lemma_pow2_properties(n:nat)
    ensures pow2_properties(n)
{
    reveal_pow2();
}

function {:opaque} BitwiseMaskHigh(i:word, bitpos:int): word
    requires 0 <= bitpos < 32;
    ensures BitwiseMaskHigh(i, bitpos) == i / pow2(bitpos) * pow2(bitpos)
    ensures BitwiseMaskHigh(i, bitpos) % pow2(bitpos) == 0
    ensures pow2_properties(bitpos)
{
    lemma_BitmaskAsWord(i, bitpos);
    lemma_pow2_properties(bitpos);
    BitsAsWord(BitAnd(WordAsBits(i), BitmaskHigh(bitpos)))
}
