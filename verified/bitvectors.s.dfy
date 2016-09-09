include "nlarith.s.dfy"

lemma {:axiom} lemma_BitIntEquiv(b:bv32, i:int)
    requires i == b as int || (0 <= i < 0x1_0000_0000 && b == i as bv32)
    ensures i == b as int && b == i as bv32
    ensures i == 0 <==> b == 0

function IntAsBits(i:int): bv32
    requires 0 <= i < 0x1_0000_0000;
    ensures IntAsBits(i) as int == i;
    //ensures IntAsBits(i) == i as bv32;
    ensures i == 0 <==> IntAsBits(i) == 0;
{
    var b := i as bv32;
    lemma_BitIntEquiv(b, i);
    b
}

function BitsAsInt(b:bv32): int
    ensures 0 <= BitsAsInt(b) < 0x1_0000_0000;
    ensures b == 0 <==> BitsAsInt(b) == 0;
    ensures BitsAsInt(b) as bv32 == b;
    //ensures BitsAsInt(b) == b as int;
    decreases b as int // XXX: workaround Dafny issue #26
{
    var i := b as int;
    lemma_BitIntEquiv(b, i);
    i
}

/* Z3 gets hopelessly lost thinking about bitwise operations, so we
 * wrap them in opaque functions */
function {:opaque} BitAdd(x:bv32, y:bv32): bv32
{
    x + y
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

lemma {:axiom} lemma_BitAddEquiv(x:bv32, y:bv32)
    requires BitsAsInt(x) + BitsAsInt(y) < 0x1_0000_0000
    ensures BitsAsInt(BitAdd(x, y)) == BitsAsInt(x) + BitsAsInt(y)

lemma {:axiom} lemma_BitSubEquiv(x:bv32, y:bv32)
    requires BitsAsInt(x) - BitsAsInt(y) >= 0
    ensures BitsAsInt(x - y) == BitsAsInt(x) - BitsAsInt(y)

lemma {:axiom} lemma_BitModEquiv(x:bv32, y:bv32)
    requires y != 0
    ensures BitsAsInt(BitMod(x, y)) == BitsAsInt(x) % BitsAsInt(y)

lemma {:axiom} lemma_BitDivEquiv(x:bv32, y:bv32)
    requires y != 0
    ensures BitsAsInt(BitDiv(x, y)) == BitsAsInt(x) / BitsAsInt(y)

lemma {:axiom} lemma_BitMulEquiv(x:bv32, y:bv32)
    requires BitsAsInt(x) * BitsAsInt(y) < 0x1_0000_0000
    ensures BitsAsInt(BitMul(x, y)) == BitsAsInt(x) * BitsAsInt(y)

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
    ensures BitsAsInt(BitAtPos'(bitpos)) == pow2(bitpos)

function BitAtPos(bitpos:int): bv32
    requires 0 <= bitpos < 32
    ensures BitAtPos(bitpos) != 0
    ensures BitsAsInt(BitAtPos(bitpos)) == pow2(bitpos)
{
    lemma_BitposPowerOf2(bitpos); BitAtPos'(bitpos)
}

function {:opaque} BitmaskLow(bitpos:int): bv32
    requires 0 <= bitpos < 32
{
    BitAtPos(bitpos) - 1
}

function {:opaque} BitmaskHigh(bitpos:int): bv32
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

lemma lemma_BitmaskAsInt(i:int, bitpos:int)
    requires 0 <= i < 0x1_0000_0000
    requires 0 <= bitpos < 32
    ensures BitsAsInt(BitAnd(IntAsBits(i), BitmaskLow(bitpos))) == i % pow2(bitpos)
    ensures BitsAsInt(BitAnd(IntAsBits(i), BitmaskHigh(bitpos))) == i / pow2(bitpos) * pow2(bitpos)
    ensures BitsAsInt(BitAnd(IntAsBits(i), BitmaskHigh(bitpos))) % pow2(bitpos) == 0
{
    var pb := BitAtPos(bitpos);
    var pi := pow2(bitpos);
    assert BitsAsInt(pb) == pi;
    var b := IntAsBits(i);
    lemma_Bitmask(b, bitpos);

    forall ensures BitsAsInt(BitAnd(b, BitmaskLow(bitpos))) == i % pi {
        assert BitAnd(b, BitmaskLow(bitpos)) == BitMod(b, pb);
        lemma_BitModEquiv(b, pb);
        calc {
            BitsAsInt(BitMod(b, pb));
            BitsAsInt(b) % BitsAsInt(pb);
            i % pi;
        }
    }

    forall ensures BitsAsInt(BitAnd(b, BitmaskHigh(bitpos))) == i / pi * pi {
        assert BitAnd(b, BitmaskHigh(bitpos)) == BitMul(BitDiv(b, pb), pb);
        lemma_BitDivEquiv(b, pb);
        assert i / pi == BitsAsInt(BitDiv(b, pb));
        lemma_DivMulLessThan(i, pi);
        lemma_BitMulEquiv(BitDiv(b, pb), pb);
        calc {
            BitsAsInt(BitMul(BitDiv(b, pb), pb));
            BitsAsInt(BitDiv(b, pb)) * BitsAsInt(pb);
            i / pi * pi;
        }
    }

    lemma_MulModZero(i / pi, pi);
}

// useful properties of pow2
predicate pow2_properties(n:nat)
{
    n >= 2 ==> pow2(n) % 4 == 0
    && pow2(10) == 0x400
    && pow2(12) == 0x1000
}

lemma lemma_pow2_properties(n:nat)
    ensures pow2_properties(n)
{
    reveal_pow2();
}

function BitwiseMaskHigh(i:int, bitpos:int): int
    requires 0 <= i < 0x1_0000_0000;
    requires 0 <= bitpos < 32;
    ensures 0 <= BitwiseMaskHigh(i, bitpos) < 0x1_0000_0000;
    ensures BitwiseMaskHigh(i, bitpos) % pow2(bitpos) == 0
    ensures pow2_properties(bitpos)
{
    lemma_BitmaskAsInt(i, bitpos);
    lemma_pow2_properties(bitpos);
    BitsAsInt(BitAnd(IntAsBits(i), BitmaskHigh(bitpos)))
}
