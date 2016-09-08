lemma {:axiom} lemma_BitvecToInt(b:bv32)
    ensures 0 <= b as int < 0x1_0000_0000;
    ensures (b as int) as bv32 == b;
    ensures b == 0 <==> b as int == 0;

lemma {:axiom} lemma_BitvecIntEquivalence(b:bv32, i:int)
    requires i == b as int || (0 <= i < 0x1_0000_0000 && b == i as bv32)
    ensures i == b as int && b == i as bv32

lemma {:axiom} lemma_BitvecIntCasts(b:bv32)
    ensures b == b as int as bv32

lemma {:axiom} lemma_IntBitvecCasts(i:int)
    requires 0 <= i < 0x1_0000_0000
    ensures i == i as bv32 as int

lemma {:axiom} lemma_IntToBitvec(i:int)
    requires 0 <= i < 0x1_0000_0000;
    ensures (i as bv32) as int == i;
    ensures i == 0 <==> i as bv32 == 0;

function IntToBitvec(i:int): bv32
    requires 0 <= i < 0x1_0000_0000;
    ensures i == 0 <==> IntToBitvec(i) == 0;
    ensures IntToBitvec(i) as int == i;
{
    lemma_IntToBitvec(i); i as bv32
}

function BitvecToInt(b:bv32): int
    ensures 0 <= BitvecToInt(b) < 0x1_0000_0000;
    ensures b == 0 <==> BitvecToInt(b) == 0;
    ensures BitvecToInt(b) as bv32 == b;
    decreases b as int // XXX: workaround Dafny issue #26
{
    lemma_BitvecToInt(b); b as int
}

lemma {:axiom} lemma_BitwiseModEquiv(x:bv32, y:bv32)
    requires y != 0
    ensures BitvecToInt(x % y) == BitvecToInt(x) % BitvecToInt(y);

lemma {:axiom} lemma_BitwiseDivEquiv(x:bv32, y:bv32)
    requires y != 0
    ensures BitvecToInt(x / y) == BitvecToInt(x) / BitvecToInt(y);

lemma {:axiom} lemma_BitwiseMulEquiv(x:bv32, y:bv32)
    ensures BitvecToInt(x * y) == BitvecToInt(x) * BitvecToInt(y);

function pow2(n:nat): nat
    ensures pow2(n) > 0
{
    if n == 0 then 1 else 2 * pow2(n - 1)
}

function BitposValue'(bitpos:int): bv32
    requires 0 <= bitpos < 32
{
    (1 as bv32 << bitpos)
}

lemma {:axiom} lemma_BitposPowerOf2(bitpos:int)
    requires 0 <= bitpos < 32
    ensures BitvecToInt(BitposValue'(bitpos)) == pow2(bitpos)

function BitposValue(bitpos:int): bv32
    requires 0 <= bitpos < 32
    ensures BitposValue(bitpos) != 0
    ensures BitposValue(bitpos) as int == pow2(bitpos)
{
    lemma_BitposPowerOf2(bitpos); BitposValue'(bitpos)
}

function BitmaskLow(bitpos:int): bv32
    requires 0 <= bitpos < 32
{
    BitposValue(bitpos) - 1
}

function BitmaskHigh(bitpos:int): bv32
    requires 0 <= bitpos < 32
{
    !BitmaskLow(bitpos)
}

lemma {:axiom} lemma_BitwiseMask(x:bv32, bitpos:int)
    requires 0 <= bitpos < 32
    ensures x & BitmaskLow(bitpos) == x % BitposValue(bitpos)
    ensures x & BitmaskHigh(bitpos) == x / BitposValue(bitpos) * BitposValue(bitpos)
    ensures (x & BitmaskHigh(bitpos)) % BitposValue(bitpos) == 0
/* TODO: can't we prove this? */

lemma lemma_BitwiseMaskInt(i:int, bitpos:int)
    requires 0 <= i < 0x1_0000_0000;
    requires 0 <= bitpos < 32
    //ensures BitvecToInt(IntToBitvec(i) & BitmaskLow(bitpos)) == i % pow2(bitpos)
    //ensures BitvecToInt(IntToBitvec(i) & BitmaskHigh(bitpos)) == i / pow2(bitpos) * pow2(bitpos)
    ensures BitvecToInt(IntToBitvec(i) & BitmaskHigh(bitpos)) % pow2(bitpos) == 0
{
    lemma_BitwiseMask(IntToBitvec(i), bitpos);
    assert (IntToBitvec(i) & BitmaskHigh(bitpos)) % BitposValue(bitpos) == 0;
    lemma_BitwiseModEquiv(IntToBitvec(i) & BitmaskHigh(bitpos), BitposValue(bitpos));
    assert BitvecToInt(BitposValue(bitpos)) == pow2(bitpos);
}

function BitwiseMaskHighBitsInt(i:int, bitpos:int): int
    requires 0 <= i < 0x1_0000_0000;
    requires 0 <= bitpos < 32;
    ensures 0 <= BitwiseMaskHighBitsInt(i, bitpos) < 0x1_0000_0000;
    ensures BitwiseMaskHighBitsInt(i, bitpos) % pow2(bitpos) == 0
{
    lemma_BitwiseMaskInt(i, bitpos);
    assert BitvecToInt(IntToBitvec(i) & BitmaskHigh(bitpos)) % pow2(bitpos) == 0;
    BitvecToInt(IntToBitvec(i) & BitmaskHigh(bitpos))
}
