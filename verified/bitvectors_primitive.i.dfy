lemma lemma_ShiftsLeftSum(x: bv32, a: nat, b: nat)
    requires 0 <= a + b < 8 || 8 <= a + b < 16 || 16 <= a + b < 24 || 24 <= a + b < 32
    ensures x << (a + b) == (x << a) << b
{  }

lemma lemma_ShiftsRightSum(x: bv32, a: nat, b: nat)
    requires 0 <= a + b < 32
    ensures x >> (a + b) == (x >> a) >> b
{ }

