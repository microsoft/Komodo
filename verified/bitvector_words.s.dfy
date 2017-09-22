include "types.s.dfy"
include "bitvectors.s.dfy"

type shift_amount = s | 0 <= s < 32 // Some shifts allow s=32, but we'll be conservative for simplicity

//-----------------------------------------------------------------------------
// Functions for bitwise operations
//-----------------------------------------------------------------------------

function BitwiseXor(x:word, y:word): word
    { BitsAsWord(BitXor(WordAsBits(x), WordAsBits(y))) }

function BitwiseAnd(x:word, y:word): word
    { BitsAsWord(BitAnd(WordAsBits(x), WordAsBits(y))) }

function BitwiseOr(x:word, y:word): word
    { BitsAsWord(BitOr(WordAsBits(x), WordAsBits(y))) }

function BitwiseNot(x:word): word
    { BitsAsWord(BitNot(WordAsBits(x))) }

function LeftShift(x:word, amount:word): word
    requires 0 <= amount < 32;
    { BitsAsWord(BitShiftLeft(WordAsBits(x), amount)) }

function RightShift(x:word, amount:word): word
    requires 0 <= amount < 32;
    { BitsAsWord(BitShiftRight(WordAsBits(x), amount)) }

function RotateRight(x:word, amount:shift_amount): word
    requires 0 <= amount < 32;
    { BitsAsWord(BitRotateRight(WordAsBits(x), amount)) }

function {:opaque} UpdateTopBits(origval:word, newval:word): word
{
    BitwiseOr(LeftShift(newval, 16), BitwiseMaskLow(origval, 16))
}

