// REQUIRES-ANY: TEST, SHA
// RUN: %DAFNY /compile:0 %s %DARGS

//include "assembly.s.dfy"
include "../words_and_bytes.s.dfy"
include "../ARMdef.dfy"

function method{:axiom} BitwiseAdd32(x:word, y:word):word
    ensures BitwiseAdd32(x, y) == (((x as int) + (y as int)) % 0x100000000) as word;

//-///////////////////////////////////////////////////
//- Ch, Maj, BSIG0, BSIG1, SSIG0, SSIG1
//-///////////////////////////////////////////////////

function {:opaque} Ch(x:word, y:word, z:word) : word
{
    BitwiseXor(BitwiseAnd(x, y), BitwiseAnd(BitwiseNot(x), z))
}

function {:opaque} Maj(x:word, y:word, z:word) : word
{
    BitwiseXor(BitwiseXor(BitwiseAnd(x, y), BitwiseAnd(x, z)), BitwiseAnd(y, z))
}

function {:opaque} Parity(x:word, y:word, z:word) : word
{
    BitwiseXor(BitwiseXor(x, y), z)
}

function {:opaque} ft(t:word, x:word, y:word, z:word) : word
    requires 0 <= t <= 79;
{

    if t >= 0 && t <= 19 then
        Ch(x, y, z)

    else if t >= 40 && t <= 59 then
        Maj(x, y, z)
    else
        Parity(x, y, z)
}

function {:opaque} BSIG0(x:word) : word
{
    BitwiseXor(BitwiseXor(RotateRight(x, 2), RotateRight(x, 13)), RotateRight(x, 22))
}

function {:opaque} BSIG1(x:word) : word
{
    BitwiseXor(BitwiseXor(RotateRight(x, 6), RotateRight(x, 11)), RotateRight(x, 25))
}

function {:opaque} SSIG0(x:word) : word
{
    BitwiseXor(BitwiseXor(RotateRight(x, 7), RotateRight(x, 18)), RightShift(x, 3))
}

function {:opaque} SSIG1(x:word) : word
{
    BitwiseXor(BitwiseXor(RotateRight(x, 17), RotateRight(x, 19)), RightShift(x, 10))
}

function{:opaque} BreakIntoBlocks<T>(os:seq<T>, block_size:int) : seq<seq<T>>
    requires 0 < block_size;
    decreases |os|;
{
    if |os| == 0 then []
    else if |os| < block_size then [os]
    else [os[..block_size]] + BreakIntoBlocks(os[block_size..], block_size)
}

function MaxBytesForSHA() : int { 0x1FFF_FFFF_FFFF_FFFF }

predicate WordSeqIsProperlySHAPaddedByteSeq(ws:seq<word>, bytes:seq<byte>)
{
       |bytes| <= MaxBytesForSHA()
    && WordSeqToBytes(ws) == bytes + [0x80 as byte] + RepeatByte(0, (119 - (|bytes| % 64)) % 64) + Uint64ToBytes((|bytes| * 8) as uint64)
}

//- Used to avoid matching loops in some uses of forall
//- (avoid formulas of the form "forall i :: ...a[i]...a[i+1]...", which can loop
//- if the trigger is a[i] and the i+1 in the body is used to instantiate the i in the trigger)
function TBlk(blk:int):bool { true }
function TStep(t:word):bool { true }

