include "assembly.s.dfy"

//-///////////////////////////////////////////////////
//- Ch, Maj, BSIG0, BSIG1, SSIG0, SSIG1
//-///////////////////////////////////////////////////

function {:opaque} Ch(x:uint32, y:uint32, z:uint32) : uint32
{
    BitwiseXor(BitwiseAnd(x, y), BitwiseAnd(BitwiseNot(x), z))
}

function {:opaque} Maj(x:uint32, y:uint32, z:uint32) : uint32
{
    BitwiseXor(BitwiseXor(BitwiseAnd(x, y), BitwiseAnd(x, z)), BitwiseAnd(y, z))
}

function {:opaque} Parity(x:uint32, y:uint32, z:uint32) : uint32
{
    BitwiseXor(BitwiseXor(x, y), z)
}

function {:opaque} ft(t:uint32, x:uint32, y:uint32, z:uint32) : uint32
    requires 0 <= t <= 79;
{

    if t >= 0 && t <= 19 then
        Ch(x, y, z)

    else if t >= 40 && t <= 59 then
        Maj(x, y, z)
    else
        Parity(x, y, z)
}

function {:opaque} BSIG0(x:uint32) : uint32
{
    BitwiseXor(BitwiseXor(RotateRight(x, 2), RotateRight(x, 13)), RotateRight(x, 22))
}

function {:opaque} BSIG1(x:uint32) : uint32
{
    BitwiseXor(BitwiseXor(RotateRight(x, 6), RotateRight(x, 11)), RotateRight(x, 25))
}

function {:opaque} SSIG0(x:uint32) : uint32
{
    BitwiseXor(BitwiseXor(RotateRight(x, 7), RotateRight(x, 18)), RightShift(x, 3))
}

function {:opaque} SSIG1(x:uint32) : uint32
{
    BitwiseXor(BitwiseXor(RotateRight(x, 17), RotateRight(x, 19)), RightShift(x, 10))
}

function method {:opaque} NumPaddingZeroes(message_len:uint32) : uint32
    //- According to the spec, this is the smallest non-negative k such that message_len + 1 + k = 448 (mod 512)
    ensures 0 <= NumPaddingZeroes(message_len) < 512;
{
    (959 - (message_len % 512)) % 512
}

function{:opaque} BreakIntoBlocks<T>(os:seq<T>, block_size:int) : seq<seq<T>>
    requires 0 < block_size;
    decreases |os|;
{
    if |os| == 0 then []
    else if |os| < block_size then [os]
    else [os[..block_size]] + BreakIntoBlocks(os[block_size..], block_size)
}

/*
function PadMessageForSHA(messageBits: seq<int>) : seq<int>
{
    messageBits + [1] + RepeatDigit(0, NumPaddingZeroes(|messageBits|)) + BEIntToDigitSeq(2, 64, |messageBits|)
}

function {:opaque} BlockMessageForSHA(paddedMessageBits: seq<int>) : seq<seq<int>>
    requires IsBitSeq(paddedMessageBits);
    requires |paddedMessageBits| % 512 == 0;
{
    BreakIntoBlocks(BEIntToDigitSeq(power2(32), |paddedMessageBits|/32, BEBitSeqToInt(paddedMessageBits)), 16)
}

function method OneOf8(i:uint32, n0:uint32, n1:uint32, n2:uint32, n3:uint32, n4:uint32, n5:uint32, n6:uint32, n7:uint32) : uint32
    requires 0 <= i < 8;
{
    if i == 0 then n0 else if i == 1 then n1 else if i == 2 then n2 else if i == 3 then n3
    else if i == 4 then n4 else if i == 5 then n5 else if i == 6 then n6 else n7
}
*/

//- Used to avoid matching loops in some uses of forall
//- (avoid formulas of the form "forall i :: ...a[i]...a[i+1]...", which can loop
//- if the trigger is a[i] and the i+1 in the body is used to instantiate the i in the trigger)
function TBlk(blk:uint32):bool { true }
function TStep(t:uint32):bool { true }

