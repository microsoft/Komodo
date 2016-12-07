// REQUIRES-ANY: TEST, SHA
// RUN: %DAFNY /compile:0 %s %DARGS

include "../words_and_bytes.s.dfy"
include "../ARMdef.dfy"

//-////////////////////////////////////////////////////////////////////////////
//- HMAC specification based on:
//- http://csrc.nist.gov/publications/fips/fips198-1/FIPS-198-1_final.pdf
//-////////////////////////////////////////////////////////////////////////////

function {:opaque} SeqXor(a:seq<word>, b:seq<word>) : seq<word>
    requires |a|==|b|;
    ensures  |SeqXor(a, b)| == |a|;
    ensures  forall i :: 0 <= i < |a| ==> SeqXor(a, b)[i] == BitwiseXor(a[i], b[i]);
{
    if |a| == 0 then [] else [ BitwiseXor(a[0], b[0]) ] + SeqXor(a[1..], b[1..])
}

function {:autoReq} Opad(len:int) : seq<word>
{
    RepeatValue<word>(0x5c5c5c5c as word, len)
}

function {:autoReq} Ipad(len:int) : seq<word>
{
    RepeatValue<word>(0x36363636 as word, len)
}
