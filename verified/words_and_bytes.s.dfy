// REQUIRES-ANY: TEST, UTIL
// RUN: %DAFNY /compile:0 %s %DARGS

include "bitvectors.s.dfy"  // For the definition of word

module words_and_bytes_s {
import opened words_and_bytes_s_bitvectors_s = bitvectors_s

type byte = i | 0 <= i < 256
type uint64 = i | 0 <= i < 0x1_0000_0000_0000_0000

// Map an arbitrary number of bytes to an integer
function BEByteSeqToInt(bytes:seq<byte>) : int
    decreases |bytes|;
{
    if bytes == [] then 0
    else BEByteSeqToInt(bytes[..|bytes|-1]) * 256 + (bytes[|bytes|-1] as int)
}

// Map a big-endian integer to a sequence of bytes
function BEUintToSeqByte(v:int, width:int) : seq<byte>
    ensures width >= 0 && v >= 0 ==> |BEUintToSeqByte(v, width)| == width;
{
    if width > 0 && v >= 0 then
        BEUintToSeqByte(v/0x100, width - 1) + [ (v % 0x100) as byte ]
    else
        []
}

function {:opaque} BytesToWord(b0:byte, b1:byte, b2:byte, b3:byte) : word
{
    var w := BEByteSeqToInt([b0, b1, b2, b3]);
    if 0 <= w < 0x1_0000_0000 then (w as word) else 42
    // We defer the proof that BEByteSeqToInt is in bounds to the verified implementation
}

function{:opaque} WordToBytes(w:word) : seq<byte>
    ensures |WordToBytes(w)| == 4;
{
    BEUintToSeqByte(w as int, 4)
//    [ byte( w/ 0x1000000),
//      byte((w/   0x10000) % 256),
//      byte((w/     0x100) % 256),
//      byte(w              % 256) ]
}

function {:opaque} Uint64ToBytes(u:uint64) : seq<byte>
    ensures |Uint64ToBytes(u)| == 8;
{
    [ ( u/ 0x100000000000000) as byte,
      ((u/   0x1000000000000) % 0x100) as byte,
      ((u/     0x10000000000) % 0x100) as byte,
      ((u/       0x100000000) % 0x100) as byte,
      ((u/         0x1000000) % 0x100) as byte,
      ((u/           0x10000) % 0x100) as byte,
      ((u/             0x100) % 0x100) as byte,
      ((u                   ) % 0x100) as byte]
}

function WordSeqToBytes(ws:seq<word>) : seq<byte>
    ensures |WordSeqToBytes(ws)| == |ws| * 4;
    //ensures var bytes := WordSeqToBytes(ws); forall i :: 0 <= i < |ws| ==> bytes[i*4..(i+1)*4] == WordToBytes(ws[i]);
{
    if |ws| == 0 then [] else WordToBytes(ws[0]) + WordSeqToBytes(ws[1..])
}

function RepeatByte(b:byte, count:int) : seq<byte>
    requires count >= 0;
    ensures  |RepeatByte(b, count)| == count;
    ensures  forall x :: x in RepeatByte(b, count) ==> x == b;
{
    if count == 0 then [] else RepeatByte(b, count-1) + [b]
}

function RepeatValue<T>(n:T, count:int) : seq<T>
    requires count >= 0;
    ensures  |RepeatValue(n, count)| == count;
    ensures  forall x :: x in RepeatValue(n, count) ==> x == n;
{
    if count == 0 then [] else RepeatValue(n, count-1) + [n]
}

function ConcatenateSeqs<T>(ss:seq<seq<T>>) : seq<T>
{
    if |ss| == 0 then [] else ss[0] + ConcatenateSeqs(ss[1..])
}

}
