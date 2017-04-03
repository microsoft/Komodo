include "words_and_bytes.s.dfy"
include "words_and_bytes_isolated.i.dfy"

function {:opaque} BytesToUint64(b0:byte, b1:byte, b2:byte, b3:byte, b4:byte, b5:byte, b6:byte, b7:byte) : uint64
{
    assert [b0, b1, b2, b3, b4, b5, b6, b7] == [b0] + [b1] + [b2] + [b3] + [b4] + [b5] + [b6] + [b7];
    assert{:fuel BEByteSeqToInt, 8} 0 <= BEByteSeqToInt([b0, b1, b2, b3, b4, b5, b6, b7]) < 0x1_0000_0000_0000_0000;
    BEByteSeqToInt([b0, b1, b2, b3, b4, b5, b6, b7])
}

lemma lemma_be_uint_byte_inverses(b:seq<byte>)
    ensures BEUintToSeqByte(BEByteSeqToInt(b), |b|) == b
{
    if (|b| != 0)
    {
        lemma_be_uint_byte_inverses(b[.. |b| - 1]);
    }
}

lemma lemma_BytesToWord_WordToBytes_inverses(b0:byte, b1:byte, b2:byte, b3:byte)
    ensures WordToBytes(BytesToWord(b0, b1, b2, b3)) == [b0, b1, b2, b3]
{
    reveal WordToBytes();
    reveal BytesToWord();
    lemma_be_uint_byte_inverses([b0, b1, b2, b3]);
}

lemma lemma_BytesToUint64_Uint64ToBytes_inverses(b0:byte, b1:byte, b2:byte, b3:byte, b4:byte, b5:byte, b6:byte, b7:byte)
    ensures Uint64ToBytes(BytesToUint64(b0, b1, b2, b3, b4, b5, b6, b7)) == [b0, b1, b2, b3, b4, b5, b6, b7]
{
    reveal Uint64ToBytes();
    reveal BytesToUint64();
    lemma_be_uint_byte_inverses([b0, b1, b2, b3, b4, b5, b6, b7]);
}

lemma lemma_explode8_BytesToWord(b0:byte, b1:byte, b2:byte, b3:byte)
    ensures BytesToWord(b0, b1, b2, b3) == 0x100_0000 * b0 + 0x1_0000 * b1 + 0x100 * b2 + b3
{
    reveal BytesToWord();
    assert{:fuel BEByteSeqToInt, 4} BytesToWord(b0, b1, b2, b3) == 0x100_0000 * b0 + 0x1_0000 * b1 + 0x100 * b2 + b3;
}

lemma lemma_implode8_WordToBytes(b0:byte, b1:byte, b2:byte, b3:byte)
    ensures WordToBytes(0x100_0000 * b0 + 0x1_0000 * b1 + 0x100 * b2 + b3) == [b0, b1, b2, b3]
{
    lemma_explode8_BytesToWord(b0, b1, b2, b3);
    lemma_BytesToWord_WordToBytes_inverses(b0, b1, b2, b3);
}

lemma lemma_WordToBytes_BytesToWord_inverses(w:word, b:seq<byte>)
    requires b == WordToBytes(w)
    ensures  BytesToWord(b[0], b[1], b[2], b[3]) == w
{
    lemma_explode8_WordToBytes(w, b);
    lemma_explode8_BytesToWord(b[0], b[1], b[2], b[3]);
}

lemma lemma_explode8_BytesToUint64(b0:byte, b1:byte, b2:byte, b3:byte, b4:byte, b5:byte, b6:byte, b7:byte)
    ensures BytesToUint64(b0, b1, b2, b3, b4, b5, b6, b7) ==
        (0x100_0000 * b0 + 0x1_0000 * b1 + 0x100 * b2 + b3) * 0x1_0000_0000 +
        (0x100_0000 * b4 + 0x1_0000 * b5 + 0x100 * b6 + b7)
{
    var b := [b0, b1, b2, b3, b4, b5, b6, b7];
    assert b == [b[0]] + [b[1]] + [b[2]] + [b[3]] + [b[4]] + [b[5]] + [b[6]] + [b[7]];
    assert{:fuel BEByteSeqToInt, 8} BEByteSeqToInt([b0, b1, b2, b3, b4, b5, b6, b7]) ==
        (0x100_0000 * b0 + 0x1_0000 * b1 + 0x100 * b2 + b3) * 0x1_0000_0000 +
        (0x100_0000 * b4 + 0x1_0000 * b5 + 0x100 * b6 + b7);
    reveal BytesToUint64();
}

lemma lemma_explode32_BytesToUint64(b0:byte, b1:byte, b2:byte, b3:byte, b4:byte, b5:byte, b6:byte, b7:byte)
    ensures BytesToUint64(b0, b1, b2, b3, b4, b5, b6, b7) == 0x1_0000_0000 * BytesToWord(b0, b1, b2, b3) + BytesToWord(b4, b5, b6, b7)
{
    lemma_explode8_BytesToUint64(b0, b1, b2, b3, b4, b5, b6, b7);
    lemma_explode8_BytesToWord(b0, b1, b2, b3);
    lemma_explode8_BytesToWord(b4, b5, b6, b7);
}

lemma lemma_implode32_Uint64ToBytes(w0:word, w1:word)
    ensures Uint64ToBytes(0x1_0000_0000 * w0 + w1) == WordToBytes(w0) + WordToBytes(w1)
{
    var b03 := WordToBytes(w0);
    var b47 := WordToBytes(w1);
    var b0, b1, b2, b3 := b03[0], b03[1], b03[2], b03[3];
    var b4, b5, b6, b7 := b47[0], b47[1], b47[2], b47[3];
    calc
    {
        Uint64ToBytes(0x1_0000_0000 * w0 + w1);
            { lemma_WordToBytes_BytesToWord_inverses(w0, b03); }
            { lemma_WordToBytes_BytesToWord_inverses(w1, b47); }
        Uint64ToBytes(0x1_0000_0000 * BytesToWord(b0, b1, b2, b3) + BytesToWord(b4, b5, b6, b7));
            { lemma_explode32_BytesToUint64(b0, b1, b2, b3, b4, b5, b6, b7); }
        Uint64ToBytes(BytesToUint64(b0, b1, b2, b3, b4, b5, b6, b7));
            { lemma_BytesToUint64_Uint64ToBytes_inverses(b0, b1, b2, b3, b4, b5, b6, b7); }
        [b0, b1, b2, b3, b4, b5, b6, b7];
        WordToBytes(w0) + WordToBytes(w1);
    }
}

lemma bswap32_on_byte(b:byte) 
    ensures WordToBytes(b) == [0, 0, 0, b]
{
    lemma_implode8_WordToBytes(0, 0, 0, b);
}

lemma lemma_bswap32_inverse(w:word)
    ensures bswap32(bswap32(w)) == w
{
    var b := WordToBytes(w);
    lemma_BytesToWord_WordToBytes_inverses(b[3], b[2], b[1], b[0]);
    lemma_WordToBytes_BytesToWord_inverses(w, b);
}

function {:opaque} bswap32_seq(input:seq<word>) : seq<word>
    ensures |bswap32_seq(input)| == |input|
    ensures forall i :: 0 <= i < |bswap32_seq(input)| ==> bswap32_seq(input)[i] == bswap32(input[i])
{
    if input == [] then []
    else [bswap32(input[0])] + bswap32_seq(input[1..])
}

lemma length_to_bytes(length:word)
    ensures WordSeqToBytes(bswap32_seq([0, bswap32(length)])) == Uint64ToBytes(length)
{
    assert{:fuel WordSeqToBytes, 2} WordSeqToBytes([0, length]) == WordToBytes(0) + WordToBytes(length);
    assert bswap32(0) == 0 by { lemma_implode8_WordToBytes(0, 0, 0, 0); lemma_explode8_BytesToWord(0, 0, 0, 0); }
    lemma_bswap32_inverse(length);
    lemma_implode32_Uint64ToBytes(0, length);
}

lemma bswap32_seq_indexing(s:seq<word>, i:nat, j:nat)
    requires 0 <= i < j <= |s|;
    ensures bswap32_seq(s)[i..j] == bswap32_seq(s[i..j]);
{
    reveal_bswap32_seq();
    if i == 0 {
    } else {
        
    }
}

lemma bswap32_seq_adds(s:seq<word>, s':seq<word>) 
    ensures bswap32_seq(s) + bswap32_seq(s') == bswap32_seq(s + s');
{
    if s == [] {
    } else {
        calc {
            bswap32_seq(s) + bswap32_seq(s');
                { reveal_bswap32_seq(); }
            [bswap32(s[0])] + bswap32_seq(s[1..]) + bswap32_seq(s');
                { bswap32_seq_adds(s[1..], s'); }
            [bswap32(s[0])] + bswap32_seq(s[1..] + s');
                { reveal_bswap32_seq(); }
            bswap32_seq(s + s');
        }
    }
}

lemma {:fuel BEUintToSeqByte, 5} WordToBytes_zero()
    ensures WordToBytes(0) == [0, 0, 0, 0];
{
    reveal_WordToBytes();
}

lemma BEByteSeqToInt_on_zero(s:seq<byte>)
    requires forall i :: 0 <= i < |s| ==> s[i] == 0;
    ensures BEByteSeqToInt(s) == 0;
{
    if |s| == 0 {
    } else {
        BEByteSeqToInt_on_zero(s[..|s|-1]);
    }
}

lemma bswap32_seq_on_zero(s:seq<word>)
    requires forall i :: 0 <= i < |s| ==> s[i] == 0;
    ensures  bswap32_seq(s) == s;
{
    if |s| == 0 {
        reveal_bswap32_seq();
    } else {
        calc {
            bswap32_seq(s);
                { reveal_bswap32_seq(); }
            [bswap32(s[0])] + bswap32_seq(s[1..]);
            [bswap32(0)] + bswap32_seq(s[1..]);
                { WordToBytes_zero(); reveal_BytesToWord(); BEByteSeqToInt_on_zero([0,0,0,0]); }
            [0] + bswap32_seq(s[1..]);
                { bswap32_seq_on_zero(s[1..]); }
            [0] + s[1..];
            [s[0]] + s[1..];
            s;
        }
    }
}

lemma RepeatByte_adds(b:byte, c:nat, c':nat)
    ensures RepeatByte(b, c) + RepeatByte(b, c') == RepeatByte(b, c + c');
{
    if c' == 0 {
    } else {
        calc {
            RepeatByte(b, c) + RepeatByte(b, c');
            RepeatByte(b, c) + RepeatByte(b, c' - 1) + [b];
                { RepeatByte_adds(b, c, c' - 1); }
            RepeatByte(b, c + c' - 1) + [b];
            RepeatByte(b, c + c');
        }
    }
}

lemma {:fuel RepeatByte, 5} WordSeqToBytes_on_zero(s:seq<word>)
    requires forall i :: 0 <= i < |s| ==> s[i] == 0;
    ensures  WordSeqToBytes(s) == RepeatByte(0, |s|*4);
{
    if |s| == 0 {
    } else {
        calc {
            WordSeqToBytes(s);
            WordToBytes(s[0]) + WordSeqToBytes(s[1..]);
                { WordToBytes_zero(); }
            [0, 0, 0, 0] + WordSeqToBytes(s[1..]);
                { assert RepeatByte(0, 4) == [0, 0, 0, 0]; }
            RepeatByte(0, 4) + WordSeqToBytes(s[1..]);
                { WordSeqToBytes_on_zero(s[1..]); }
            RepeatByte(0, 4) + RepeatByte(0, |s[1..]|*4);
                { RepeatByte_adds(0, 4, |s[1..]|*4); }
            RepeatByte(0, 4 + |s[1..]|*4);
            RepeatByte(0, |s|*4);
        }
    }
}

lemma lemma_WordSeqToBytes_adds(s:seq<word>, s':seq<word>)
    ensures WordSeqToBytes(s + s') == WordSeqToBytes(s) + WordSeqToBytes(s');
{
    if s == [] {
    } else {
        calc {
            WordSeqToBytes(s + s');
            WordToBytes((s + s')[0]) + WordSeqToBytes((s + s')[1..]);
                { assert (s + s')[0] == s[0]; }
            WordToBytes(s[0]) + WordSeqToBytes((s + s')[1..]);
                { lemma_WordSeqToBytes_adds(s[1..], s'); assert s[1..] + s' == (s+s')[1..]; }
            WordToBytes(s[0]) + WordSeqToBytes(s[1..]) + WordSeqToBytes(s');
            WordSeqToBytes(s) + WordSeqToBytes(s');
        }
    }
}

