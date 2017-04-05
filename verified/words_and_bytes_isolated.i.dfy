include "words_and_bytes.s.dfy"

lemma lemma_explode8_WordToBytes(w:word, b:seq<byte>)
    requires b == WordToBytes(w)
    ensures  w == 0x100_0000 * b[0] + 0x1_0000 * b[1] + 0x100 * b[2] + b[3]
{
    reveal WordToBytes();
    assert {:fuel BEUintToSeqByte, 4} w == 0x100_0000 * b[0] + 0x1_0000 * b[1] + 0x100 * b[2] + b[3];
}

lemma lemma_explode8_Uint64ToBytes(u:uint64, b:seq<byte>)
    requires b == Uint64ToBytes(u)
    ensures  u ==
        (0x100_0000 * b[0] + 0x1_0000 * b[1] + 0x100 * b[2] + b[3]) * 0x1_0000_0000 +
        (0x100_0000 * b[4] + 0x1_0000 * b[5] + 0x100 * b[6] + b[7])
{
    reveal Uint64ToBytes();
    assert {:fuel BEUintToSeqByte, 8} u ==
        (0x100_0000 * b[0] + 0x1_0000 * b[1] + 0x100 * b[2] + b[3]) * 0x1_0000_0000 +
        (0x100_0000 * b[4] + 0x1_0000 * b[5] + 0x100 * b[6] + b[7]);
}

