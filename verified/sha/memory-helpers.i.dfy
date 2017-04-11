include "../ARMdef.dfy"
include "../ARMspartan.dfy"
include "sha256-invariants.i.dfy"

lemma lemma_ValidMemRange_offset_word(base:int, count:nat)
    requires ValidMemRange(base, base + count * WORDSIZE);
    ensures  count > 1 ==> ValidMemRange(base + WORDSIZE, base + WORDSIZE + (count - 1) * WORDSIZE);
{
    var offset := base + WORDSIZE;
    var limit := base + WORDSIZE + (count - 1) * WORDSIZE;
    //assert isUInt32(offset);
    //assert base <= offset < base + count * WORDSIZE;
    assert WordAligned(offset);
    //assert ValidMem(offset);
    //assert ValidMem(limit);
}

lemma lemma_ValidMemRange_reduced(base:int, count:nat, count':nat)
    requires ValidMemRange(base, base + count * WORDSIZE);
    requires count' < count;
    ensures  ValidMemRange(base, base + (count - count') * WORDSIZE);
{
    var offset := base + count'*WORDSIZE;
    var limit := base + WORDSIZE + (count - count') * WORDSIZE;
    assert WordAligned(offset);
    if count' == 0 {
    } else {
        lemma_ValidMemRange_offset(base, count, count' - 1);
        assert ValidMemRange(base, base + (count - count' + 1) * WORDSIZE);
    }
}

lemma lemma_ValidMemRange_offset(base:int, count:nat, count':nat)
    requires ValidMemRange(base, base + count * WORDSIZE);
    requires count' < count;
    ensures  ValidMemRange(base + count'*WORDSIZE, base + (count - count') * WORDSIZE);
{
    var offset := base + count'*WORDSIZE;
    var limit := base + WORDSIZE + (count - count') * WORDSIZE;
    assert WordAligned(offset);
    if count' == 0 {
    } else {
        lemma_ValidMemRange_offset(base, count, count' - 1);
        assert ValidMemRange(base + (count' - 1)*WORDSIZE, base + (count - count' + 1) * WORDSIZE);
        lemma_ValidMemRange_offset_word(base + (count' - 1)*WORDSIZE, (count - count' + 1));
    }
}

function AddrMemContentsSeq(m:memmap, begin_ptr:nat, count:nat) : seq<word>
  requires ValidAddrMemStateOpaque(m);
  requires count > 0 ==> ValidMemRange(begin_ptr, begin_ptr + count * WORDSIZE);
  decreases count;
  ensures  |AddrMemContentsSeq(m, begin_ptr, count)| == count;
  ensures  forall i :: 0 <= i < count ==> AddrMemContents(m, begin_ptr + i * WORDSIZE) == AddrMemContentsSeq(m, begin_ptr, count)[i];
{
  if count == 0 then []
  else
      lemma_ValidMemRange_offset_word(begin_ptr, count);
      [AddrMemContents(m, begin_ptr)] + AddrMemContentsSeq(m, begin_ptr + WORDSIZE, count - 1)
}

lemma lemma_AddrMemContentsSeq_adds(m:memmap, begin_ptr:nat, count:nat, count':nat)
  requires ValidAddrMemStateOpaque(m);
  requires count > 0 ==> ValidMemRange(begin_ptr, begin_ptr + count * WORDSIZE);
  requires count' < count;
  decreases count;
  ensures  count - count' > 0 ==> ValidMemRange(begin_ptr + count' * WORDSIZE, begin_ptr + (count - count') * WORDSIZE);
  ensures  AddrMemContentsSeq(m, begin_ptr, count) == AddrMemContentsSeq(m, begin_ptr, count') 
                                                    + AddrMemContentsSeq(m, begin_ptr + count' * WORDSIZE, count - count') 
{
    if count' == 0 {
    } else {
        lemma_AddrMemContentsSeq_adds(m, begin_ptr + WORDSIZE, count - 1, count' - 1);
    }
}

lemma lemma_AddrMemContentsSeq_framing1(m:memmap, m':memmap, begin_ptr:nat, count:nat, l1:nat, h1:nat)
    requires ValidAddrMemStateOpaque(m) && ValidAddrMemStateOpaque(m');
    requires l1 <= h1;
    requires AddrMemPreservingExcept(m, m', l1, h1);
    requires h1 <= begin_ptr || l1 >= begin_ptr + count * WORDSIZE;
    requires count > 0 ==> ValidMemRange(begin_ptr, begin_ptr + count * WORDSIZE);
    decreases count;
    ensures  AddrMemContentsSeq(m, begin_ptr, count) == AddrMemContentsSeq(m', begin_ptr, count);
{
    if count == 0 {
    } else {
        lemma_ValidMemRange_offset_word(begin_ptr, count);
        lemma_AddrMemContentsSeq_framing1(m, m', begin_ptr + WORDSIZE, count - 1, l1, h1);
    }
}

lemma lemma_AddrMemContentsSeq_framing2(m:memmap, m':memmap, begin_ptr:nat, count:nat, l1:nat, h1:nat, l2:nat, h2:nat)
    requires ValidAddrMemStateOpaque(m) && ValidAddrMemStateOpaque(m');
    requires l1 <= h1 && l2 <= h2;
    requires AddrMemPreservingExcept2(m, m', l1, h1, l2, h2);
    requires h1 < begin_ptr || l1 > begin_ptr + count * WORDSIZE;
    requires h2 < begin_ptr || l2 > begin_ptr + count * WORDSIZE;
    requires count > 0 ==> ValidMemRange(begin_ptr, begin_ptr + count * WORDSIZE);
    decreases count;
    ensures  AddrMemContentsSeq(m, begin_ptr, count) == AddrMemContentsSeq(m', begin_ptr, count);
{
    if count == 0 {
    } else {
        lemma_ValidMemRange_offset_word(begin_ptr, count);
        lemma_AddrMemContentsSeq_framing2(m, m', begin_ptr + WORDSIZE, count - 1, l1, h1, l2, h2);
    }
}

lemma lemma_memset_result(m:memstate, m':memstate, src:word, dst:word, num_words:word)
    requires ValidMemState(m) && ValidMemState(m');
    requires ValidAddrMemStateOpaque(m.addresses) && ValidAddrMemStateOpaque(m'.addresses);
    requires ValidMemRange(dst, dst + num_words * WORDSIZE);
    requires ValidMemRange(src, src + num_words * WORDSIZE);
    requires forall a:addr :: dst <= a < dst + num_words * WORDSIZE
                ==> MemContents(m', a) == MemContents(m, a - dst + src);
    decreases num_words;
    ensures  AddrMemContentsSeq(m'.addresses, dst, num_words) == AddrMemContentsSeq(m.addresses, src, num_words);
{
    if num_words == 0 {
    } else if num_words == 1 {
        calc {
            AddrMemContentsSeq(m'.addresses, dst, num_words);
            [AddrMemContents(m'.addresses, dst)] + [];
            [AddrMemContents(m'.addresses, dst)];
                calc {
                    AddrMemContents(m'.addresses, dst);
                        { reveal_ValidAddrMemStateOpaque(); }
                    m'.addresses[dst];
                    MemContents(m', dst);
                    MemContents(m, src);
                        { reveal_ValidAddrMemStateOpaque(); }
                    m.addresses[src];
                    AddrMemContents(m.addresses, src);
                }
            [AddrMemContents(m.addresses, src)];
            [AddrMemContents(m.addresses, src)] + [];
            AddrMemContentsSeq(m.addresses, src, num_words);
        }
    } else {
        lemma_ValidMemRange_offset_word(dst, num_words);
        lemma_ValidMemRange_offset_word(src, num_words);
        lemma_memset_result(m, m', src + WORDSIZE, dst + WORDSIZE, num_words - 1);
        calc {
            AddrMemContentsSeq(m'.addresses, dst, num_words);
            [AddrMemContents(m'.addresses, dst)] + AddrMemContentsSeq(m'.addresses, dst + WORDSIZE, num_words - 1);
                calc {
                    AddrMemContents(m'.addresses, dst);
                        { reveal_ValidAddrMemStateOpaque(); }
                    m'.addresses[dst];
                    MemContents(m', dst);
                    MemContents(m, src);
                        { reveal_ValidAddrMemStateOpaque(); }
                    m.addresses[src];
                    AddrMemContents(m.addresses, src);
                }
            [AddrMemContents(m.addresses, src)] + AddrMemContentsSeq(m.addresses, src + WORDSIZE, num_words - 1);
            AddrMemContentsSeq(m.addresses, src, num_words);
        }
    }
}
