include "../ARMdef.s.dfy"
include "../valesupp.i.dfy"
include "../kom_common.i.dfy"
include "sha256-invariants.i.dfy"

lemma lemma_AddrMemContentsSeq_adds(m:memmap, begin_ptr:nat, count:nat, count':nat)
  requires ValidAddrMemStateOpaque(m);
  requires count > 0 ==> ValidMemWords(begin_ptr, count);
  requires count' < count;
  decreases count;
  ensures  count - count' > 0 ==> ValidMemWords(WordOffset(begin_ptr, count'), count - count');
  ensures  AddrMemContentsSeq(m, begin_ptr, count) == AddrMemContentsSeq(m, begin_ptr, count') 
                                                    + AddrMemContentsSeq(m, WordOffset(begin_ptr, count'), count - count')
{
    if count' == 0 {
    } else {
        reveal WordAligned();
        lemma_AddrMemContentsSeq_adds(m, WordOffset(begin_ptr, 1), count - 1, count' - 1);
    }
}

lemma lemma_ValidMemRange_offset_word(base:int, count:nat)
    requires ValidMemWords(base, count);
    ensures  count > 1 ==> ValidMemWords(WordOffset(base, 1), count - 1);
{}

lemma lemma_ValidMemRange_reduced(base:int, count:nat, count':nat)
    requires ValidMemWords(base, count);
    requires count' < count;
    ensures  ValidMemWords(base, count - count');
{
    if count' == 0 {
    } else {
        var offset := WordOffset(base, count');
        var limit := WordOffset(base, 1 + count - count');
        lemma_ValidMemRange_offset(base, count, count' - 1);
        assert ValidMemWords(base, count - count' + 1);
    }
}

lemma lemma_ValidMemRange_offset(base:int, count:nat, count':nat)
    requires ValidMemWords(base, count);
    requires count' < count;
    ensures  ValidMemWords(WordOffset(base, count'), count - count');
    ensures  ValidMemRange(WordOffset(base, count'), WordOffset(base, count));
{
    if count' == 0 {
    } else {
        var offset := WordOffset(base, count');
        var limit := WordOffset(base, 1 + count - count');
        lemma_ValidMemRange_offset(base, count, count' - 1);
        //assert ValidMemRange(base + (count' - 1)*WORDSIZE, base + (count - count' + 1) * WORDSIZE);
        lemma_ValidMemRange_offset_word(WordOffset(base, count' - 1), count - count' + 1);
    }
}

function {:opaque} AddrMemContentsSeq(m:memmap, begin_ptr:nat, count:nat) : seq<word>
  requires ValidAddrMemStateOpaque(m);
  requires count > 0 ==> ValidMemWords(begin_ptr, count);
  decreases count;
  ensures  |AddrMemContentsSeq(m, begin_ptr, count)| == count;
  ensures  forall i :: 0 <= i < count ==> AddrMemContents(m, WordOffset(begin_ptr, i)) == AddrMemContentsSeq(m, begin_ptr, count)[i];
{
  if count == 0 then []
  else
      lemma_ValidMemRange_offset_word(begin_ptr, count);
      [AddrMemContents(m, begin_ptr)] + AddrMemContentsSeq(m, WordOffset(begin_ptr, 1), count - 1)
}

lemma lemma_MemPreservingExcept_implies_AddrMemPreservingExcept(s:state, r:state, base:nat, limit:nat)
    requires ValidState(s) && ValidState(r);
    requires limit >= base;
    requires MemPreservingExcept(s, r, base, limit);
    requires ValidAddrMemStateOpaque(s.m.addresses) && ValidAddrMemStateOpaque(r.m.addresses);
    ensures  AddrMemPreservingExcept(s.m.addresses, r.m.addresses, base, limit);
{
}

lemma lemma_ParentStackPreserving_implies_AddrMemPreservingExcept(s:state, r:state)
    requires ValidState(s) && ValidState(r) && SaneConstants();
    requires ParentStackPreserving(s, r);
    requires NonStackMemPreserving(s, r);
    requires ValidAddrMemStateOpaque(s.m.addresses) && ValidAddrMemStateOpaque(r.m.addresses);
    ensures  SP(Monitor) in s.regs;
    ensures  AddrMemPreservingExcept(s.m.addresses, r.m.addresses, StackLimit(), s.regs[SP(Monitor)]);
{
    lemma_MemPreservingExcept_implies_AddrMemPreservingExcept(s, r, StackLimit(), StackBase());
    assert AddrMemPreservingExcept(s.m.addresses, r.m.addresses, StackLimit(), StackBase());

    forall a:addr | ValidMem(a) && !(StackLimit() <= a < s.regs[SP(Monitor)])
        ensures AddrMemContents(s.m.addresses, a) == AddrMemContents(r.m.addresses, a)
    {
        if a < StackLimit() {
        } else {
            //assert a >= s.regs[SP(Monitor)];
            if a < StackBase() {
                assert MemContents(s.m, a) == MemContents(r.m, a);      // OBSERVE
            } else {
            }
        }
    }
}

lemma lemma_AddrMemPreservingExcept3_hierarchy(m:memmap, m':memmap, 
                                               l1:nat, h1:nat, 
                                               l1':nat, h1':nat, 
                                               l2:nat, h2:nat, 
                                               l3:nat, h3:nat)
    requires ValidAddrMemStateOpaque(m) && ValidAddrMemStateOpaque(m');
    requires l1 <= h1 && l2 <= h2 && l3 <= h3;
    requires l1' <= l1 && h1 <= h1';
    requires AddrMemPreservingExcept3(m, m', l1, h1, l2, h2, l3, h3);
    ensures  AddrMemPreservingExcept3(m, m', l1', h1', l2, h2, l3, h3);
{
}

lemma lemma_AddrMemPreservingExcept3_condensed(m:memmap, m':memmap, 
                                               l1:nat, h1:nat, 
                                               l2:nat, h2:nat, 
                                               l3:nat, h3:nat)
    requires ValidAddrMemStateOpaque(m) && ValidAddrMemStateOpaque(m');
    requires l1 <= h1 <= l2 <= h2 <= l3 <= h3;
    requires AddrMemPreservingExcept3(m, m', l1, h1, l2, h2, l3, h3);
    ensures  AddrMemPreservingExcept(m, m', l1, h3);
{
}

lemma lemma_AddrMemContentsSeq_framing1(m:memmap, m':memmap, begin_ptr:addr, count:nat, l1:nat, h1:nat)
    requires ValidAddrMemStateOpaque(m) && ValidAddrMemStateOpaque(m');
    requires l1 <= h1;
    requires AddrMemPreservingExcept(m, m', l1, h1);
    requires count > 0 ==> ValidMemWords(begin_ptr, count);
    requires h1 <= begin_ptr || l1 >= WordOffset(begin_ptr, count);
    decreases count;
    ensures  AddrMemContentsSeq(m, begin_ptr, count) == AddrMemContentsSeq(m', begin_ptr, count);
{
    if count != 0 {
        lemma_ValidMemRange_offset_word(begin_ptr, count);
        lemma_AddrMemContentsSeq_framing1(m, m', WordOffset(begin_ptr, 1), count - 1, l1, h1);
    }
}

lemma lemma_AddrMemContentsSeq_framing2(m:memmap, m':memmap, begin_ptr:addr, count:nat, l1:nat, h1:nat, l2:nat, h2:nat)
    requires ValidAddrMemStateOpaque(m) && ValidAddrMemStateOpaque(m');
    requires l1 <= h1 && l2 <= h2;
    requires AddrMemPreservingExcept2(m, m', l1, h1, l2, h2);
    requires count > 0 ==> ValidMemWords(begin_ptr, count);
    requires h1 < begin_ptr || l1 > WordOffset(begin_ptr, count);
    requires h2 < begin_ptr || l2 > WordOffset(begin_ptr, count);
    decreases count;
    ensures  AddrMemContentsSeq(m, begin_ptr, count) == AddrMemContentsSeq(m', begin_ptr, count);
{
    if count != 0 {
        lemma_ValidMemRange_offset_word(begin_ptr, count);
        lemma_AddrMemContentsSeq_framing2(m, m', WordOffset(begin_ptr, 1), count - 1, l1, h1, l2, h2);
    }
}

lemma lemma_AddrMemContentsSeq_framing3(m:memmap, m':memmap, begin_ptr:addr, count:nat, 
                                        l1:nat, h1:nat, 
                                        l2:nat, h2:nat, 
                                        l3:nat, h3:nat)
    requires ValidAddrMemStateOpaque(m) && ValidAddrMemStateOpaque(m');
    requires l1 <= h1 && l2 <= h2 && l3 <= h3;
    requires AddrMemPreservingExcept3(m, m', l1, h1, l2, h2, l3, h3);
    requires count > 0 ==> ValidMemWords(begin_ptr, count);
    requires h1 < begin_ptr || l1 > WordOffset(begin_ptr, count);
    requires h2 < begin_ptr || l2 > WordOffset(begin_ptr, count);
    requires h3 <= begin_ptr || l3 >= WordOffset(begin_ptr, count);
    decreases count;
    ensures  AddrMemContentsSeq(m, begin_ptr, count) == AddrMemContentsSeq(m', begin_ptr, count);
{
    if count != 0 {
        lemma_ValidMemRange_offset_word(begin_ptr, count);
        lemma_AddrMemContentsSeq_framing3(m, m', WordOffset(begin_ptr, 1), count - 1, l1, h1, l2, h2, l3, h3);
    }
}

lemma lemma_memset_result(m:memstate, m':memstate, src:word, dst:word, num_words:word)
    requires ValidMemState(m) && ValidMemState(m');
    requires ValidAddrMemStateOpaque(m.addresses) && ValidAddrMemStateOpaque(m'.addresses);
    requires ValidMemWords(dst, num_words);
    requires ValidMemWords(src, num_words);
    requires forall a:addr :: dst <= a < WordOffset(dst, num_words)
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
                        { reveal ValidAddrMemStateOpaque(); }
                    m'.addresses[dst];
                    MemContents(m', dst);
                    MemContents(m, src);
                        { reveal ValidAddrMemStateOpaque(); }
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
        lemma_memset_result(m, m', WordOffset(src, 1), WordOffset(dst, 1), num_words - 1);
        calc {
            AddrMemContentsSeq(m'.addresses, dst, num_words);
            [AddrMemContents(m'.addresses, dst)] + AddrMemContentsSeq(m'.addresses, dst + WORDSIZE, num_words - 1);
                calc {
                    AddrMemContents(m'.addresses, dst);
                        { reveal ValidAddrMemStateOpaque(); }
                    m'.addresses[dst];
                    MemContents(m', dst);
                    MemContents(m, src);
                        { reveal ValidAddrMemStateOpaque(); }
                    m.addresses[src];
                    AddrMemContents(m.addresses, src);
                }
            [AddrMemContents(m.addresses, src)] + AddrMemContentsSeq(m.addresses, src + WORDSIZE, num_words - 1);
            AddrMemContentsSeq(m.addresses, src, num_words);
        }
    }
}

lemma {:fuel AddrMemContentsSeq,9} lemma_package_hash_result(m:memmap, base:word, s:seq<word>)
    requires ValidAddrMemStateOpaque(m);
    requires ValidMemWords(base, SHA_CTXSIZE);
    requires s == [ AddrMemContents(m, WordOffset(base, 0)),
                    AddrMemContents(m, WordOffset(base, 1)),
                    AddrMemContents(m, WordOffset(base, 2)),
                    AddrMemContents(m, WordOffset(base, 3)),
                    AddrMemContents(m, WordOffset(base, 4)),
                    AddrMemContents(m, WordOffset(base, 5)),
                    AddrMemContents(m, WordOffset(base, 6)),
                    AddrMemContents(m, WordOffset(base, 7)) ];
    ensures  s == AddrMemContentsSeq(m, base, SHA_CTXSIZE);
{}
