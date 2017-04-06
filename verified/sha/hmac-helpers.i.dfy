include "memory-helpers.i.dfy"

lemma lemma_apply_opad_complete(m:memmap, m':memmap, base:nat, count:nat)
    requires ValidAddrMemStateOpaque(m) && ValidAddrMemStateOpaque(m');
    requires count > 0 ==> ValidMemRange(base, base + count * WORDSIZE);
    requires forall a :: base <= a < base + count * WORDSIZE && WordAligned(a) 
                     ==> AddrMemContents(m', a) == BitwiseXor(AddrMemContents(m, a), 0x5c5c5c5c); 
    ensures  AddrMemContentsSeq(m', base, count) == 
      SeqXor(AddrMemContentsSeq(m, base, count), Opad(count));

{
  if count == 0 {
	} else {
		lemma_ValidMemRange_offset(base, count);
		lemma_apply_opad_complete(m, m', base, count - 1);
	}
}


lemma lemma_apply_ipad_complete(m:memmap, m':memmap, base:nat, count:nat)
    requires ValidAddrMemStateOpaque(m) && ValidAddrMemStateOpaque(m');
    requires count > 0 ==> ValidMemRange(base, base + count * WORDSIZE);
    requires forall a :: base <= a < base + count * WORDSIZE && WordAligned(a) 
                     ==> AddrMemContents(m', a) == BitwiseXor(AddrMemContents(m, a), 0x36363636); 
    ensures  AddrMemContentsSeq(m', base, count) == 
      SeqXor(AddrMemContentsSeq(m, base, count), Ipad(count));

{
  if count == 0 {
	} else {
		lemma_ValidMemRange_offset(base, count);
		lemma_apply_ipad_complete(m, m', base, count - 1);
	}
}
