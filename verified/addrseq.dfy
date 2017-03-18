include "kom_common.s.dfy"
include "pagedb.s.dfy"

// I spent a lot of time trying to use the things in Seq.dfy, but because of 
// the requirements pertaining to addresses (e.g., they have to be in 
// TheValidAddresses and have to be word-aligned) I needed to special case 
// everything so that I could use preconditions/postconditions that deal with 
// these sorts of things.

// Proving termination for this thing seems very finicky
// so this stuff is in its own file.

function {:opaque} addrRangeSeq(l: addr, r: addr) : seq<addr>
    requires isUInt32(l) && WordAligned(l) &&
        isUInt32(r) && WordAligned(r)
    requires l <= r
    ensures |addrRangeSeq(l, r)| == (r-l) / WORDSIZE
    ensures forall i | 0 <= i < (r-l) / WORDSIZE ::
        addrRangeSeq(l, r)[i] == l + i * WORDSIZE
    //ensures forall a: addr :: l <= a <= r <==>
    //    a in addrRangeSeq(l, r)
    decreases r-l
{
    assert l+WORDSIZE > l;
    assert r - (l+WORDSIZE) < r - l;
    if l == r then [] else [l] + addrRangeSeq(l+WORDSIZE,r)
}

// FIXME: make this true via kom_common.s, not as an axiom!
predicate {:axiom} insecurePagesAreValid(physPage: word, base: addr)
    requires physPageIsInsecureRam(physPage)
    requires base == physPage * PAGESIZE + KOM_DIRECTMAP_VBASE
    ensures forall a : addr | base <= a <= base + PAGESIZE ::
        a in TheValidAddresses()

function addrsInPhysPage(physPage: word, base: addr) : seq<addr>
    requires physPageIsInsecureRam(physPage)
    requires base == physPage * PAGESIZE + KOM_DIRECTMAP_VBASE
    ensures forall a : addr | a in addrsInPhysPage(physPage, base) ::
        a in TheValidAddresses()
{
    // Not sure why I have to assume an axiom and can't assert it.
    // FIXME
    assume insecurePagesAreValid(physPage, base);
    addrRangeSeq(base,base+PAGESIZE)
}

function addrsInPage(page: PageNr, base: addr) : seq<addr>
    requires base == page_monvaddr(page)
    requires SaneConstants()
    ensures forall a : addr | a in addrsInPage(page, base) :: a in TheValidAddresses()
{
    addrRangeSeq(base, base+PAGESIZE)
}

function {:opaque} addrSeqToContents(s:seq<addr>, mem:memmap) : seq<word>
    requires ValidAddrMemState(mem)
    requires forall a : addr | a in s :: a in TheValidAddresses()
    ensures |addrSeqToContents(s,mem)| == |s|
{
   if |s| == 0 then []
   else [mem[s[0]]] + addrSeqToContents(s[1..], mem)
}
