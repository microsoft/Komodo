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
    requires l <= r
    ensures |addrRangeSeq(l, r)| == BytesToWords(r-l)
    ensures forall i | 0 <= i < BytesToWords(r-l) ::
        addrRangeSeq(l, r)[i] == l + WordsToBytes(i)
    //ensures forall a: addr :: l <= a <= r <==> a in addrRangeSeq(l, r)
    decreases r-l
{
    assert l+WORDSIZE > l;
    assert r - (l+WORDSIZE) < r - l;
    if l == r then [] else [l] + addrRangeSeq(l+WORDSIZE,r)
}

function addrsInPhysPage(physPage: word, base: addr) : seq<addr>
    requires physPageIsInsecureRam(physPage)
    requires base == physPage * PAGESIZE + KOM_DIRECTMAP_VBASE
    requires SaneConstants()
    ensures forall a : addr | a in addrsInPhysPage(physPage, base) :: ValidMem(a)
{
    reveal_PageAligned(); // why?
    addrRangeSeq(base, base+PAGESIZE)
}

function addrsInPage(page: PageNr, base: addr) : seq<addr>
    requires base == page_monvaddr(page)
    requires SaneConstants()
    ensures forall a : addr | a in addrsInPage(page, base) :: ValidMem(a)
{
    addrRangeSeq(base, base+PAGESIZE)
}

function {:opaque} addrSeqToContents(s:seq<addr>, ms:memstate) : seq<word>
    requires ValidMemState(ms)
    requires forall a : addr | a in s :: ValidMem(a)
    ensures |addrSeqToContents(s, ms)| == |s|
    ensures forall i | 0 <= i < |s| :: addrSeqToContents(s, ms)[i] == MemContents(ms, s[i])
{
   if |s| == 0 then []
   else [MemContents(ms, s[0])] + addrSeqToContents(s[1..], ms)
}
