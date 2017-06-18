//-----------------------------------------------------------------------------
// Core types (for a 32-bit word-aligned machine)
//-----------------------------------------------------------------------------

const UINT32_LIM:int := 0x1_0000_0000;
const WORDSIZE:int := 4;
predicate isUInt32(i:int) { 0 <= i < UINT32_LIM }
type word = x | isUInt32(x)

predicate {:opaque} WordAligned(i:int) { i % WORDSIZE == 0 }

type addr = x | (reveal WordAligned(); isUInt32(x) && WordAligned(x))

function method WordsToBytes(w:int): int
    ensures WordAligned(WordsToBytes(w))
{ reveal WordAligned(); WORDSIZE * w }

function method BytesToWords(b:int): int
    requires WordAligned(b)
{ reveal WordAligned(); b / WORDSIZE }

function {:opaque} TruncateWord(x:int): word
{ x % UINT32_LIM }

function method WordOffset(a:addr, i:int): addr
    requires isUInt32(a + WordsToBytes(i))
    ensures WordAligned(WordOffset(a, i))
{ a + WordsToBytes(i) }

const PAGESIZE:int := 0x1000;
const PAGEBITS:int := 12;

predicate {:opaque} PageAligned(addr:int)
    requires addr >= 0
    ensures PageAligned(addr) ==> WordAligned(addr)
{
    if addr % PAGESIZE == 0
    then lemma_PageAlignedImpliesWordAligned(addr); true
    else false
}

lemma lemma_PageAlignedImplies1KAligned(addr:int)
    requires addr >= 0 && addr % 0x1000 == 0
    ensures addr % 0x400 == 0
{ assert 0x1000 % 0x400 == 0; }

lemma lemma_1KAlignedImpliesWordAligned(addr:int)
    requires addr >= 0 && addr % 0x400 == 0
    ensures WordAligned(addr)
{
    calc {
        true;
        addr % 0x400 == 0;
        addr % 0x200 == 0;
        addr % 0x100 == 0;
        addr % 0x80 == 0;
        addr % 0x40 == 0;
        addr % 0x20 == 0;
        addr % 0x10 == 0;
        addr % 8 == 0;
        addr % 4 == 0;
        { reveal WordAligned(); }
        WordAligned(addr);
    }
}

lemma lemma_PageAlignedImpliesWordAligned(addr:int)
    requires addr >= 0 && addr % 0x1000 == 0
    ensures WordAligned(addr)
{
    lemma_PageAlignedImplies1KAligned(addr);
    lemma_1KAlignedImpliesWordAligned(addr);
}

function WordAlignedAdd(x1:int, x2:int): int
    requires WordAligned(x1) && WordAligned(x2)
    ensures  WordAligned(WordAlignedAdd(x1, x2))
{
    reveal WordAligned();
    x1 + x2
}

function WordAlignedSub(x1:int, x2:int): int
    requires WordAligned(x1) && WordAligned(x2)
    ensures  WordAligned(WordAlignedSub(x1, x2))
{
    reveal WordAligned();
    x1 - x2
}
