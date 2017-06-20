include "../valesupp.i.dfy"
include "../words_and_bytes.s.dfy"
include "../kom_common.s.dfy"
include "../sha/sha256.i.dfy"
include "../sha/bit-vector-lemmas.i.dfy"

const K_SHA256_BYTES:int := K_SHA256_WORDS * WORDSIZE;

predicate {:opaque} SaneShaGlobal(gm: globalsmap)
    ensures SaneShaGlobal(gm) ==> ValidGlobal(K_SHA256s())
{
 ValidGlobalStateOpaque(gm)
 && ValidGlobal(K_SHA256s())
 && SizeOfGlobal(K_SHA256s()) == K_SHA256_BYTES
 && isUInt32(AddressOfGlobal(K_SHA256s()) + K_SHA256_BYTES) // We won't wrap around while accessing K_SHA256s
 && forall j :: 0 <= j < K_SHA256_WORDS ==> GlobalContents(gm, K_SHA256s(), AddressOfGlobal(K_SHA256s()) + WordsToBytes(j)) == K_SHA256(j)
}

predicate AddrMemPreservingExcept(sm:memmap, rm:memmap, base:int, limit:int)
    requires ValidAddrMemStateOpaque(sm) && ValidAddrMemStateOpaque(rm);
    requires limit >= base;
{
    forall a:addr :: ValidMem(a) && !(base <= a < limit)
        ==> AddrMemContents(sm, a) == AddrMemContents(rm, a)
}

predicate AddrMemPreservingExcept2(sm:memmap, rm:memmap, base1:int, limit1:int, base2:int, limit2:int)
    requires ValidAddrMemStateOpaque(sm) && ValidAddrMemStateOpaque(rm);
    requires limit1 >= base1 && limit2 >= base2;
{
    forall a:addr :: ValidMem(a) && !(base1 <= a < limit1) && !(base2 <= a < limit2)
        ==> AddrMemContents(sm, a) == AddrMemContents(rm, a)
}

predicate AddrMemPreservingExcept3(sm:memmap, rm:memmap, 
                                   base1:int, limit1:int, 
                                   base2:int, limit2:int,
                                   base3:int, limit3:int)
    requires ValidAddrMemStateOpaque(sm) && ValidAddrMemStateOpaque(rm);
    requires limit1 >= base1 && limit2 >= base2 && limit3 >= base3;
{
    forall a:addr :: ValidMem(a) && !(base1 <= a < limit1) && !(base2 <= a < limit2) && !(base3 <= a < limit3)
        ==> AddrMemContents(sm, a) == AddrMemContents(rm, a)
}

const SHA_CTXSIZE:int := 8; // 8 words
const SHA_STACKSIZE:int := 19; // 19 words on the stack

predicate BlockInvariant(
            trace:SHA256Trace, old_trace:SHA256Trace, input:seq<word>, globals:globalsmap,
            old_M_len:nat, old_mem:memmap, mem:memmap, sp:word, lr:word, r1:word, r12:word,
            a:word, b:word, c:word, d:word, e:word, f:word, g:word, h:word,
            input_ptr:word, ctx_ptr:word,             
            num_blocks:nat, block:nat)            
{
    ValidAddrMemStateOpaque(old_mem)
 && ValidAddrMemStateOpaque(mem)
 // Stack is accessible
 && SaneStackPointer(sp)
 && ValidMemRange(sp, WordOffset(sp, SHA_STACKSIZE))

 // Pointer into our in-memory H[8] is valid
 && ctx_ptr == AddrMemContents(mem, WordOffset(sp, SHA_BLOCKSIZE))
 && WordAligned(ctx_ptr) && isUInt32(ctx_ptr + WordsToBytes(SHA_CTXSIZE))
 && (WordOffset(ctx_ptr, SHA_CTXSIZE) < sp || ctx_ptr > WordOffset(sp, SHA_STACKSIZE))
 && ValidMemRange(ctx_ptr, WordOffset(ctx_ptr, SHA_CTXSIZE))

 // Input properties
 && block <= num_blocks
 && SeqLength(input) == num_blocks * SHA_BLOCKSIZE
 && WordAligned(input_ptr) && isUInt32(input_ptr + WordsToBytes(num_blocks * SHA_BLOCKSIZE))
 && r1 == WordOffset(input_ptr, block * SHA_BLOCKSIZE)
 && WordOffset(input_ptr, num_blocks * SHA_BLOCKSIZE) == AddrMemContents(mem, WordOffset(sp, 18)) == r12
 && (WordOffset(input_ptr, num_blocks * SHA_BLOCKSIZE) < sp || WordOffset(sp, SHA_STACKSIZE) <= input_ptr)  // Doesn't alias sp
 && (WordOffset(input_ptr, num_blocks * SHA_BLOCKSIZE) < ctx_ptr || WordOffset(ctx_ptr, SHA_CTXSIZE) <= input_ptr)  // Doesn't alias input_ptr
 && ValidMemRange(input_ptr, WordOffset(input_ptr, num_blocks * SHA_BLOCKSIZE))
// && (forall j {:trigger ValidMem(input_ptr + j * WORDSIZE)} :: 0 <= j < num_blocks * SHA_BLOCKSIZE
//    ==> AddrMemContents(mem, input_ptr + j * WORDSIZE) == input[j])
 && (forall j:int :: 0 <= j < num_blocks * SHA_BLOCKSIZE
    ==> AddrMemContents(mem, WordOffset(input_ptr, j)) == input[j])

 // Trace properties
 && IsCompleteSHA256Trace(trace)
 && SHA256TraceIsCorrect(trace) 
 && |old_trace.M| <= |trace.M|
 && old_trace.M == trace.M[0..|old_trace.M|]  // old_trace.M is a prefix of trace.M
 && |trace.M| == old_M_len + block
 && (forall i :: 0 <= i < block 
             ==> trace.M[old_M_len + i] == input[i*16..(i+1)*16]) 

 // Globals properties
 && SaneShaGlobal(globals)
 && lr == AddressOfGlobal(K_SHA256s()) 

 // Hs match memory and our registers
 && last(trace.H)[0] == AddrMemContents(mem, WordOffset(ctx_ptr, 0)) == a 
 && last(trace.H)[1] == AddrMemContents(mem, WordOffset(ctx_ptr, 1)) == b 
 && last(trace.H)[2] == AddrMemContents(mem, WordOffset(ctx_ptr, 2)) == c 
 && last(trace.H)[3] == AddrMemContents(mem, WordOffset(ctx_ptr, 3)) == d 
 && last(trace.H)[4] == AddrMemContents(mem, WordOffset(ctx_ptr, 4)) == e 
 && last(trace.H)[5] == AddrMemContents(mem, WordOffset(ctx_ptr, 5)) == f 
 && last(trace.H)[6] == AddrMemContents(mem, WordOffset(ctx_ptr, 6)) == g 
 && last(trace.H)[7] == AddrMemContents(mem, WordOffset(ctx_ptr, 7)) == h 

 // Memory framing:  We only touch the stack and 8 words pointed to by ctx_ptr
 && AddrMemPreservingExcept2(old_mem, mem, sp, WordOffset(sp, SHA_STACKSIZE), ctx_ptr,
                            WordOffset(ctx_ptr, SHA_CTXSIZE))
}
