include "../ARMspartan.dfy"
include "../words_and_bytes.s.dfy"
include "../kom_common.s.dfy"
include "../sha/sha256.i.dfy"
include "../sha/bit-vector-lemmas.i.dfy"
include "../ARMdecls-refined.gen.dfy"

predicate SaneShaGlobal(gm: globalsmap)
{
 ValidGlobalStateOpaque(gm)
 && ValidGlobal(K_SHA256s())
 && SizeOfGlobal(K_SHA256s()) == 4*64
 && isUInt32(AddressOfGlobal(K_SHA256s()) + 4*64) // We won't wrap around while accessing K_SHA256s
 && forall j :: 0 <= j < 64 ==> GlobalContents(gm, K_SHA256s(), AddressOfGlobal(K_SHA256s()) + j*4) == K_SHA256(j)
}

predicate BlockInvariant(
            trace:SHA256Trace, input:seq<word>, globals:globalsmap,
            old_M_len:nat, old_mem:memmap, mem:memmap, sp:word, lr:word, r1:word, r12:word,
            a:word, b:word, c:word, d:word, e:word, f:word, g:word, h:word,
            input_ptr:word, ctx_ptr:word,             
            num_blocks:nat, block:nat)            
{
    ValidAddrMemStateOpaque(old_mem)
 && ValidAddrMemStateOpaque(mem)
 // Stack is accessible
 && ValidAddrs(sp, 19)

 // Pointer into our in-memory H[8] is valid
 && ctx_ptr == AddrMemContents(mem, sp + 16 * 4)
 && (ctx_ptr + 32 < sp || ctx_ptr > sp + 19 * 4)
 && ValidAddrs(ctx_ptr, 8)

 // Input properties
 && block <= num_blocks
 && SeqLength(input) == num_blocks*16
 && r1 == input_ptr + block * 16 * 4
 && input_ptr + num_blocks * 16 * 4 == AddrMemContents(mem, sp + 18*4) == r12
 && input_ptr + num_blocks * 16 * 4 < 0x1_0000_0000
 && (input_ptr + num_blocks * 16 * 4 < sp || sp + 19 * 4 <= input_ptr)  // Doesn't alias sp
 && (input_ptr + num_blocks * 16 * 4 < ctx_ptr || ctx_ptr + 32 <= input_ptr)  // Doesn't alias input_ptr
 && ValidAddrs(input_ptr, num_blocks * 16)
 && (forall j {:trigger ValidMem(input_ptr + j * 4)} :: 0 <= j < num_blocks * 16 ==> AddrMemContents(mem, input_ptr + j * 4) == input[j])

 // Trace properties
 && IsCompleteSHA256Trace(trace)
 && SHA256TraceIsCorrect(trace) 
 && |trace.M| == old_M_len + block
 && (forall i :: 0 <= i < block 
             ==> trace.M[old_M_len + i] == bswap32_seq(input[i*16..(i+1)*16])) 

 // Globals properties
 && SaneShaGlobal(globals)
 && ValidGlobalAddr(K_SHA256s(), lr) 
 && lr == AddressOfGlobal(K_SHA256s()) 

 // Hs match memory and our registers
 && last(trace.H)[0] == AddrMemContents(mem, ctx_ptr + 0 * 4) == a 
 && last(trace.H)[1] == AddrMemContents(mem, ctx_ptr + 1 * 4) == b 
 && last(trace.H)[2] == AddrMemContents(mem, ctx_ptr + 2 * 4) == c 
 && last(trace.H)[3] == AddrMemContents(mem, ctx_ptr + 3 * 4) == d 
 && last(trace.H)[4] == AddrMemContents(mem, ctx_ptr + 4 * 4) == e 
 && last(trace.H)[5] == AddrMemContents(mem, ctx_ptr + 5 * 4) == f 
 && last(trace.H)[6] == AddrMemContents(mem, ctx_ptr + 6 * 4) == g 
 && last(trace.H)[7] == AddrMemContents(mem, ctx_ptr + 7 * 4) == h 

 // Memory framing:  We only touch the stack and 8 bytes pointed to by ctx_ptr
 && (forall addr:word :: ValidMem(addr) && (addr < sp || addr >= sp + 19 * 4) 
                                         && (addr < ctx_ptr || addr >= ctx_ptr + 8 * 4) 
                     ==> AddrMemContents(old_mem, addr) == AddrMemContents(mem, addr))
}
