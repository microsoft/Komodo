include "../ARMspartan.dfy"
include "../words_and_bytes.s.dfy"
include "../kom_common.s.dfy"
include "../sha/sha256.i.dfy"
include "../sha/bit-vector-lemmas.i.dfy"
include "../ARMdecls.gen.dfy"

module sha256_refined_invariants_i {

import opened sha256_refined_invariants_i_ARMspartan = ARMspartan 
import opened sha256_refined_invariants_i_words_and_bytes_s = words_and_bytes_s 
import opened sha256_refined_invariants_i_kom_common_s = kom_common_s 
import opened sha256_refined_invariants_i_sha256_i = sha256_i
import opened sha256_refined_invariants_i_bit_vector_lemmas_i = bit_vector_lemmas_i
import opened sha256_refined_invariants_i_ARMdecls = ARMdecls 


predicate BlockInvariant(
            trace:SHA256Trace, input:seq<word>, globals:map<operand, seq<word>>,
            mem:memmap, sp:word, lr:word, r1:word,
            a:word, b:word, c:word, d:word, e:word, f:word, g:word, h:word,
            input_ptr:word, ctx_ptr:word,             
            num_blocks:nat, block:nat)
{
 // Stack is accessible
    (forall j {:trigger ValidAddr(mem, sp + j * 4)} {:trigger sp + j * 4 in mem} :: 
               0 <= j < 19 ==> ValidAddr(mem, sp + j * 4))

 // Pointer into our in-memory H[8] is valid
 && ctx_ptr == mem[sp + 16 * 4]
 && (ctx_ptr + 32 < sp || ctx_ptr > sp + 19 * 4)
 && (forall addr{:trigger ValidAddr(mem, addr)} {:trigger addr in mem} :: 
             ctx_ptr <= addr < ctx_ptr + 8 * 4
          && (addr - ctx_ptr) % 4 == 0 
          ==> ValidAddr(mem, addr))

 // Input properties
 && block <= num_blocks
 && SeqLength(input) == num_blocks*16
 && r1 == input_ptr + block * 16 * 4
 && input_ptr + num_blocks * 16 * 4 == mem[sp + 18*4]
 && input_ptr + num_blocks * 16 * 4 < 0x1_0000_0000
 && (input_ptr + num_blocks * 16 * 4 < sp || sp + 19 * 4 <= input_ptr)  // Doesn't alias sp
 && (input_ptr + num_blocks * 16 * 4 < ctx_ptr || ctx_ptr + 32 <= input_ptr)  // Doesn't alias input_ptr
 && (forall j {:trigger ValidAddr(mem, input_ptr + j * 4)} {:trigger input_ptr + j * 4 in mem} ::
            0 <= j < num_blocks * 16 ==> ValidAddr(mem, input_ptr + j * 4) 
                                      && mem[input_ptr + j * 4] == input[j])

 // Trace properties
 && IsCompleteSHA256Trace(trace)
 && SHA256TraceIsCorrect(trace) 
 && |trace.M| >= block
 && (forall i :: 0 <= i < block 
             ==> trace.M[|trace.M| - block + i] == bswap32_seq(input[i*16..(i+1)*16])) 

 // Globals properties
 && ValidGlobalsAddr(globals, K_SHA256s().sym, lr) 
 && K_SHA256s() in globals
 && AddressOfGlobal(K_SHA256s()) + 256 < 0x1_0000_0000 
 && lr == AddressOfGlobal(K_SHA256s()) 
 && SeqLength(globals[K_SHA256s()]) == 256
 && (forall j :: 0 <= j < 64 ==> globals[K_SHA256s()][j] == K_SHA256(j))

 // Hs match memory and our registers
 && last(trace.H)[0] == mem[ctx_ptr + 0 * 4] == a 
 && last(trace.H)[1] == mem[ctx_ptr + 1 * 4] == b 
 && last(trace.H)[2] == mem[ctx_ptr + 2 * 4] == c 
 && last(trace.H)[3] == mem[ctx_ptr + 3 * 4] == d 
 && last(trace.H)[4] == mem[ctx_ptr + 4 * 4] == e 
 && last(trace.H)[5] == mem[ctx_ptr + 5 * 4] == f 
 && last(trace.H)[6] == mem[ctx_ptr + 6 * 4] == g 
 && last(trace.H)[7] == mem[ctx_ptr + 7 * 4] == h 

 // Memory framing:  We only touch the stack and 8 bytes pointed to by ctx_ptr
 && (forall addr:word :: addr in mem && (addr < sp || addr >= sp + 19 * 4) 
                                     && (addr < ctx_ptr || addr >= ctx_ptr + 8 * 4) 
                     ==> addr in mem && mem[addr] == mem[addr])
}


}
