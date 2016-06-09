include "sha256.i.dfy"
include "ARMspartan.dfy"
include "ARMprint.dfy"

function sp_code_ComputeOneStep_SHA256_spartan_part1(K:int, W:sp_operand):code
{
  sp_Block(sp_CCons(sp_code_Mov32(var_eax(), stack(0)), sp_CCons(sp_code_Mov32(stack(9), var_eax()), sp_CCons(sp_code_Mov32(var_ebx(), stack(1)), sp_CCons(sp_code_Mov32(stack(10), var_ebx()), sp_CCons(sp_code_Mov32(var_ecx(), stack(2)), sp_CCons(sp_code_Mov32(stack(11), var_ecx()), sp_CCons(sp_code_Mov32(var_edx(), var_ebx()), sp_CCons(sp_code_And32(var_ebx(), var_eax()), sp_CCons(sp_code_And32(var_edx(), var_ecx()), sp_CCons(sp_code_And32(var_ecx(), var_eax()), sp_CCons(sp_code_Xor32(var_ebx(), var_ecx()), sp_CCons(sp_code_Xor32(var_ebx(), var_edx()), sp_CCons(sp_code_Mov32(var_ecx(), var_eax()), sp_CCons(sp_code_Mov32(var_edx(), var_eax()), sp_CCons(sp_code_Ror32(var_eax(), sp_op_const(2)), sp_CCons(sp_code_Ror32(var_ecx(), sp_op_const(13)), sp_CCons(sp_code_Xor32(var_eax(), var_ecx()), sp_CCons(sp_code_Ror32(var_edx(), sp_op_const(22)), sp_CCons(sp_code_Xor32(var_eax(), var_edx()), sp_CCons(sp_code_Add32Wrap(var_eax(), var_ebx()), sp_CNil())))))))))))))))))))))
}

function sp_code_ComputeOneStep_SHA256_spartan_part2(K:int, W:sp_operand):code
{
  sp_Block(sp_CCons(sp_code_Mov32(var_ebx(), stack(4)), sp_CCons(sp_code_Mov32(stack(13), var_ebx()), sp_CCons(sp_code_Mov32(var_edx(), var_ebx()), sp_CCons(sp_code_Not32(var_edx()), sp_CCons(sp_code_Mov32(var_ecx(), stack(6)), sp_CCons(sp_code_Mov32(stack(15), var_ecx()), sp_CCons(sp_code_And32(var_edx(), var_ecx()), sp_CCons(sp_code_Mov32(var_ecx(), stack(5)), sp_CCons(sp_code_Mov32(stack(14), var_ecx()), sp_CCons(sp_code_And32(var_ecx(), var_ebx()), sp_CCons(sp_code_Xor32(var_ecx(), var_edx()), sp_CCons(sp_code_Mov32(var_edx(), var_ebx()), sp_CCons(sp_code_Mov32(var_edi(), var_ebx()), sp_CCons(sp_code_Ror32(var_edx(), sp_op_const(6)), sp_CCons(sp_code_Ror32(var_edi(), sp_op_const(11)), sp_CCons(sp_code_Xor32(var_edx(), var_edi()), sp_CCons(sp_code_Ror32(var_ebx(), sp_op_const(25)), sp_CCons(sp_code_Xor32(var_edx(), var_ebx()), sp_CCons(sp_code_Mov32(var_ebx(), stack(7)), sp_CCons(sp_code_Add32Wrap(var_ebx(), var_edx()), sp_CCons(sp_code_Add32Wrap(var_ebx(), var_ecx()), sp_CCons(sp_code_Add32Wrap(var_ebx(), sp_op_const(K)), sp_CCons(sp_code_Mov32(var_ecx(), W), sp_CCons(sp_code_Add32Wrap(var_ebx(), var_ecx()), sp_CNil())))))))))))))))))))))))))
}

function sp_code_ComputeOneStep_SHA256_spartan_part3(K:int, W:sp_operand):code
{
  sp_Block(sp_CCons(sp_code_Add32Wrap(var_eax(), var_ebx()), sp_CCons(sp_code_Mov32(stack(8), var_eax()), sp_CCons(sp_code_Mov32(var_eax(), stack(3)), sp_CCons(sp_code_Add32Wrap(var_eax(), var_ebx()), sp_CCons(sp_code_Mov32(stack(12), var_eax()), sp_CNil()))))))
}

function sp_code_ComputeOneStep_SHA256_spartan_parts2and3(K:int, W:sp_operand):code
{
  sp_Block(sp_CCons(sp_code_Mov32(var_ebx(), stack(4)), sp_CCons(sp_code_Mov32(stack(13), var_ebx()), sp_CCons(sp_code_Mov32(var_edx(), var_ebx()), sp_CCons(sp_code_Not32(var_edx()), sp_CCons(sp_code_Mov32(var_ecx(), stack(6)), sp_CCons(sp_code_Mov32(stack(15), var_ecx()), sp_CCons(sp_code_And32(var_edx(), var_ecx()), sp_CCons(sp_code_Mov32(var_ecx(), stack(5)), sp_CCons(sp_code_Mov32(stack(14), var_ecx()), sp_CCons(sp_code_And32(var_ecx(), var_ebx()), sp_CCons(sp_code_Xor32(var_ecx(), var_edx()), sp_CCons(sp_code_Mov32(var_edx(), var_ebx()), sp_CCons(sp_code_Mov32(var_edi(), var_ebx()), sp_CCons(sp_code_Ror32(var_edx(), sp_op_const(6)), sp_CCons(sp_code_Ror32(var_edi(), sp_op_const(11)), sp_CCons(sp_code_Xor32(var_edx(), var_edi()), sp_CCons(sp_code_Ror32(var_ebx(), sp_op_const(25)), sp_CCons(sp_code_Xor32(var_edx(), var_ebx()), sp_CCons(sp_code_Mov32(var_ebx(), stack(7)), sp_CCons(sp_code_Add32Wrap(var_ebx(), var_edx()), sp_CCons(sp_code_Add32Wrap(var_ebx(), var_ecx()), sp_CCons(sp_code_Add32Wrap(var_ebx(), sp_op_const(K)), sp_CCons(sp_code_Mov32(var_ecx(), W), sp_CCons(sp_code_Add32Wrap(var_ebx(), var_ecx()), sp_CCons(sp_code_Add32Wrap(var_eax(), var_ebx()), sp_CCons(sp_code_Mov32(stack(8), var_eax()), sp_CCons(sp_code_Mov32(var_eax(), stack(3)), sp_CCons(sp_code_Add32Wrap(var_eax(), var_ebx()), sp_CCons(sp_code_Mov32(stack(12), var_eax()), sp_CNil()))))))))))))))))))))))))))))))
}

function method{:opaque} sp_code_ComputeOneStep_SHA256_spartan(K:int, W:sp_operand):code
{
  sp_Block(sp_CCons(sp_code_Mov32(var_eax(), stack(0)), sp_CCons(sp_code_Mov32(stack(9), var_eax()), sp_CCons(sp_code_Mov32(var_ebx(), stack(1)), sp_CCons(sp_code_Mov32(stack(10), var_ebx()), sp_CCons(sp_code_Mov32(var_ecx(), stack(2)), sp_CCons(sp_code_Mov32(stack(11), var_ecx()), sp_CCons(sp_code_Mov32(var_edx(), var_ebx()), sp_CCons(sp_code_And32(var_ebx(), var_eax()), sp_CCons(sp_code_And32(var_edx(), var_ecx()), sp_CCons(sp_code_And32(var_ecx(), var_eax()), sp_CCons(sp_code_Xor32(var_ebx(), var_ecx()), sp_CCons(sp_code_Xor32(var_ebx(), var_edx()), sp_CCons(sp_code_Mov32(var_ecx(), var_eax()), sp_CCons(sp_code_Mov32(var_edx(), var_eax()), sp_CCons(sp_code_Ror32(var_eax(), sp_op_const(2)), sp_CCons(sp_code_Ror32(var_ecx(), sp_op_const(13)), sp_CCons(sp_code_Xor32(var_eax(), var_ecx()), sp_CCons(sp_code_Ror32(var_edx(), sp_op_const(22)), sp_CCons(sp_code_Xor32(var_eax(), var_edx()), sp_CCons(sp_code_Add32Wrap(var_eax(), var_ebx()), sp_CCons(sp_code_Mov32(var_ebx(), stack(4)), sp_CCons(sp_code_Mov32(stack(13), var_ebx()), sp_CCons(sp_code_Mov32(var_edx(), var_ebx()), sp_CCons(sp_code_Not32(var_edx()), sp_CCons(sp_code_Mov32(var_ecx(), stack(6)), sp_CCons(sp_code_Mov32(stack(15), var_ecx()), sp_CCons(sp_code_And32(var_edx(), var_ecx()), sp_CCons(sp_code_Mov32(var_ecx(), stack(5)), sp_CCons(sp_code_Mov32(stack(14), var_ecx()), sp_CCons(sp_code_And32(var_ecx(), var_ebx()), sp_CCons(sp_code_Xor32(var_ecx(), var_edx()), sp_CCons(sp_code_Mov32(var_edx(), var_ebx()), sp_CCons(sp_code_Mov32(var_edi(), var_ebx()), sp_CCons(sp_code_Ror32(var_edx(), sp_op_const(6)), sp_CCons(sp_code_Ror32(var_edi(), sp_op_const(11)), sp_CCons(sp_code_Xor32(var_edx(), var_edi()), sp_CCons(sp_code_Ror32(var_ebx(), sp_op_const(25)), sp_CCons(sp_code_Xor32(var_edx(), var_ebx()), sp_CCons(sp_code_Mov32(var_ebx(), stack(7)), sp_CCons(sp_code_Add32Wrap(var_ebx(), var_edx()), sp_CCons(sp_code_Add32Wrap(var_ebx(), var_ecx()), sp_CCons(sp_code_Add32Wrap(var_ebx(), sp_op_const(K)), sp_CCons(sp_code_Mov32(var_ecx(), W), sp_CCons(sp_code_Add32Wrap(var_ebx(), var_ecx()), sp_CCons(sp_code_Add32Wrap(var_eax(), var_ebx()), sp_CCons(sp_code_Mov32(stack(8), var_eax()), sp_CCons(sp_code_Mov32(var_eax(), stack(3)), sp_CCons(sp_code_Add32Wrap(var_eax(), var_ebx()), sp_CCons(sp_code_Mov32(stack(12), var_eax()), sp_CNil()))))))))))))))))))))))))))))))))))))))))))))))))))
}

predicate sp_postcondition_predicate_ComputeOneStep_SHA256_spartan_part1(sp_s:sp_state, sp_r:sp_state, sp_ok:sp_bool, K:int, W:sp_operand, atoh:atoh_Type, z:SHA256Trace, currentBlock:uint32, currentStep:uint32, numBlocks:uint32, currentState:SHA256_state)
{
       StackContainsRange(sp_s, 0, 16)
    && ValidRegisters(sp_s)
    && 0 <= K < 4294967296
    && Valid32BitOperand(sp_s, W)
    && 0 <= sp_eval_op(sp_s, stack(0)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(1)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(2)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(3)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(4)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(5)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(6)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(7)) < 4294967296
    && 0 <= int(currentStep) < SeqLength(currentState.W) && int(currentState.W[currentStep]) == sp_eval_op(sp_s, W)
    && StackContainsRange(sp_r, 0, 16)
    && ValidRegisters(sp_r)
    && Valid32BitOperand(sp_r, W)
    // Programmer-specified conditions go below:
    && sp_eval_op(sp_r, var_eax()) == int(BitwiseAdd32(BSIG0(currentState.atoh.a), Maj(currentState.atoh.a, currentState.atoh.b, currentState.atoh.c)))
    && sp_eval_op(sp_r, stack(0)) == sp_eval_op(sp_s, stack(0))
    && sp_eval_op(sp_r, stack(1)) == sp_eval_op(sp_s, stack(1))
    && sp_eval_op(sp_r, stack(2)) == sp_eval_op(sp_s, stack(2))
    && sp_eval_op(sp_r, stack(3)) == sp_eval_op(sp_s, stack(3))
    && sp_eval_op(sp_r, stack(4)) == sp_eval_op(sp_s, stack(4))
    && sp_eval_op(sp_r, stack(5)) == sp_eval_op(sp_s, stack(5))
    && sp_eval_op(sp_r, stack(6)) == sp_eval_op(sp_s, stack(6))
    && sp_eval_op(sp_r, stack(7)) == sp_eval_op(sp_s, stack(7))
    && sp_eval_op(sp_r, stack(8)) == sp_eval_op(sp_s, stack(8))
    && sp_eval_op(sp_r, stack(9)) == sp_eval_op(sp_s, stack(0))
    && sp_eval_op(sp_r, stack(10)) == sp_eval_op(sp_s, stack(1))
    && sp_eval_op(sp_r, stack(11)) == sp_eval_op(sp_s, stack(2))
    && sp_eval_op(sp_r, W) == sp_eval_op(sp_s, W)
}

predicate sp_postcondition_predicate_ComputeOneStep_SHA256_spartan_part2(sp_s:sp_state, sp_r:sp_state, sp_ok:sp_bool, K:int, W:sp_operand, atoh:atoh_Type, z:SHA256Trace, currentBlock:uint32, currentStep:uint32, numBlocks:uint32, currentState:SHA256_state)
{
       StackContainsRange(sp_s, 0, 16)
    && ValidRegisters(sp_s)
    && 0 <= K < 4294967296
    && Valid32BitOperand(sp_s, W)
    && 0 <= sp_eval_op(sp_s, stack(0)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(1)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(2)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(3)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(4)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(5)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(6)) < 4294967296
    && 0 <= sp_eval_op(sp_s, stack(7)) < 4294967296
    && 0 <= int(currentStep) < SeqLength(currentState.W) && int(currentState.W[currentStep]) == sp_eval_op(sp_s, W)
    && StackContainsRange(sp_r, 0, 16)
    && ValidRegisters(sp_r)
    && Valid32BitOperand(sp_r, W)
    // Programmer-specified conditions go below:
    && sp_eval_op(sp_r, var_eax()) == int(BitwiseAdd32(BSIG0(currentState.atoh.a), Maj(currentState.atoh.a, currentState.atoh.b, currentState.atoh.c)))
    &&  var bsig1 := int(BSIG1(uint32(sp_eval_op(sp_s, stack(4)))));
        var my_ch := int(Ch(uint32(sp_eval_op(sp_s, stack(4))), uint32(sp_eval_op(sp_s, stack(5))), uint32(sp_eval_op(sp_s, stack(6)))));
        sp_eval_op(sp_r, var_ebx()) == int(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(BitwiseAdd32(currentState.atoh.h, uint32(bsig1)), uint32(my_ch)), uint32(K)), uint32(sp_eval_op(sp_s, W))))
    && sp_eval_op(sp_r, stack(0)) == sp_eval_op(sp_s, stack(0))
    && sp_eval_op(sp_r, stack(1)) == sp_eval_op(sp_s, stack(1))
    && sp_eval_op(sp_r, stack(2)) == sp_eval_op(sp_s, stack(2))
    && sp_eval_op(sp_r, stack(3)) == sp_eval_op(sp_s, stack(3))
    && sp_eval_op(sp_r, stack(4)) == sp_eval_op(sp_s, stack(4))
    && sp_eval_op(sp_r, stack(5)) == sp_eval_op(sp_s, stack(5))
    && sp_eval_op(sp_r, stack(6)) == sp_eval_op(sp_s, stack(6))
    && sp_eval_op(sp_r, stack(7)) == sp_eval_op(sp_s, stack(7))
    && sp_eval_op(sp_r, stack(8)) == sp_eval_op(sp_s, stack(8))
    && sp_eval_op(sp_r, stack(9)) == sp_eval_op(sp_s, stack(0))
    && sp_eval_op(sp_r, stack(10)) == sp_eval_op(sp_s, stack(1))
    && sp_eval_op(sp_r, stack(11)) == sp_eval_op(sp_s, stack(2))
    && sp_eval_op(sp_r, stack(13)) == sp_eval_op(sp_s, stack(4))
    && sp_eval_op(sp_r, stack(14)) == sp_eval_op(sp_s, stack(5))
    && sp_eval_op(sp_r, stack(15)) == sp_eval_op(sp_s, stack(6))
}

lemma sp_lemma_ComputeOneStep_SHA256_spartan_part1(sp_s:sp_state, sp_r:sp_state, sp_ok:sp_bool, ghost K:int, ghost W:sp_operand, ghost atoh:atoh_Type, ghost z:SHA256Trace, ghost currentBlock:uint32, ghost currentStep:uint32, ghost numBlocks:uint32, ghost currentState:SHA256_state)
  requires sp_eval(sp_code_ComputeOneStep_SHA256_spartan_part1(K, W), sp_s, sp_r, sp_ok)
  ensures  sp_ok
  requires StackContainsRange(sp_s, 0, 16)
  requires ValidRegisters(sp_s)
  requires 0 <= K < 4294967296
  requires Valid32BitOperand(sp_s, W)
  ensures  StackContainsRange(sp_r, 0, 16)
  ensures  ValidRegisters(sp_r)
  ensures  0 <= K < 4294967296
  ensures  Valid32BitOperand(sp_r, W)
  requires 0 <= sp_eval_op(sp_s, stack(0)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(1)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(2)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(3)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(4)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(5)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(6)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(7)) < 4294967296
  requires HeapOperand(W)
  requires currentStep <= 63
  requires currentBlock < 4294967294
  requires K == int(K_SHA256(currentStep))
  requires atoh == atoh_c(uint32(sp_eval_op(sp_s, stack(0))), uint32(sp_eval_op(sp_s, stack(1))), uint32(sp_eval_op(sp_s, stack(2))), uint32(sp_eval_op(sp_s, stack(3))), uint32(sp_eval_op(sp_s, stack(4))), uint32(sp_eval_op(sp_s, stack(5))), uint32(sp_eval_op(sp_s, stack(6))), uint32(sp_eval_op(sp_s, stack(7))))
  requires currentState.atoh == atoh
  requires currentState.num_blocks == numBlocks
  requires 0 <= int(currentStep) < SeqLength(currentState.W) && int(currentState.W[currentStep]) == sp_eval_op(sp_s, W)
  requires IsSHA256ReadyForStep(z, currentState, int(currentBlock), int(currentStep))
  ensures  sp_postcondition_predicate_ComputeOneStep_SHA256_spartan_part1(sp_s, sp_r, sp_ok, K, W, atoh, z, currentBlock, currentStep, numBlocks, currentState);
{
  var sp_old_s:sp_state := sp_s;
  var sp_b1 := sp_get_block(sp_code_ComputeOneStep_SHA256_spartan_part1(K, W));
  ghost var sp_r2, sp_ok2, sp_c2, sp_b2 := sp_lemma_block(sp_b1, sp_s, sp_r, sp_ok);
  sp_lemma_Mov32(sp_s, sp_r2, sp_ok2, var_eax(), stack(0));
  ghost var sp_r3, sp_ok3, sp_c3, sp_b3 := sp_lemma_block(sp_b2, sp_r2, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r2, sp_r3, sp_ok3, stack(9), var_eax());
  ghost var sp_r4, sp_ok4, sp_c4, sp_b4 := sp_lemma_block(sp_b3, sp_r3, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r3, sp_r4, sp_ok4, var_ebx(), stack(1));
  ghost var sp_r5, sp_ok5, sp_c5, sp_b5 := sp_lemma_block(sp_b4, sp_r4, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r4, sp_r5, sp_ok5, stack(10), var_ebx());
  ghost var sp_r6, sp_ok6, sp_c6, sp_b6 := sp_lemma_block(sp_b5, sp_r5, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r5, sp_r6, sp_ok6, var_ecx(), stack(2));
  ghost var sp_r7, sp_ok7, sp_c7, sp_b7 := sp_lemma_block(sp_b6, sp_r6, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r6, sp_r7, sp_ok7, stack(11), var_ecx());
  ghost var sp_r8, sp_ok8, sp_c8, sp_b8 := sp_lemma_block(sp_b7, sp_r7, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r7, sp_r8, sp_ok8, var_edx(), var_ebx());
  lemma_BitwiseCommutative(uint32(sp_eval_op(sp_r8, var_ebx())), uint32(sp_eval_op(sp_r8, var_eax())));
  ghost var sp_r10, sp_ok10, sp_c10, sp_b10 := sp_lemma_block(sp_b8, sp_r8, sp_r, sp_ok);
  sp_lemma_And32(sp_r8, sp_r10, sp_ok10, var_ebx(), var_eax());
  ghost var sp_r11, sp_ok11, sp_c11, sp_b11 := sp_lemma_block(sp_b10, sp_r10, sp_r, sp_ok);
  sp_lemma_And32(sp_r10, sp_r11, sp_ok11, var_edx(), var_ecx());
  lemma_BitwiseCommutative(uint32(sp_eval_op(sp_r11, var_ecx())), uint32(sp_eval_op(sp_r11, var_eax())));
  ghost var sp_r13, sp_ok13, sp_c13, sp_b13 := sp_lemma_block(sp_b11, sp_r11, sp_r, sp_ok);
  sp_lemma_And32(sp_r11, sp_r13, sp_ok13, var_ecx(), var_eax());
  ghost var sp_r14, sp_ok14, sp_c14, sp_b14 := sp_lemma_block(sp_b13, sp_r13, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r13, sp_r14, sp_ok14, var_ebx(), var_ecx());
  ghost var sp_r15, sp_ok15, sp_c15, sp_b15 := sp_lemma_block(sp_b14, sp_r14, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r14, sp_r15, sp_ok15, var_ebx(), var_edx());
  forall 
    ensures sp_eval_op(sp_r15, var_ebx()) == int(Maj(uint32(sp_eval_op(sp_old_s, stack(0))), uint32(sp_eval_op(sp_old_s, stack(1))), uint32(sp_eval_op(sp_old_s, stack(2)))))
  {
    reveal_Maj();
  }
  ghost var sp_r17, sp_ok17, sp_c17, sp_b17 := sp_lemma_block(sp_b15, sp_r15, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r15, sp_r17, sp_ok17, var_ecx(), var_eax());
  ghost var sp_r18, sp_ok18, sp_c18, sp_b18 := sp_lemma_block(sp_b17, sp_r17, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r17, sp_r18, sp_ok18, var_edx(), var_eax());
  ghost var sp_r19, sp_ok19, sp_c19, sp_b19 := sp_lemma_block(sp_b18, sp_r18, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r18, sp_r19, sp_ok19, var_eax(), sp_op_const(2));
  ghost var sp_r20, sp_ok20, sp_c20, sp_b20 := sp_lemma_block(sp_b19, sp_r19, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r19, sp_r20, sp_ok20, var_ecx(), sp_op_const(13));
  ghost var sp_r21, sp_ok21, sp_c21, sp_b21 := sp_lemma_block(sp_b20, sp_r20, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r20, sp_r21, sp_ok21, var_eax(), var_ecx());
  ghost var sp_r22, sp_ok22, sp_c22, sp_b22 := sp_lemma_block(sp_b21, sp_r21, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r21, sp_r22, sp_ok22, var_edx(), sp_op_const(22));
  ghost var sp_r23, sp_ok23, sp_c23, sp_b23 := sp_lemma_block(sp_b22, sp_r22, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r22, sp_r23, sp_ok23, var_eax(), var_edx());
  forall 
    ensures sp_eval_op(sp_r23, var_eax()) == int(BSIG0(uint32(sp_eval_op(sp_old_s, stack(0)))))
  {
    reveal_BSIG0();
  }
  ghost var sp_r25, sp_ok25, sp_c25, sp_b25 := sp_lemma_block(sp_b23, sp_r23, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r23, sp_r25, sp_ok25, var_eax(), var_ebx());
  assert sp_eval_op(sp_r25, var_eax()) == int(BitwiseAdd32(BSIG0(currentState.atoh.a), Maj(currentState.atoh.a, currentState.atoh.b, currentState.atoh.c)));

  sp_lemma_empty(sp_r25, sp_r, sp_ok);
}

lemma {:timeLimitMultiplier 2} sp_lemma_ComputeOneStep_SHA256_spartan_part2(sp_s:sp_state, sp_r25:sp_state, sp_r:sp_state, sp_ok:sp_bool, ghost K:int, ghost W:sp_operand, ghost atoh:atoh_Type, ghost z:SHA256Trace, ghost currentBlock:uint32, ghost currentStep:uint32, ghost numBlocks:uint32, ghost currentState:SHA256_state)
  requires sp_eval(sp_code_ComputeOneStep_SHA256_spartan_part2(K, W), sp_r25, sp_r, sp_ok)
  ensures  sp_ok
  requires StackContainsRange(sp_s, 0, 16)
  requires ValidRegisters(sp_s)
  requires 0 <= K < 4294967296
  requires Valid32BitOperand(sp_s, W)
  ensures  StackContainsRange(sp_r, 0, 16)
  ensures  ValidRegisters(sp_r)
  ensures  0 <= K < 4294967296
  ensures  Valid32BitOperand(sp_r, W)
  requires 0 <= sp_eval_op(sp_s, stack(0)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(1)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(2)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(3)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(4)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(5)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(6)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(7)) < 4294967296
  requires HeapOperand(W)
  requires currentStep <= 63
  requires currentBlock < 4294967294
  requires K == int(K_SHA256(currentStep))
  requires atoh == atoh_c(uint32(sp_eval_op(sp_s, stack(0))), uint32(sp_eval_op(sp_s, stack(1))), uint32(sp_eval_op(sp_s, stack(2))), uint32(sp_eval_op(sp_s, stack(3))), uint32(sp_eval_op(sp_s, stack(4))), uint32(sp_eval_op(sp_s, stack(5))), uint32(sp_eval_op(sp_s, stack(6))), uint32(sp_eval_op(sp_s, stack(7))))
  requires currentState.atoh == atoh
  requires currentState.num_blocks == numBlocks
  requires 0 <= int(currentStep) < SeqLength(currentState.W) && int(currentState.W[currentStep]) == sp_eval_op(sp_s, W)
  requires IsSHA256ReadyForStep(z, currentState, int(currentBlock), int(currentStep))
  requires sp_postcondition_predicate_ComputeOneStep_SHA256_spartan_part1(sp_s, sp_r25, sp_ok, K, W, atoh, z, currentBlock, currentStep, numBlocks, currentState);
  ensures  sp_postcondition_predicate_ComputeOneStep_SHA256_spartan_part2(sp_s, sp_r, sp_ok, K, W, atoh, z, currentBlock, currentStep, numBlocks, currentState);
{
  var sp_old_s:sp_state := sp_s;

  var sp_b1 := sp_get_block(sp_code_ComputeOneStep_SHA256_spartan_part2(K, W));
  ghost var sp_r27, sp_ok27, sp_c27, sp_b27 := sp_lemma_block(sp_b1, sp_r25, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r25, sp_r27, sp_ok27, var_ebx(), stack(4));
  ghost var sp_r28, sp_ok28, sp_c28, sp_b28 := sp_lemma_block(sp_b27, sp_r27, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r27, sp_r28, sp_ok28, stack(13), var_ebx());
  ghost var sp_r29, sp_ok29, sp_c29, sp_b29 := sp_lemma_block(sp_b28, sp_r28, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r28, sp_r29, sp_ok29, var_edx(), var_ebx());
  ghost var sp_r30, sp_ok30, sp_c30, sp_b30 := sp_lemma_block(sp_b29, sp_r29, sp_r, sp_ok);
  sp_lemma_Not32(sp_r29, sp_r30, sp_ok30, var_edx());
  ghost var sp_r31, sp_ok31, sp_c31, sp_b31 := sp_lemma_block(sp_b30, sp_r30, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r30, sp_r31, sp_ok31, var_ecx(), stack(6));
  ghost var sp_r32, sp_ok32, sp_c32, sp_b32 := sp_lemma_block(sp_b31, sp_r31, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r31, sp_r32, sp_ok32, stack(15), var_ecx());
  ghost var sp_r33, sp_ok33, sp_c33, sp_b33 := sp_lemma_block(sp_b32, sp_r32, sp_r, sp_ok);
  sp_lemma_And32(sp_r32, sp_r33, sp_ok33, var_edx(), var_ecx());
  ghost var sp_r34, sp_ok34, sp_c34, sp_b34 := sp_lemma_block(sp_b33, sp_r33, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r33, sp_r34, sp_ok34, var_ecx(), stack(5));
  ghost var sp_r35, sp_ok35, sp_c35, sp_b35 := sp_lemma_block(sp_b34, sp_r34, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r34, sp_r35, sp_ok35, stack(14), var_ecx());
  lemma_BitwiseCommutative(uint32(sp_eval_op(sp_r35, var_ecx())), uint32(sp_eval_op(sp_r35, var_ebx())));
  ghost var sp_r37, sp_ok37, sp_c37, sp_b37 := sp_lemma_block(sp_b35, sp_r35, sp_r, sp_ok);
  sp_lemma_And32(sp_r35, sp_r37, sp_ok37, var_ecx(), var_ebx());
  lemma_BitwiseCommutative(uint32(sp_eval_op(sp_r37, var_ecx())), uint32(sp_eval_op(sp_r37, var_edx())));
  ghost var sp_r39, sp_ok39, sp_c39, sp_b39 := sp_lemma_block(sp_b37, sp_r37, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r37, sp_r39, sp_ok39, var_ecx(), var_edx());
  forall 
    ensures sp_eval_op(sp_r39, var_ecx()) == int(Ch(uint32(sp_eval_op(sp_old_s, stack(4))), uint32(sp_eval_op(sp_old_s, stack(5))), uint32(sp_eval_op(sp_old_s, stack(6)))))
  {
    reveal_Ch();
  }
  ghost var sp_r41, sp_ok41, sp_c41, sp_b41 := sp_lemma_block(sp_b39, sp_r39, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r39, sp_r41, sp_ok41, var_edx(), var_ebx());
  ghost var sp_r42, sp_ok42, sp_c42, sp_b42 := sp_lemma_block(sp_b41, sp_r41, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r41, sp_r42, sp_ok42, var_edi(), var_ebx());
  ghost var sp_r43, sp_ok43, sp_c43, sp_b43 := sp_lemma_block(sp_b42, sp_r42, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r42, sp_r43, sp_ok43, var_edx(), sp_op_const(6));
  ghost var sp_r44, sp_ok44, sp_c44, sp_b44 := sp_lemma_block(sp_b43, sp_r43, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r43, sp_r44, sp_ok44, var_edi(), sp_op_const(11));
  ghost var sp_r45, sp_ok45, sp_c45, sp_b45 := sp_lemma_block(sp_b44, sp_r44, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r44, sp_r45, sp_ok45, var_edx(), var_edi());
  ghost var sp_r46, sp_ok46, sp_c46, sp_b46 := sp_lemma_block(sp_b45, sp_r45, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r45, sp_r46, sp_ok46, var_ebx(), sp_op_const(25));
  ghost var sp_r47, sp_ok47, sp_c47, sp_b47 := sp_lemma_block(sp_b46, sp_r46, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r46, sp_r47, sp_ok47, var_edx(), var_ebx());
  forall 
    ensures sp_eval_op(sp_r47, var_edx()) == int(BSIG1(uint32(sp_eval_op(sp_old_s, stack(4)))))
  {
    reveal_BSIG1();
  }
  ghost var sp_r49, sp_ok49, sp_c49, sp_b49 := sp_lemma_block(sp_b47, sp_r47, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r47, sp_r49, sp_ok49, var_ebx(), stack(7));
  ghost var sp_r50, sp_ok50, sp_c50, sp_b50 := sp_lemma_block(sp_b49, sp_r49, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r49, sp_r50, sp_ok50, var_ebx(), var_edx());
  ghost var sp_r51, sp_ok51, sp_c51, sp_b51 := sp_lemma_block(sp_b50, sp_r50, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r50, sp_r51, sp_ok51, var_ebx(), var_ecx());
  ghost var sp_r52, sp_ok52, sp_c52, sp_b52 := sp_lemma_block(sp_b51, sp_r51, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r51, sp_r52, sp_ok52, var_ebx(), sp_op_const(K));
  ghost var sp_r53, sp_ok53, sp_c53, sp_b53 := sp_lemma_block(sp_b52, sp_r52, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r52, sp_r53, sp_ok53, var_ecx(), W);
  ghost var sp_r54, sp_ok54, sp_c54, sp_b54 := sp_lemma_block(sp_b53, sp_r53, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r53, sp_r54, sp_ok54, var_ebx(), var_ecx());
  sp_lemma_empty(sp_r54, sp_r, sp_ok);
}

lemma sp_lemma_ComputeOneStep_SHA256_spartan_part3(sp_s:sp_state, sp_r54:sp_state, sp_r:sp_state, sp_ok:sp_bool, ghost K:int, ghost W:sp_operand, ghost atoh:atoh_Type, ghost z:SHA256Trace, ghost currentBlock:uint32, ghost currentStep:uint32, ghost numBlocks:uint32, ghost currentState:SHA256_state)
  returns (ghost next_atoh:atoh_Type, ghost next_z:SHA256Trace)
  requires sp_eval(sp_code_ComputeOneStep_SHA256_spartan_part3(K, W), sp_r54, sp_r, sp_ok)
  ensures  sp_ok
  requires StackContainsRange(sp_s, 0, 16)
  requires ValidRegisters(sp_s)
  requires 0 <= K < 4294967296
  requires Valid32BitOperand(sp_s, W)
  ensures  StackContainsRange(sp_r, 0, 16)
  ensures  ValidRegisters(sp_r)
  ensures  0 <= K < 4294967296
  ensures  Valid32BitOperand(sp_r, W)
  requires 0 <= sp_eval_op(sp_s, stack(0)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(1)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(2)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(3)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(4)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(5)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(6)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(7)) < 4294967296
  requires HeapOperand(W)
  requires currentStep <= 63
  requires currentBlock < 4294967294
  requires K == int(K_SHA256(currentStep))
  requires atoh == atoh_c(uint32(sp_eval_op(sp_s, stack(0))), uint32(sp_eval_op(sp_s, stack(1))), uint32(sp_eval_op(sp_s, stack(2))), uint32(sp_eval_op(sp_s, stack(3))), uint32(sp_eval_op(sp_s, stack(4))), uint32(sp_eval_op(sp_s, stack(5))), uint32(sp_eval_op(sp_s, stack(6))), uint32(sp_eval_op(sp_s, stack(7))))
  requires currentState.atoh == atoh
  requires currentState.num_blocks == numBlocks
  requires 0 <= int(currentStep) < SeqLength(currentState.W) && int(currentState.W[currentStep]) == sp_eval_op(sp_s, W)
  requires IsSHA256ReadyForStep(z, currentState, int(currentBlock), int(currentStep))
  requires sp_postcondition_predicate_ComputeOneStep_SHA256_spartan_part2(sp_s, sp_r54, sp_ok, K, W, atoh, z, currentBlock, currentStep, numBlocks, currentState);
  ensures  0 <= sp_eval_op(sp_r, stack(8)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(9)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(10)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(11)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(12)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(13)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(14)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(15)) < 4294967296
  ensures  next_atoh == atoh_c(uint32(sp_eval_op(sp_r, stack(8))), uint32(sp_eval_op(sp_r, stack(9))), uint32(sp_eval_op(sp_r, stack(10))), uint32(sp_eval_op(sp_r, stack(11))), uint32(sp_eval_op(sp_r, stack(12))), uint32(sp_eval_op(sp_r, stack(13))), uint32(sp_eval_op(sp_r, stack(14))), uint32(sp_eval_op(sp_r, stack(15))))
  ensures  IsSHA256ReadyForStep(next_z, currentState.(atoh := next_atoh), int(currentBlock), int(currentStep) + 1)
{
  var sp_old_s:sp_state := sp_s;

  var sp_b1 := sp_get_block(sp_code_ComputeOneStep_SHA256_spartan_part3(K, W));
  ghost var sp_r55, sp_ok55, sp_c55, sp_b55 := sp_lemma_block(sp_b1, sp_r54, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r54, sp_r55, sp_ok55, var_eax(), var_ebx());
  ghost var sp_r56, sp_ok56, sp_c56, sp_b56 := sp_lemma_block(sp_b55, sp_r55, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r55, sp_r56, sp_ok56, stack(8), var_eax());
  ghost var sp_r57, sp_ok57, sp_c57, sp_b57 := sp_lemma_block(sp_b56, sp_r56, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r56, sp_r57, sp_ok57, var_eax(), stack(3));
  ghost var sp_r58, sp_ok58, sp_c58, sp_b58 := sp_lemma_block(sp_b57, sp_r57, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r57, sp_r58, sp_ok58, var_eax(), var_ebx());
  ghost var sp_r59, sp_ok59, sp_c59, sp_b59 := sp_lemma_block(sp_b58, sp_r58, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r58, sp_r59, sp_ok59, stack(12), var_eax());
  assert ((TBlk(currentBlock) && TBlk(currentBlock + 1)) && TStep(currentStep)) && TStep(currentStep + 1);
  next_atoh := atoh_c(uint32(sp_eval_op(sp_r59, stack(8))), uint32(sp_eval_op(sp_r59, stack(9))), uint32(sp_eval_op(sp_r59, stack(10))), uint32(sp_eval_op(sp_r59, stack(11))), uint32(sp_eval_op(sp_r59, stack(12))), uint32(sp_eval_op(sp_r59, stack(13))), uint32(sp_eval_op(sp_r59, stack(14))), uint32(sp_eval_op(sp_r59, stack(15))));
  next_z := SHA256Trace_c(z.M, z.H, z.W, SeqDrop(z.atoh, int(currentBlock)) + SeqBuild(SeqAppendElt(z.atoh[currentBlock], next_atoh)));
  ghost var next_s := currentState.(atoh := next_atoh);
  lemma_SHA256TransitionOKAfterSettingAtoH(z, currentState, next_z, next_s, currentBlock, currentStep);
  sp_lemma_empty(sp_r59, sp_r, sp_ok);
}

lemma {:fuel ConcatenateCodes,90} sp_lemma_ComputeOneStep_SHA256_spartan_using_split(sp_s:sp_state, sp_r:sp_state, sp_ok:sp_bool, ghost K:int, ghost W:sp_operand, ghost atoh:atoh_Type, ghost z:SHA256Trace, ghost currentBlock:uint32, ghost currentStep:uint32, ghost numBlocks:uint32, ghost currentState:SHA256_state)
  returns (ghost next_atoh:atoh_Type, ghost next_z:SHA256Trace)
  requires sp_eval(sp_code_ComputeOneStep_SHA256_spartan(K, W), sp_s, sp_r, sp_ok)
  ensures  sp_ok
  requires StackContainsRange(sp_s, 0, 16)
  requires ValidRegisters(sp_s)
  requires 0 <= K < 4294967296
  requires Valid32BitOperand(sp_s, W)
  ensures  StackContainsRange(sp_r, 0, 16)
  ensures  ValidRegisters(sp_r)
  ensures  0 <= K < 4294967296
  ensures  Valid32BitOperand(sp_r, W)
  requires 0 <= sp_eval_op(sp_s, stack(0)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(1)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(2)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(3)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(4)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(5)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(6)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(7)) < 4294967296
  requires HeapOperand(W)
  requires currentStep <= 63
  requires currentBlock < 4294967294
  requires K == int(K_SHA256(currentStep))
  requires atoh == atoh_c(uint32(sp_eval_op(sp_s, stack(0))), uint32(sp_eval_op(sp_s, stack(1))), uint32(sp_eval_op(sp_s, stack(2))), uint32(sp_eval_op(sp_s, stack(3))), uint32(sp_eval_op(sp_s, stack(4))), uint32(sp_eval_op(sp_s, stack(5))), uint32(sp_eval_op(sp_s, stack(6))), uint32(sp_eval_op(sp_s, stack(7))))
  requires currentState.atoh == atoh
  requires currentState.num_blocks == numBlocks
  requires 0 <= int(currentStep) < SeqLength(currentState.W) && int(currentState.W[currentStep]) == sp_eval_op(sp_s, W)
  requires IsSHA256ReadyForStep(z, currentState, int(currentBlock), int(currentStep))
  ensures  0 <= sp_eval_op(sp_r, stack(8)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(9)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(10)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(11)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(12)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(13)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(14)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(15)) < 4294967296
  ensures  next_atoh == atoh_c(uint32(sp_eval_op(sp_r, stack(8))), uint32(sp_eval_op(sp_r, stack(9))), uint32(sp_eval_op(sp_r, stack(10))), uint32(sp_eval_op(sp_r, stack(11))), uint32(sp_eval_op(sp_r, stack(12))), uint32(sp_eval_op(sp_r, stack(13))), uint32(sp_eval_op(sp_r, stack(14))), uint32(sp_eval_op(sp_r, stack(15))))
  ensures  IsSHA256ReadyForStep(next_z, currentState.(atoh := next_atoh), int(currentBlock), int(currentStep) + 1)
{
  reveal_sp_code_ComputeOneStep_SHA256_spartan();
  var sp_old_s:sp_state := sp_s;
  var sp_block := sp_get_block(sp_code_ComputeOneStep_SHA256_spartan(K, W));
  var sp_block1 := sp_get_block(sp_code_ComputeOneStep_SHA256_spartan_part1(K, W));
  var sp_block2 := sp_get_block(sp_code_ComputeOneStep_SHA256_spartan_part2(K, W));
  var sp_block3 := sp_get_block(sp_code_ComputeOneStep_SHA256_spartan_part3(K, W));
  var sp_blocks2and3 := sp_get_block(sp_code_ComputeOneStep_SHA256_spartan_parts2and3(K, W));
  assert sp_blocks2and3 == ConcatenateCodes(sp_block2, sp_block3);
  assert ConcatenateCodes(sp_block1, sp_blocks2and3) == sp_block;

  assert sp_eval(sp_Block(sp_block), sp_old_s, sp_r, sp_ok);
  reveal_eval();
  var sp_intermediate_state1, ok1 := lemma_GetIntermediateStateBetweenCodeBlocks(sp_old_s, sp_r, sp_block1, sp_blocks2and3, sp_block, sp_ok);
  sp_lemma_ComputeOneStep_SHA256_spartan_part1(sp_old_s, sp_intermediate_state1, ok1, K, W, atoh, z, currentBlock, currentStep, numBlocks, currentState);
  var sp_intermediate_state2, ok2 := lemma_GetIntermediateStateBetweenCodeBlocks(sp_intermediate_state1, sp_r, sp_block2, sp_block3, sp_blocks2and3, sp_ok);
  sp_lemma_ComputeOneStep_SHA256_spartan_part2(sp_old_s, sp_intermediate_state1, sp_intermediate_state2, ok2, K, W, atoh, z, currentBlock, currentStep, numBlocks, currentState);
  next_atoh, next_z := sp_lemma_ComputeOneStep_SHA256_spartan_part3(sp_old_s, sp_intermediate_state2, sp_r, sp_ok, K, W, atoh, z, currentBlock, currentStep, numBlocks, currentState);
}

lemma {:timeLimitMultiplier 3} sp_lemma_ComputeOneStep_SHA256_spartan(sp_s:sp_state, sp_r:sp_state, sp_ok:sp_bool, ghost K:int, ghost W:sp_operand, ghost atoh:atoh_Type, ghost z:SHA256Trace, ghost currentBlock:uint32, ghost currentStep:uint32, ghost numBlocks:uint32, ghost currentState:SHA256_state)
  returns (ghost next_atoh:atoh_Type, ghost next_z:SHA256Trace)
  requires sp_eval(sp_code_ComputeOneStep_SHA256_spartan(K, W), sp_s, sp_r, sp_ok)
  ensures  sp_ok
  requires StackContainsRange(sp_s, 0, 16)
  requires ValidRegisters(sp_s)
  requires 0 <= K < 4294967296
  requires Valid32BitOperand(sp_s, W)
  ensures  StackContainsRange(sp_r, 0, 16)
  ensures  ValidRegisters(sp_r)
  ensures  0 <= K < 4294967296
  ensures  Valid32BitOperand(sp_r, W)
  requires 0 <= sp_eval_op(sp_s, stack(0)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(1)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(2)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(3)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(4)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(5)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(6)) < 4294967296
  requires 0 <= sp_eval_op(sp_s, stack(7)) < 4294967296
  requires HeapOperand(W)
  requires currentStep <= 63
  requires currentBlock < 4294967294
  requires K == int(K_SHA256(currentStep))
  requires atoh == atoh_c(uint32(sp_eval_op(sp_s, stack(0))), uint32(sp_eval_op(sp_s, stack(1))), uint32(sp_eval_op(sp_s, stack(2))), uint32(sp_eval_op(sp_s, stack(3))), uint32(sp_eval_op(sp_s, stack(4))), uint32(sp_eval_op(sp_s, stack(5))), uint32(sp_eval_op(sp_s, stack(6))), uint32(sp_eval_op(sp_s, stack(7))))
  requires currentState.atoh == atoh
  requires currentState.num_blocks == numBlocks
  requires 0 <= int(currentStep) < SeqLength(currentState.W) && int(currentState.W[currentStep]) == sp_eval_op(sp_s, W)
  requires IsSHA256ReadyForStep(z, currentState, int(currentBlock), int(currentStep))
  ensures  0 <= sp_eval_op(sp_r, stack(8)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(9)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(10)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(11)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(12)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(13)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(14)) < 4294967296
  ensures  0 <= sp_eval_op(sp_r, stack(15)) < 4294967296
  ensures  next_atoh == atoh_c(uint32(sp_eval_op(sp_r, stack(8))), uint32(sp_eval_op(sp_r, stack(9))), uint32(sp_eval_op(sp_r, stack(10))), uint32(sp_eval_op(sp_r, stack(11))), uint32(sp_eval_op(sp_r, stack(12))), uint32(sp_eval_op(sp_r, stack(13))), uint32(sp_eval_op(sp_r, stack(14))), uint32(sp_eval_op(sp_r, stack(15))))
  ensures  IsSHA256ReadyForStep(next_z, currentState.(atoh := next_atoh), int(currentBlock), int(currentStep) + 1)
{
  reveal_sp_code_ComputeOneStep_SHA256_spartan();
  var sp_old_s:sp_state := sp_s;
  var sp_b1 := sp_get_block(sp_code_ComputeOneStep_SHA256_spartan(K, W));
  ghost var sp_r2, sp_ok2, sp_c2, sp_b2 := sp_lemma_block(sp_b1, sp_s, sp_r, sp_ok);
  sp_lemma_Mov32(sp_s, sp_r2, sp_ok2, var_eax(), stack(0));
  ghost var sp_r3, sp_ok3, sp_c3, sp_b3 := sp_lemma_block(sp_b2, sp_r2, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r2, sp_r3, sp_ok3, stack(9), var_eax());
  ghost var sp_r4, sp_ok4, sp_c4, sp_b4 := sp_lemma_block(sp_b3, sp_r3, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r3, sp_r4, sp_ok4, var_ebx(), stack(1));
  ghost var sp_r5, sp_ok5, sp_c5, sp_b5 := sp_lemma_block(sp_b4, sp_r4, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r4, sp_r5, sp_ok5, stack(10), var_ebx());
  ghost var sp_r6, sp_ok6, sp_c6, sp_b6 := sp_lemma_block(sp_b5, sp_r5, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r5, sp_r6, sp_ok6, var_ecx(), stack(2));
  ghost var sp_r7, sp_ok7, sp_c7, sp_b7 := sp_lemma_block(sp_b6, sp_r6, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r6, sp_r7, sp_ok7, stack(11), var_ecx());
  ghost var sp_r8, sp_ok8, sp_c8, sp_b8 := sp_lemma_block(sp_b7, sp_r7, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r7, sp_r8, sp_ok8, var_edx(), var_ebx());
  lemma_BitwiseCommutative(uint32(sp_eval_op(sp_r8, var_ebx())), uint32(sp_eval_op(sp_r8, var_eax())));
  ghost var sp_r10, sp_ok10, sp_c10, sp_b10 := sp_lemma_block(sp_b8, sp_r8, sp_r, sp_ok);
  sp_lemma_And32(sp_r8, sp_r10, sp_ok10, var_ebx(), var_eax());
  ghost var sp_r11, sp_ok11, sp_c11, sp_b11 := sp_lemma_block(sp_b10, sp_r10, sp_r, sp_ok);
  sp_lemma_And32(sp_r10, sp_r11, sp_ok11, var_edx(), var_ecx());
  lemma_BitwiseCommutative(uint32(sp_eval_op(sp_r11, var_ecx())), uint32(sp_eval_op(sp_r11, var_eax())));
  ghost var sp_r13, sp_ok13, sp_c13, sp_b13 := sp_lemma_block(sp_b11, sp_r11, sp_r, sp_ok);
  sp_lemma_And32(sp_r11, sp_r13, sp_ok13, var_ecx(), var_eax());
  ghost var sp_r14, sp_ok14, sp_c14, sp_b14 := sp_lemma_block(sp_b13, sp_r13, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r13, sp_r14, sp_ok14, var_ebx(), var_ecx());
  ghost var sp_r15, sp_ok15, sp_c15, sp_b15 := sp_lemma_block(sp_b14, sp_r14, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r14, sp_r15, sp_ok15, var_ebx(), var_edx());
  forall 
    ensures sp_eval_op(sp_r15, var_ebx()) == int(Maj(uint32(sp_eval_op(sp_old_s, stack(0))), uint32(sp_eval_op(sp_old_s, stack(1))), uint32(sp_eval_op(sp_old_s, stack(2)))))
  {
    reveal_Maj();
  }
  ghost var sp_r17, sp_ok17, sp_c17, sp_b17 := sp_lemma_block(sp_b15, sp_r15, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r15, sp_r17, sp_ok17, var_ecx(), var_eax());
  ghost var sp_r18, sp_ok18, sp_c18, sp_b18 := sp_lemma_block(sp_b17, sp_r17, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r17, sp_r18, sp_ok18, var_edx(), var_eax());
  ghost var sp_r19, sp_ok19, sp_c19, sp_b19 := sp_lemma_block(sp_b18, sp_r18, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r18, sp_r19, sp_ok19, var_eax(), sp_op_const(2));
  ghost var sp_r20, sp_ok20, sp_c20, sp_b20 := sp_lemma_block(sp_b19, sp_r19, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r19, sp_r20, sp_ok20, var_ecx(), sp_op_const(13));
  ghost var sp_r21, sp_ok21, sp_c21, sp_b21 := sp_lemma_block(sp_b20, sp_r20, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r20, sp_r21, sp_ok21, var_eax(), var_ecx());
  ghost var sp_r22, sp_ok22, sp_c22, sp_b22 := sp_lemma_block(sp_b21, sp_r21, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r21, sp_r22, sp_ok22, var_edx(), sp_op_const(22));
  ghost var sp_r23, sp_ok23, sp_c23, sp_b23 := sp_lemma_block(sp_b22, sp_r22, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r22, sp_r23, sp_ok23, var_eax(), var_edx());
  forall 
    ensures sp_eval_op(sp_r23, var_eax()) == int(BSIG0(uint32(sp_eval_op(sp_old_s, stack(0)))))
  {
    reveal_BSIG0();
  }
  ghost var sp_r25, sp_ok25, sp_c25, sp_b25 := sp_lemma_block(sp_b23, sp_r23, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r23, sp_r25, sp_ok25, var_eax(), var_ebx());
  assert sp_eval_op(sp_r25, var_eax()) == int(BitwiseAdd32(BSIG0(currentState.atoh.a), Maj(currentState.atoh.a, currentState.atoh.b, currentState.atoh.c)));
  ghost var sp_r27, sp_ok27, sp_c27, sp_b27 := sp_lemma_block(sp_b25, sp_r25, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r25, sp_r27, sp_ok27, var_ebx(), stack(4));
  ghost var sp_r28, sp_ok28, sp_c28, sp_b28 := sp_lemma_block(sp_b27, sp_r27, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r27, sp_r28, sp_ok28, stack(13), var_ebx());
  ghost var sp_r29, sp_ok29, sp_c29, sp_b29 := sp_lemma_block(sp_b28, sp_r28, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r28, sp_r29, sp_ok29, var_edx(), var_ebx());
  ghost var sp_r30, sp_ok30, sp_c30, sp_b30 := sp_lemma_block(sp_b29, sp_r29, sp_r, sp_ok);
  sp_lemma_Not32(sp_r29, sp_r30, sp_ok30, var_edx());
  ghost var sp_r31, sp_ok31, sp_c31, sp_b31 := sp_lemma_block(sp_b30, sp_r30, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r30, sp_r31, sp_ok31, var_ecx(), stack(6));
  ghost var sp_r32, sp_ok32, sp_c32, sp_b32 := sp_lemma_block(sp_b31, sp_r31, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r31, sp_r32, sp_ok32, stack(15), var_ecx());
  ghost var sp_r33, sp_ok33, sp_c33, sp_b33 := sp_lemma_block(sp_b32, sp_r32, sp_r, sp_ok);
  sp_lemma_And32(sp_r32, sp_r33, sp_ok33, var_edx(), var_ecx());
  ghost var sp_r34, sp_ok34, sp_c34, sp_b34 := sp_lemma_block(sp_b33, sp_r33, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r33, sp_r34, sp_ok34, var_ecx(), stack(5));
  ghost var sp_r35, sp_ok35, sp_c35, sp_b35 := sp_lemma_block(sp_b34, sp_r34, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r34, sp_r35, sp_ok35, stack(14), var_ecx());
  lemma_BitwiseCommutative(uint32(sp_eval_op(sp_r35, var_ecx())), uint32(sp_eval_op(sp_r35, var_ebx())));
  ghost var sp_r37, sp_ok37, sp_c37, sp_b37 := sp_lemma_block(sp_b35, sp_r35, sp_r, sp_ok);
  sp_lemma_And32(sp_r35, sp_r37, sp_ok37, var_ecx(), var_ebx());
  lemma_BitwiseCommutative(uint32(sp_eval_op(sp_r37, var_ecx())), uint32(sp_eval_op(sp_r37, var_edx())));
  ghost var sp_r39, sp_ok39, sp_c39, sp_b39 := sp_lemma_block(sp_b37, sp_r37, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r37, sp_r39, sp_ok39, var_ecx(), var_edx());
  forall 
    ensures sp_eval_op(sp_r39, var_ecx()) == int(Ch(uint32(sp_eval_op(sp_old_s, stack(4))), uint32(sp_eval_op(sp_old_s, stack(5))), uint32(sp_eval_op(sp_old_s, stack(6)))))
  {
    reveal_Ch();
  }
  ghost var sp_r41, sp_ok41, sp_c41, sp_b41 := sp_lemma_block(sp_b39, sp_r39, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r39, sp_r41, sp_ok41, var_edx(), var_ebx());
  ghost var sp_r42, sp_ok42, sp_c42, sp_b42 := sp_lemma_block(sp_b41, sp_r41, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r41, sp_r42, sp_ok42, var_edi(), var_ebx());
  ghost var sp_r43, sp_ok43, sp_c43, sp_b43 := sp_lemma_block(sp_b42, sp_r42, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r42, sp_r43, sp_ok43, var_edx(), sp_op_const(6));
  ghost var sp_r44, sp_ok44, sp_c44, sp_b44 := sp_lemma_block(sp_b43, sp_r43, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r43, sp_r44, sp_ok44, var_edi(), sp_op_const(11));
  ghost var sp_r45, sp_ok45, sp_c45, sp_b45 := sp_lemma_block(sp_b44, sp_r44, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r44, sp_r45, sp_ok45, var_edx(), var_edi());
  ghost var sp_r46, sp_ok46, sp_c46, sp_b46 := sp_lemma_block(sp_b45, sp_r45, sp_r, sp_ok);
  sp_lemma_Ror32(sp_r45, sp_r46, sp_ok46, var_ebx(), sp_op_const(25));
  ghost var sp_r47, sp_ok47, sp_c47, sp_b47 := sp_lemma_block(sp_b46, sp_r46, sp_r, sp_ok);
  sp_lemma_Xor32(sp_r46, sp_r47, sp_ok47, var_edx(), var_ebx());
  forall 
    ensures sp_eval_op(sp_r47, var_edx()) == int(BSIG1(uint32(sp_eval_op(sp_old_s, stack(4)))))
  {
    reveal_BSIG1();
  }
  ghost var sp_r49, sp_ok49, sp_c49, sp_b49 := sp_lemma_block(sp_b47, sp_r47, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r47, sp_r49, sp_ok49, var_ebx(), stack(7));
  ghost var sp_r50, sp_ok50, sp_c50, sp_b50 := sp_lemma_block(sp_b49, sp_r49, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r49, sp_r50, sp_ok50, var_ebx(), var_edx());
  ghost var sp_r51, sp_ok51, sp_c51, sp_b51 := sp_lemma_block(sp_b50, sp_r50, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r50, sp_r51, sp_ok51, var_ebx(), var_ecx());
  ghost var sp_r52, sp_ok52, sp_c52, sp_b52 := sp_lemma_block(sp_b51, sp_r51, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r51, sp_r52, sp_ok52, var_ebx(), sp_op_const(K));
  ghost var sp_r53, sp_ok53, sp_c53, sp_b53 := sp_lemma_block(sp_b52, sp_r52, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r52, sp_r53, sp_ok53, var_ecx(), W);
  ghost var sp_r54, sp_ok54, sp_c54, sp_b54 := sp_lemma_block(sp_b53, sp_r53, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r53, sp_r54, sp_ok54, var_ebx(), var_ecx());
  ghost var sp_r55, sp_ok55, sp_c55, sp_b55 := sp_lemma_block(sp_b54, sp_r54, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r54, sp_r55, sp_ok55, var_eax(), var_ebx());
  ghost var sp_r56, sp_ok56, sp_c56, sp_b56 := sp_lemma_block(sp_b55, sp_r55, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r55, sp_r56, sp_ok56, stack(8), var_eax());
  ghost var sp_r57, sp_ok57, sp_c57, sp_b57 := sp_lemma_block(sp_b56, sp_r56, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r56, sp_r57, sp_ok57, var_eax(), stack(3));
  ghost var sp_r58, sp_ok58, sp_c58, sp_b58 := sp_lemma_block(sp_b57, sp_r57, sp_r, sp_ok);
  sp_lemma_Add32Wrap(sp_r57, sp_r58, sp_ok58, var_eax(), var_ebx());
  ghost var sp_r59, sp_ok59, sp_c59, sp_b59 := sp_lemma_block(sp_b58, sp_r58, sp_r, sp_ok);
  sp_lemma_Mov32(sp_r58, sp_r59, sp_ok59, stack(12), var_eax());
  assert ((TBlk(currentBlock) && TBlk(currentBlock + 1)) && TStep(currentStep)) && TStep(currentStep + 1);
  next_atoh := atoh_c(uint32(sp_eval_op(sp_r59, stack(8))), uint32(sp_eval_op(sp_r59, stack(9))), uint32(sp_eval_op(sp_r59, stack(10))), uint32(sp_eval_op(sp_r59, stack(11))), uint32(sp_eval_op(sp_r59, stack(12))), uint32(sp_eval_op(sp_r59, stack(13))), uint32(sp_eval_op(sp_r59, stack(14))), uint32(sp_eval_op(sp_r59, stack(15))));
  next_z := SHA256Trace_c(z.M, z.H, z.W, SeqDrop(z.atoh, int(currentBlock)) + SeqBuild(SeqAppendElt(z.atoh[currentBlock], next_atoh)));
  ghost var next_s := currentState.(atoh := next_atoh);
  lemma_SHA256TransitionOKAfterSettingAtoH(z, currentState, next_z, next_s, currentBlock, currentStep);
  sp_lemma_empty(sp_r59, sp_r, sp_ok);
}

method Main()
{
  printHeader();
  var n := printCode(sp_code_ComputeOneStep_SHA256_spartan(33, OHeap(5000, X86Uint32)), 0);
  printFooter();
}

