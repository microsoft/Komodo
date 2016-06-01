// Dafny-Spartan interface

include "x86def.dfy"

type sp_int = int
type sp_bool = bool
type sp_operand = oprnd // TODO: rename oprnd -> operand
type sp_cmp = obool
type sp_code = code
type sp_codes = codes
type sp_state = state
function sp_eval_op(s:state, o:oprnd):int requires ValidOperand(s, o); { OperandContents(s, o) }

function pow2_32():int { 0x1_0000_0000 }
predicate isUInt32(i:int) { 0 <= i < pow2_32() }

function method sp_CNil():codes { CNil }
function sp_cHead(b:codes):code requires b.sp_CCons? { b.hd }
predicate sp_cHeadIs(b:codes, c:code) { b.sp_CCons? && b.hd == c }
predicate sp_cTailIs(b:codes, t:codes) { b.sp_CCons? && b.tl == t }

function method fromOperand(o:oprnd):oprnd { o }
function method sp_op_const(n:int):oprnd { OConst(n) }

function method sp_cmp_eq(o1:oprnd, o2:oprnd):obool { OCmp(OEq, o1, o2) }
function method sp_cmp_ne(o1:oprnd, o2:oprnd):obool { OCmp(ONe, o1, o2) }
function method sp_cmp_le(o1:oprnd, o2:oprnd):obool { OCmp(OLe, o1, o2) }
function method sp_cmp_ge(o1:oprnd, o2:oprnd):obool { OCmp(OGe, o1, o2) }
function method sp_cmp_lt(o1:oprnd, o2:oprnd):obool { OCmp(OLt, o1, o2) }
function method sp_cmp_gt(o1:oprnd, o2:oprnd):obool { OCmp(OGt, o1, o2) }

function method sp_Block(block:codes):code { Block(block) }
function method sp_IfElse(ifb:obool, ift:code, iff:code):code { IfElse(ifb, ift, iff) }
function method sp_While(whileb:obool, whilec:code):code { While(whileb, whilec) }

function method sp_get_block(c:code):codes requires c.Block? { c.block }
function method sp_get_ifCond(c:code):obool requires c.IfElse? { c.ifCond }
function method sp_get_ifTrue(c:code):code requires c.IfElse? { c.ifTrue }
function method sp_get_ifFalse(c:code):code requires c.IfElse? { c.ifFalse }
function method sp_get_whileCond(c:code):obool requires c.While? { c.whileCond }
function method sp_get_whileBody(c:code):code requires c.While? { c.whileBody }

function method stack(slot:int):oprnd {  OVar(IdStackSlot(slot)) }
function stackval(s:sp_state, o:oprnd):int requires ValidOperand(s, o); { sp_eval_op(s, o) }
predicate NonEmptyStack(s:sp_state) { s.stack != [] }
predicate StackContains(s:sp_state, slot:int) 
    requires NonEmptyStack(s);
    { stack(slot).x in s.stack[0].locals }

predicate StackContainsRange(s:sp_state, start_slot:int, end_slot:int) 
{ 
    NonEmptyStack(s)
 && forall slot {:trigger stack(slot).x in s.stack[0].locals} :: //{:trigger sp_eval_op(s, stack(slot))} :: 
        start_slot <= slot < end_slot ==> stack(slot).x in s.stack[0].locals 
                                       //&& 0 <= sp_eval_op(s, stack(slot)) < 0x1_0000_0000
}

predicate ValidRegisters(s:sp_state)
{
    ValidOperand(s, var_eax()) 
 && ValidOperand(s, var_ebx()) 
 && ValidOperand(s, var_ecx()) 
 && ValidOperand(s, var_edx()) 
 && ValidOperand(s, var_edi())
 && ValidOperand(s, var_esi())
 && ValidOperand(s, var_ebp())
}

predicate HeapOperand(o:oprnd) { o.OHeap? }

function SeqLength<T>(s:seq<T>) : int { |s| }
function SeqDrop<T>(s:seq<T>, tail:int) : seq<T> 
    requires 0 <= tail <= |s|;                                           
    { s[..tail] }
function SeqAppendElt<T>(s:seq<T>, elt:T) : seq<T> { s + [elt] }
function SeqBuild<T>(elt:T) : seq<T> { [elt] }

function method{:opaque} sp_code_incr(o:oprnd):code { Ins(Add32(o, OConst(1))) }
function method{:opaque} sp_code_decr(o:oprnd):code { Ins(Sub32(o, OConst(1))) }
function method{:opaque} sp_code_rand(o:oprnd):code { Ins(Rand(o)) }
function method{:opaque} sp_code_Mov32(dst:oprnd, src:oprnd):code { Ins(Mov32(dst, src)) }
function method{:opaque} sp_code_Add32(dst:oprnd, src:oprnd):code { Ins(Add32(dst, src)) }
function method{:opaque} sp_code_Add32Wrap(dst:oprnd, src:oprnd):code { Ins(Add32(dst, src)) }
function method{:opaque} sp_code_Xor32(dst:oprnd, src:oprnd):code { Ins(Xor32(dst, src)) }
function method{:opaque} sp_code_And32(dst:oprnd, src:oprnd):code { Ins(And32(dst, src)) }
function method{:opaque} sp_code_Not32(dst:oprnd):code { Ins(Not32(dst)) }
function method{:opaque} sp_code_AddCarry(dst:oprnd, src:oprnd):code { Ins(AddCarry(dst, src)) }
function method{:opaque} sp_code_GetCf(dst:oprnd):code { Ins(GetCf(dst)) }
function method{:opaque} sp_code_Rol32(dst:oprnd, src:oprnd):code { Ins(Rol32(dst, src)) }
function method{:opaque} sp_code_Ror32(dst:oprnd, src:oprnd):code { Ins(Ror32(dst, src)) }
function method{:opaque} sp_code_Shl32(dst:oprnd, src:oprnd):code { Ins(Shl32(dst, src)) }
function method{:opaque} sp_code_Shr32(dst:oprnd, src:oprnd):code { Ins(Shr32(dst, src)) }

lemma sp_lemma_incr(s:state, r:state, ok:bool, o:oprnd)
  requires Valid32BitDestinationOperand(s, o)
  requires sp_eval(sp_code_incr(o), s, r, ok)
  requires 0 <= eval_op(s, o) <= 1000
  ensures  evalUpdateAndHavocFlags(s, o, eval_op(s, o) + 1, r, ok)
{
  reveal_sp_eval();
  reveal_sp_code_incr();
}

lemma sp_lemma_decr(s:state, r:state, ok:bool, o:oprnd)
  requires Valid32BitDestinationOperand(s, o)
  requires sp_eval(sp_code_decr(o), s, r, ok)
  requires 1 <= eval_op(s, o) <= 1000
  ensures  evalUpdateAndHavocFlags(s, o, eval_op(s, o) - 1, r, ok)
{
  reveal_sp_eval();
  reveal_sp_code_decr();
}

lemma sp_lemma_rand(s:state, r:state, ok:bool, o:oprnd)
  requires sp_eval(sp_code_rand(o), s, r, ok)
  requires Valid32BitDestinationOperand(s, o)
  ensures  ok
  ensures  IdX86Reg(X86Eflags) in r.globals
  ensures  exists n:nat :: evalUpdateAndHavocFlags(s, o, n, r, ok)
  ensures  0 <= OperandContents(r, o) < GetValueLimitForX86Type(X86Uint32)
{
  reveal_sp_eval();
  reveal_sp_code_rand();
}

lemma sp_lemma_Mov32(s:state, r:state, ok:bool, dst:oprnd, src:oprnd)
  requires Valid32BitOperand(s, src);
  requires Valid32BitDestinationOperand(s, dst);
  requires sp_eval(sp_code_Mov32(dst, src), s, r, ok);
  ensures  evalUpdateAndMaintainFlags(s, dst, OperandContents(s, src), r, ok);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
{
  reveal_sp_eval();
  reveal_sp_code_Mov32();
  assert OperandContents(r, dst) == OperandContents(s, src);
}

lemma sp_lemma_Add32(s:state, r:state, ok:bool, dst:oprnd, src:oprnd)
  requires Valid32BitOperand(s, src);
  requires Valid32BitDestinationOperand(s, dst);
  requires sp_eval(sp_code_Add32(dst, src), s, r, ok);
  requires 0 <= OperandContents(s, dst) < GetValueLimitForX86Type(X86Uint32);
  requires 0 <= OperandContents(s, src) < GetValueLimitForX86Type(X86Uint32);
  requires 0 <= OperandContents(s, dst) + OperandContents(s, src) < GetValueLimitForX86Type(X86Uint32);
  ensures  evalUpdateAndHavocFlags(s, dst, OperandContents(s, dst) + OperandContents(s, src), r, ok);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
{
  reveal_sp_eval();
  reveal_sp_code_Add32();
}

lemma sp_lemma_Add32Wrap(s:state, r:state, ok:bool, dst:oprnd, src:oprnd)
  requires Valid32BitOperand(s, src);
  requires Valid32BitDestinationOperand(s, dst);
  requires sp_eval(sp_code_Add32Wrap(dst, src), s, r, ok);
  requires 0 <= OperandContents(s, dst) < GetValueLimitForX86Type(X86Uint32);
  requires 0 <= OperandContents(s, src) < GetValueLimitForX86Type(X86Uint32);
  ensures  evalUpdateAndHavocFlags(s, dst, (OperandContents(s, dst) + OperandContents(s, src)) % 0x1_0000_0000, r, ok);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
  ensures  OperandContents(r, dst) == int(BitwiseAdd32(uint32(OperandContents(s, dst)), uint32(OperandContents(s, src))));
{
  reveal_sp_eval();
  reveal_sp_code_Add32Wrap();
}

lemma sp_lemma_Xor32(s:state, r:state, ok:bool, dst:oprnd, src:oprnd)
  requires Valid32BitOperand(s, src);
  requires Valid32BitDestinationOperand(s, dst);
  requires 0 <= OperandContents(s, dst) < GetValueLimitForX86Type(X86Uint32);
  requires 0 <= OperandContents(s, src) < GetValueLimitForX86Type(X86Uint32);
  requires sp_eval(sp_code_Xor32(dst, src), s, r, ok)
  ensures  evalUpdateAndHavocFlags(s, dst, xor32(OperandContents(s, dst), OperandContents(s, src)), r, ok);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
{
  reveal_sp_eval();
  reveal_sp_code_Xor32();
}

lemma sp_lemma_And32(s:state, r:state, ok:bool, dst:oprnd, src:oprnd)
  requires Valid32BitOperand(s, src);
  requires Valid32BitDestinationOperand(s, dst);
  requires 0 <= OperandContents(s, dst) < GetValueLimitForX86Type(X86Uint32);
  requires 0 <= OperandContents(s, src) < GetValueLimitForX86Type(X86Uint32);
  requires sp_eval(sp_code_And32(dst, src), s, r, ok)
  ensures  evalUpdateAndHavocFlags(s, dst, and32(OperandContents(s, dst), OperandContents(s, src)), r, ok);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
{
  reveal_sp_eval();
  reveal_sp_code_And32();
}

lemma sp_lemma_Not32(s:state, r:state, ok:bool, dst:oprnd)
  requires Valid32BitDestinationOperand(s, dst);
  requires sp_eval(sp_code_Not32(dst), s, r, ok)
  requires 0 <= OperandContents(s, dst) < GetValueLimitForX86Type(X86Uint32);
  ensures  evalUpdateAndHavocFlags(s, dst, not32(OperandContents(s, dst)), r, ok);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
{
  reveal_sp_eval();
  reveal_sp_code_Not32();
}

lemma sp_lemma_AddCarry(s:state, r:state, ok:bool, dst:oprnd, src:oprnd)
  requires Valid32BitOperand(s, src);
  requires Valid32BitDestinationOperand(s, dst);
  requires sp_eval(sp_code_AddCarry(dst, src), s, r, ok)
  ensures  var old_carry := if Cf(flags(s)) then 1 else 0;
           var sum := OperandContents(s, dst) + OperandContents(s, src) + old_carry;
              evalUpdateAndHavocFlags(s, dst, sum % 0x1_0000_0000, r, ok)
           && Cf(r.globals[IdX86Reg(X86Eflags)]) == (sum >= 0x1_0000_0000);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
{
  reveal_sp_eval();
  reveal_sp_code_AddCarry();
}

lemma sp_lemma_Rol32(s:state, r:state, ok:bool, dst:oprnd, amount:oprnd)
  requires Valid32BitDestinationOperand(s, dst);
  requires amount.OConst?;
  requires 0 <= amount.n < 32;
  requires sp_eval(sp_code_Rol32(dst, amount), s, r, ok)
  ensures  evalUpdateAndHavocFlags(s, dst, rol32(eval_op(s, dst), amount.n), r, ok);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
{
  reveal_sp_eval();
  reveal_sp_code_Rol32();
}

lemma sp_lemma_Ror32(s:state, r:state, ok:bool, dst:oprnd, amount:oprnd)
  requires Valid32BitDestinationOperand(s, dst);
  requires amount.OConst?;
  requires 0 <= amount.n < 32;
  requires sp_eval(sp_code_Ror32(dst, amount), s, r, ok)
  ensures  evalUpdateAndHavocFlags(s, dst, ror32(eval_op(s, dst), amount.n), r, ok);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
{
  reveal_sp_eval();
  reveal_sp_code_Ror32();
}

lemma sp_lemma_Shl32(s:state, r:state, ok:bool, dst:oprnd, amount:oprnd)
  requires Valid32BitDestinationOperand(s, dst);
  requires amount.OConst?;
  requires 0 <= amount.n < 32;
  requires sp_eval(sp_code_Shl32(dst, amount), s, r, ok)
  ensures  evalUpdateAndHavocFlags(s, dst, shl32(eval_op(s, dst), amount.n), r, ok);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
{
  reveal_sp_eval();
  reveal_sp_code_Shl32();
}

lemma sp_lemma_Shr32(s:state, r:state, ok:bool, dst:oprnd, amount:oprnd)
  requires Valid32BitDestinationOperand(s, dst);
  requires amount.OConst?;
  requires 0 <= amount.n < 32;
  requires sp_eval(sp_code_Shr32(dst, amount), s, r, ok)
  ensures  evalUpdateAndHavocFlags(s, dst, shr32(eval_op(s, dst), amount.n), r, ok);
  ensures  ok;
  ensures  0 <= OperandContents(r, dst) < GetValueLimitForX86Type(X86Uint32);
{
  reveal_sp_eval();
  reveal_sp_code_Shr32();
}

lemma sp_lemma_GetCf(s:state, r:state, ok:bool, dst:oprnd)
  requires Valid32BitDestinationOperand(s, dst);
  requires sp_eval(sp_code_GetCf(dst), s, r, ok);
  requires 0 <= OperandContents(s, dst) < 256;
  ensures  evalUpdateAndMaintainFlags(s, dst, clear_low_byte(OperandContents(s, dst)) + if Cf(flags(s)) then 1 else 0, r, ok);
  ensures  ok;
  ensures  OperandContents(r, dst) == if Cf(flags(s)) then 1 else 0;
{
  reveal_sp_eval();
  reveal_sp_code_GetCf();
}

lemma sp_lemma_empty(s:state, r:state, ok:bool)
  requires sp_eval(Block(sp_CNil()), s, r, ok)
  ensures  ok
  ensures  r == s
{
  reveal_sp_eval();
}

lemma sp_lemma_block(b:codes, s0:state, r:state, ok:bool) returns(r1:state, ok1:bool, c0:code, b1:codes)
  requires b.sp_CCons?
  requires sp_eval(Block(b), s0, r, ok)
  ensures  b == sp_CCons(c0, b1)
  ensures  sp_eval(c0, s0, r1, ok1)
  ensures  ok1 ==> sp_eval(Block(b1), r1, r, ok)
{
  reveal_sp_eval();
  assert evalBlock(b, s0, r, ok);
  r1, ok1 :| sp_eval(b.hd, s0, r1, ok1) && (if !ok1 then !ok else evalBlock(b.tl, r1, r, ok));
  c0 := b.hd;
  b1 := b.tl;
}

lemma sp_lemma_ifElse(ifb:obool, ct:code, cf:code, s:state, r:state, ok:bool) returns(cond:bool)
  requires ValidOperand(s, ifb.o1);
  requires ValidOperand(s, ifb.o2);
  requires sp_eval(IfElse(ifb, ct, cf), s, r, ok)
  ensures  cond == evalOBool(s, ifb)
  ensures  (if cond then sp_eval(ct, s, r, ok) else sp_eval(cf, s, r, ok))
{
  reveal_sp_eval();
  cond := evalOBool(s, ifb);
}

// HACK
lemma unpack_eval_while(b:obool, c:code, s:state, r:state, ok:bool)
  requires evalCode(While(b, c), s, r, ok)
  ensures  exists n:nat :: evalWhile(b, c, n, s, r, ok)
{
}

predicate{:opaque} evalWhileOpaque(b:obool, c:code, n:nat, s:state, r:state, ok:bool) { evalWhile(b, c, n, s, r, ok) }

predicate sp_whileInv(b:obool, c:code, n:int, r1:state, ok1:bool, r2:state, ok2:bool)
{
  n >= 0 && ok1 && evalWhileOpaque(b, c, n, r1, r2, ok2)
}

lemma sp_lemma_while(b:obool, c:code, s:state, r:state, ok:bool) returns(n:nat, r':state, ok':bool)
  requires ValidOperand(s, b.o1)
  requires ValidOperand(s, b.o2)
  requires sp_eval(While(b, c), s, r, ok)
  ensures  evalWhileOpaque(b, c, n, s, r, ok)
  ensures  ok'
  ensures  r' == s
{
  reveal_sp_eval();
  reveal_evalWhileOpaque();
  unpack_eval_while(b, c, s, r, ok);
  n :| evalWhile(b, c, n, s, r, ok);
  ok' := true;
  r' := s;
}

lemma sp_lemma_whileTrue(b:obool, c:code, n:nat, s:state, r:state, ok:bool) returns(r':state, ok':bool)
  requires ValidOperand(s, b.o1)
  requires ValidOperand(s, b.o2)
  requires n > 0
  requires evalWhileOpaque(b, c, n, s, r, ok)
  ensures  evalOBool(s, b)
  ensures  sp_eval(c, s, r', ok')
  ensures  (if !ok' then !ok else evalWhileOpaque(b, c, n - 1, r', r, ok))
{
  reveal_sp_eval();
  reveal_evalWhileOpaque();
  r', ok' :| evalOBool(s, b) && evalCode(c, s, r', ok') && (if !ok' then !ok else evalWhile(b, c, n - 1, r', r, ok));
}

lemma sp_lemma_whileFalse(b:obool, c:code, s:state, r:state, ok:bool)
  requires ValidOperand(s, b.o1)
  requires ValidOperand(s, b.o2)
  requires evalWhileOpaque(b, c, 0, s, r, ok)
  ensures  !evalOBool(s, b)
  ensures  ok
  ensures  r == s
{
  reveal_sp_eval();
  reveal_evalWhileOpaque();
}

function ConcatenateCodes(code1:codes, code2:codes) : codes
{
    if code1.CNil? then
        code2
    else
        sp_CCons(code1.hd, ConcatenateCodes(code1.tl, code2))
}

lemma lemma_GetIntermediateStateBetweenCodeBlocks(s1:sp_state, s3:sp_state, code1:codes, code2:codes, codes1and2:codes, ok1and2:bool)
    returns (s2:sp_state, ok:bool)
    requires evalBlock(codes1and2, s1, s3, ok1and2);
    requires ConcatenateCodes(code1, code2) == codes1and2;
    ensures  evalBlock(code1, s1, s2, ok);
    ensures  if ok then evalBlock(code2, s2, s3, ok1and2) else !ok1and2;
    decreases code1;
{
    if code1.CNil? {
        s2 := s1;
        ok := true;
        return;
    }

    var s_mid, ok_mid :| evalCode(codes1and2.hd, s1, s_mid, ok_mid) && (if !ok_mid then !ok1and2 else evalBlock(codes1and2.tl, s_mid, s3, ok1and2));
    if ok_mid {
        s2, ok := lemma_GetIntermediateStateBetweenCodeBlocks(s_mid, s3, code1.tl, code2, codes1and2.tl, ok1and2);
    }
    else {
        ok := false;
    }
}
