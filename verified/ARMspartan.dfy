include "ARMdef.dfy"

//-----------------------------------------------------------------------------
// Utilities 
//-----------------------------------------------------------------------------
function pow2_32():int { 0x1_0000_0000 }
predicate isUInt32(i:int) { 0 <= i < pow2_32() }

//-----------------------------------------------------------------------------
// Sequence Utilities
//-----------------------------------------------------------------------------
function SeqLength<T>(s:seq<T>) : int { |s| }
function SeqDrop<T>(s:seq<T>, tail:int) : seq<T> 
    requires 0 <= tail <= |s|;                                           
    { s[..tail] }
function SeqAppendElt<T>(s:seq<T>, elt:T) : seq<T> { s + [elt] }
function SeqBuild<T>(elt:T) : seq<T> { [elt] }

//-----------------------------------------------------------------------------
// Spartan Types
//-----------------------------------------------------------------------------
type sp_int = int
type sp_bool = bool
type sp_operand = operand 
type sp_cmp = obool
type sp_code = code
type sp_codes = codes
type sp_state = state

//-----------------------------------------------------------------------------
// Spartan-Verification Interface
//-----------------------------------------------------------------------------
function sp_eval_op(s:state, o:operand):int requires ValidOperand(s, o); { OperandContents(s, o) }

function method sp_CNil():codes { CNil }
function sp_cHead(b:codes):code requires b.sp_CCons? { b.hd }
predicate sp_cHeadIs(b:codes, c:code) { b.sp_CCons? && b.hd == c }
predicate sp_cTailIs(b:codes, t:codes) { b.sp_CCons? && b.tl == t }

function method fromOperand(o:operand):operand { o }
function method sp_op_const(n:int):operand { OConst(n) }

function method sp_cmp_eq(o1:operand, o2:operand):obool { OCmp(OEq, o1, o2) }
function method sp_cmp_ne(o1:operand, o2:operand):obool { OCmp(ONe, o1, o2) }
function method sp_cmp_le(o1:operand, o2:operand):obool { OCmp(OLe, o1, o2) }
function method sp_cmp_ge(o1:operand, o2:operand):obool { OCmp(OGe, o1, o2) }
function method sp_cmp_lt(o1:operand, o2:operand):obool { OCmp(OLt, o1, o2) }
function method sp_cmp_gt(o1:operand, o2:operand):obool { OCmp(OGt, o1, o2) }

function method sp_Block(block:codes):code { Block(block) }
function method sp_IfElse(ifb:obool, ift:code, iff:code):code { IfElse(ifb, ift, iff) }
function method sp_While(whileb:obool, whilec:code):code { While(whileb, whilec) }

function method sp_get_block(c:code):codes requires c.Block? { c.block }
function method sp_get_ifCond(c:code):obool requires c.IfElse? { c.ifCond }
function method sp_get_ifTrue(c:code):code requires c.IfElse? { c.ifTrue }
function method sp_get_ifFalse(c:code):code requires c.IfElse? { c.ifFalse }
function method sp_get_whileCond(c:code):obool requires c.While? { c.whileCond }
function method sp_get_whileBody(c:code):code requires c.While? { c.whileBody }

//-----------------------------------------------------------------------------
// Stack
//-----------------------------------------------------------------------------
// function method stack(slot:int):operand {  OVar(IdStackSlot(slot)) }
// function stackval(s:sp_state, o:operand):int requires ValidOperand(s, o); { sp_eval_op(s, o) }
// predicate NonEmptyStack(s:sp_state) { s.stack != [] }
// predicate StackContains(s:sp_state, slot:int) 
//     requires NonEmptyStack(s);
//     { stack(slot).x in s.stack[0].locals }

//-----------------------------------------------------------------------------
// Heap
//-----------------------------------------------------------------------------
// predicate HeapOperand(o:operand) { o.OHeap? }

//-----------------------------------------------------------------------------
// Register Validity
//-----------------------------------------------------------------------------
predicate ValidRegisters(s:sp_state)
{
	( forall i:int :: 0 <= i <= 12 ==> ValidOperand(s, op_r(i)) ) &&
		( forall m:Mode :: ValidOperand(s, op_sp(m)) ) &&
		( forall m:Mode :: ValidOperand(s, op_lr(m)) )
}

//-----------------------------------------------------------------------------
// Instruction Generation
//-----------------------------------------------------------------------------
function method{:opaque} sp_code_Add(dst:operand, src1:operand,
	src2:operand):code { Ins(Add(dst, src1, src2)) }
//TODO: everything else!

//-----------------------------------------------------------------------------
// Instruction Lemmas
//-----------------------------------------------------------------------------
lemma sp_lemma_Add(s:state, r:state, ok:bool,
	dst:operand, src1:operand, src2:operand)
	requires ValidOperand(s,src1);
	requires ValidOperand(s,src2);
	requires ValidDestinationOperand(s, dst);
	requires sp_eval(sp_code_Add(dst, src1, src2), s, r, ok);
	requires 0 <= OperandContents(s, dst) < MaxVal();
	requires 0 <= OperandContents(s, src1) < MaxVal();
	requires 0 <= OperandContents(s, src2) < MaxVal();
	requires 0 <= OperandContents(s, src1) + OperandContents(s, src2) < MaxVal();
	ensures  evalUpdate(s, dst, OperandContents(s, src1) +
		OperandContents(s, src2), r, ok);
	ensures  ok;
	ensures  0 <= OperandContents(r, dst) < MaxVal();
{
	reveal_sp_eval();
	reveal_sp_code_Add();
}
//TODO: everything else!

//-----------------------------------------------------------------------------
// Control Flow Lemmas
//-----------------------------------------------------------------------------

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
