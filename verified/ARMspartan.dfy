include "ARMdef.dfy"

//-----------------------------------------------------------------------------
// Utilities 
//-----------------------------------------------------------------------------
function method pow2_32():int { 0x1_0000_0000 }
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
function sp_eval_op(s:state, o:operand):int
    requires ValidOperand(s, o);
    { OperandContents(s, o) }

function sp_eval_mem(s:state, m:mem):int
    requires ValidMem(s, m);
    requires WordAligned(m.addr);
    { MemContents(s, m) }

predicate ValidMemRange(s:state, lwr:int, upr:int)
{
    forall i:int :: lwr <= i <= upr && WordAligned(i) ==>
        ValidMem(s, Address(i))
}

predicate MemRangeIs32(s:state, lwr:int, upr:int)
    requires ValidMemRange(s, lwr, upr);
{
    forall i:int {:trigger s.addresses[Address(i)]} ::
        lwr <= i <= upr && WordAligned(i) ==> isUInt32(addrval(s, i))
}

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
// This code is pretty much only used for stack-test
// function method stack(slot:int):operand { OMem(LocalVar(slot)) }
// function stackval(s:sp_state, o:operand):int requires ValidOperand(s, o); { sp_eval_op(s, o) }
// predicate NonEmptyStack(s:sp_state) { s.stack != [] }
// predicate StackContains(s:sp_state, slot:int) 
//     requires NonEmptyStack(s);
//     { stack(slot).x in s.stack[0].locals }
// 
// predicate StackContainsRange(s:sp_state, start_slot:int, end_slot:int) 
// { 
//     NonEmptyStack(s)
//  && forall slot {:trigger stack(slot).x in s.stack[0].locals} :: //{:trigger sp_eval_op(s, stack(slot))} :: 
//         start_slot <= slot < end_slot ==> stack(slot).x in s.stack[0].locals 
//                                        //&& 0 <= sp_eval_op(s, stack(slot)) < 0x1_0000_0000
// }

//-----------------------------------------------------------------------------
// Address Helper Functions
//-----------------------------------------------------------------------------
function addrval(s:sp_state, a:int):int
    requires ValidMem(s, Address(a))
    requires WordAligned(a)
{
    MemContents(s, Address(a))
}

//-----------------------------------------------------------------------------
// Instructions
//-----------------------------------------------------------------------------
function method{:opaque} sp_code_ADD(dst:operand, src1:operand,
    src2:operand):code { Ins(ADD(dst, src1, src2)) }

function method{:opaque} sp_code_SUB(dst:operand, src1:operand,
    src2:operand):code { Ins(SUB(dst, src1, src2)) }

function method{:opaque} sp_code_MUL(dst:operand, src1:operand,
    src2:operand):code { Ins(MUL(dst, src1, src2)) }

function method{:opaque} sp_code_UDIV(dst:operand, src1:operand,
    src2:operand):code { Ins(UDIV(dst, src1, src2)) }

function method{:opaque} sp_code_AND(dst:operand, src1:operand,
    src2:operand):code { Ins(AND(dst, src1, src2)) }

function method{:opaque} sp_code_ORR(dst:operand, src1:operand,
    src2:operand):code { Ins(ORR(dst, src1, src2)) }

function method{:opaque} sp_code_EOR(dst:operand, src1:operand,
    src2:operand):code { Ins(EOR(dst, src1, src2)) }

function method{:opaque} sp_code_ROR(dst:operand, src1:operand,
    src2:operand):code { Ins(ROR(dst, src1, src2)) }

function method{:opaque} sp_code_LSL(dst:operand, src1:operand,
    src2:operand):code { Ins(LSL(dst, src1, src2)) }

function method{:opaque} sp_code_LSR(dst:operand, src1:operand,
    src2:operand):code { Ins(LSR(dst, src1, src2)) }

function method{:opaque} sp_code_MVN(dst:operand, src:operand):code
    { Ins(MVN(dst, src)) }

function method{:opaque} sp_code_MOV(dst:operand, src:operand):code
    { Ins(MOV(dst, src)) }

function method{:opaque} sp_code_LDR(rd:operand, base:operand, ofs:operand):code
    { Ins(LDR(rd, base, ofs)) }

function method{:opaque} sp_code_STR(rd:operand, base:operand, ofs:operand):code
    { Ins(STR(rd, base, ofs)) }

function method{:opaque} sp_code_CPS(mod:operand):code
    { Ins(CPS(mod)) }

// Pseudoinstructions  
function method{:opaque} sp_code_incr(o:operand):code { Ins(ADD(o, o, OConst(1))) }
function method{:opaque} sp_code_plusEquals(o1:operand, o2:operand):code { Ins(ADD(o1, o1, o2)) }
function method{:opaque} sp_code_andEquals(o1:operand, o2:operand):code { Ins(AND(o1, o1, o2)) }
function method{:opaque} sp_code_xorEquals(o1:operand, o2:operand):code { Ins(EOR(o1, o1, o2)) }
// function method{:opaque} sp_code_push(o:operand):code { 
//     // Ins(SUB(OSP, OSP, OConst(4)))
//     var i1 := Ins(SUB(OSP, OSP, OConst(4)));
//     var i2 := Ins(STR(o, OSP, OConst(0)));
//     Block(sp_CCons( i1, sp_CCons(i2, CNil) ))
// }

function method{:opaque} sp_code_loadAddrOfGlobal(rd:operand, name:string):code
    { Ins(LDR_reloc(rd, name)) }

function method{:opaque} sp_code_LDRglobal(rd:operand, name:string, base:operand, ofs:operand):code
    { Ins(LDR(rd, base, ofs)) }

//-----------------------------------------------------------------------------
// Instruction Lemmas
//-----------------------------------------------------------------------------
lemma sp_lemma_ADD(s:state, r:state, ok:bool,
    dst:operand, src1:operand, src2:operand)
    requires ValidOperand(s,src1);
    requires ValidOperand(s,src2);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_ADD(dst, src1, src2), s, r, ok);
    requires 0 <= OperandContents(s, src1) < MaxVal();
    requires 0 <= OperandContents(s, src2) < MaxVal();
    requires 0 <= OperandContents(s, src1) + OperandContents(s, src2) < MaxVal();
    ensures  evalUpdate(s, dst, OperandContents(s, src1) +
        OperandContents(s, src2), r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_ADD();
}

lemma sp_lemma_SUB(s:state, r:state, ok:bool,
    dst:operand, src1:operand, src2:operand)
    requires ValidOperand(s,src1);
    requires ValidOperand(s,src2);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_SUB(dst, src1, src2), s, r, ok);
    requires 0 <= OperandContents(s, src1) < MaxVal();
    requires 0 <= OperandContents(s, src2) < MaxVal();
    requires 0 <= OperandContents(s, src1) - OperandContents(s, src2) < MaxVal();
    ensures  evalUpdate(s, dst, OperandContents(s, src1) -
        OperandContents(s, src2), r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_SUB();
}

lemma sp_lemma_MUL(s:state, r:state, ok:bool,
    dst:operand, src1:operand, src2:operand)
    requires ValidRegOperand(s,src1);
    requires ValidRegOperand(s,src2);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_MUL(dst, src1, src2), s, r, ok);
    requires 0 <= OperandContents(s, src1) < MaxVal();
    requires 0 <= OperandContents(s, src2) < MaxVal();
    requires 0 <= OperandContents(s, src1) * OperandContents(s, src2) < MaxVal();
    ensures  evalUpdate(s, dst, OperandContents(s, src1) *
        OperandContents(s, src2), r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_MUL();
}

lemma sp_lemma_UDIV(s:state, r:state, ok:bool,
    dst:operand, src1:operand, src2:operand)
    requires ValidOperand(s,src1);
    requires ValidOperand(s,src2);
    requires ValidDestinationOperand(s, dst);
    requires OperandContents(s,src2) > 0;
    requires sp_eval(sp_code_UDIV(dst, src1, src2), s, r, ok);
    requires 0 <= OperandContents(s, src1) < MaxVal();
    requires 0 <= OperandContents(s, src2) < MaxVal();
    requires 0 <= OperandContents(s, src1) / OperandContents(s, src2) < MaxVal();
    ensures  evalUpdate(s, dst, OperandContents(s, src1) /
        OperandContents(s, src2), r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_UDIV();
}

lemma sp_lemma_AND(s:state, r:state, ok:bool,
    dst:operand, src1:operand, src2:operand)
    requires ValidOperand(s,src1);
    requires ValidOperand(s,src2);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_AND(dst, src1, src2), s, r, ok);
    requires 0 <= OperandContents(s, src1) < MaxVal();
    requires 0 <= OperandContents(s, src2) < MaxVal();
    ensures evalUpdate(s, dst, and32(eval_op(s, src1),
        eval_op(s, src2)), r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_AND();
}

lemma sp_lemma_ORR(s:state, r:state, ok:bool,
    dst:operand, src1:operand, src2:operand)
    requires ValidOperand(s,src1);
    requires ValidOperand(s,src2);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_ORR(dst, src1, src2), s, r, ok);
    requires 0 <= OperandContents(s, src1) < MaxVal();
    requires 0 <= OperandContents(s, src2) < MaxVal();
    ensures evalUpdate(s, dst, or32(eval_op(s, src1),
        eval_op(s, src2)), r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_ORR();
}

lemma sp_lemma_EOR(s:state, r:state, ok:bool,
    dst:operand, src1:operand, src2:operand)
    requires ValidOperand(s,src1);
    requires ValidOperand(s,src2);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_EOR(dst, src1, src2), s, r, ok);
    requires 0 <= OperandContents(s, src1) < MaxVal();
    requires 0 <= OperandContents(s, src2) < MaxVal();
    ensures evalUpdate(s, dst, xor32(eval_op(s, src1),
        eval_op(s, src2)), r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_EOR();
}

lemma sp_lemma_ROR(s:state, r:state, ok:bool,
    dst:operand, src1:operand, src2:operand)
    requires ValidOperand(s,src1);
    requires ValidOperand(s,src2);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_ROR(dst, src1, src2), s, r, ok);
    requires 0 <= OperandContents(s, src1) < MaxVal();
    requires 0 <= OperandContents(s, src2) < MaxVal();
    requires src2.OConst?;
    requires 0 <= eval_op(s, src2) < 32;
    ensures evalUpdate(s, dst, ror32(eval_op(s, src1),
        eval_op(s, src2)), r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_ROR();
}

lemma sp_lemma_LSL(s:state, r:state, ok:bool,
    dst:operand, src1:operand, src2:operand)
    requires ValidOperand(s,src1);
    requires ValidOperand(s,src2);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_LSL(dst, src1, src2), s, r, ok);
    requires 0 <= OperandContents(s, src1) < MaxVal();
    requires 0 <= OperandContents(s, src2) < MaxVal();
    requires src2.OConst?;
    requires 0 <= eval_op(s, src2) < 32;
    ensures evalUpdate(s, dst, shl32(eval_op(s, src1),
        eval_op(s, src2)), r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_LSL();
}

lemma sp_lemma_LSR(s:state, r:state, ok:bool,
    dst:operand, src1:operand, src2:operand)
    requires ValidOperand(s,src1);
    requires ValidOperand(s,src2);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_LSR(dst, src1, src2), s, r, ok);
    requires 0 <= OperandContents(s, src1) < MaxVal();
    requires 0 <= OperandContents(s, src2) < MaxVal();
    requires src2.OConst?;
    requires 0 <= eval_op(s, src2) < 32;
    ensures evalUpdate(s, dst, shr32(eval_op(s, src1),
        eval_op(s, src2)), r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_LSR();
}

lemma sp_lemma_MVN(s:state, r:state, ok:bool,
    dst:operand, src:operand)
    requires ValidOperand(s,src);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_MVN(dst, src), s, r, ok);
    requires 0 <= OperandContents(s, src) < MaxVal();
    ensures evalUpdate(s, dst, not32(eval_op(s, src)),
        r, ok);
    ensures  ok;
    ensures  0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_MVN();
}

lemma sp_lemma_MOV(s:state, r:state, ok:bool,
    dst:operand, src:operand)
    requires ValidOperand(s, src);
    requires ValidDestinationOperand(s, dst);
    requires sp_eval(sp_code_MOV(dst, src), s, r, ok);
    requires 0 <= OperandContents(s, src) < MaxVal();
    //requires !IsMemOperand(dst);
    //requires !IsMemOperand(src);
    ensures evalUpdate(s, dst, OperandContents(s, src), r, ok);
    ensures ok;
    ensures 0 <= OperandContents(r, dst) < MaxVal();
    ensures 0 <= OperandContents(r, dst) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_MOV();
}

lemma sp_lemma_LDR(s:state, r:state, ok:bool,
    rd:operand, base:operand, ofs:operand)
    requires ValidDestinationOperand(s, rd);
    requires ValidOperand(s, base);
    requires ValidOperand(s, ofs);
    requires ValidMem(s, addr_mem(s, base, ofs));
    requires sp_eval(sp_code_LDR(rd, base, ofs), s, r, ok);
    requires 0 <= OperandContents(s, base) < MaxVal();
    requires 0 <= OperandContents(s, ofs) < MaxVal();
    requires WordAligned(OperandContents(s, base) + OperandContents(s, ofs));
    requires 0 <= MemContents(s, Address(OperandContents(s, base) +
        OperandContents(s, ofs))) < MaxVal();
    // requires 0 <= OperandContents(s, addr_op(s, base, ofs)) < MaxVal();
    //requires IsMemOperand(addr);
    //requires !IsMemOperand(rd);
    // ensures evalUpdate(s, rd, eval_op(s, addr_op(s, base, ofs)), r, ok);
    // ensures evalUpdate(s, rd, eval_op(s, addr(eval_op(s,base), eval_op(s,ofs))), r, ok);
    ensures evalUpdate(s, rd, MemContents(s, Address(OperandContents(s, base) + OperandContents(s, ofs))), r, ok)
    ensures ValidOperand(r, base);
    ensures ValidOperand(r, ofs);
    ensures ok;
    ensures 0 <= OperandContents(r, rd) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_LDR();
}

lemma sp_lemma_STR(s:state, r:state, ok:bool,
    rd:operand, base:operand, ofs:operand)
    requires ValidRegOperand(s, rd);
    requires ValidOperand(s, base);
    requires ValidOperand(s, ofs);
    requires ValidMem(s, addr_mem(s, base, ofs));
    requires sp_eval(sp_code_STR(rd, base, ofs), s, r, ok);
    requires 0 <= OperandContents(s, rd) < MaxVal();
    requires WordAligned(OperandContents(s, base) + OperandContents(s, ofs));
    ensures evalMemUpdate(s, Address(OperandContents(s, base) + OperandContents(s, ofs)),
        OperandContents(s, rd), r, ok)
    ensures ok;
    ensures 0 <= MemContents(r, addr_mem(s, base, ofs)) < MaxVal();
{
    reveal_sp_eval();
    reveal_sp_code_STR();
}

lemma sp_lemma_CPS(s:state, r:state, ok:bool, mod:operand)
    requires ValidOperand(s, mod);
    requires sp_eval(sp_code_CPS(mod), s, r, ok);
    requires ValidModeEncoding(OperandContents(s, mod));
    requires 0 <= OperandContents(s, mod) < MaxVal();
    ensures  ok;
    ensures  evalModeUpdate(s, OperandContents(s, mod), r, ok);
{
    reveal_sp_eval();
    reveal_sp_code_CPS();
}

// Lemmas for frontend functions
lemma sp_lemma_incr(s:sp_state, r:sp_state, ok:bool, o:operand)
  requires ValidDestinationOperand(s, o)
  requires sp_eval(sp_code_incr(o), s, r, ok)
  requires 0 <= eval_op(s, o) + 1 < MaxVal();
  ensures ok;
  ensures  evalUpdate(s, o,
    OperandContents(s, o) + 1,
    r, ok)
{
  reveal_sp_eval();
  reveal_sp_code_incr();
}

// lemma sp_lemma_push(s:sp_state, r:sp_state, ok:bool, o:operand)
//     requires ValidDestinationOperand(s, OSP)
//     requires ValidOperand(s, o)
//     requires sp_eval(sp_code_push(o), s, r, ok)
//     requires 4 <= eval_op(s, o) < MaxVal()
//     requires ValidMem(s, Address(eval_op(s, OSP)))
//     ensures ok;
//     ensures  evalMemUpdate(s, Address(eval_op(s, OSP)),
//         eval_op(s, o), r, ok)
//     ensures  evalUpdate(s, OSP, eval_op(s, OSP) - 4, r, ok)
//     ensures  eval_op(r, OSP) == eval_op(s, OSP) - 4
//     ensures  addrval(r, eval_op(s, OSP)) == eval_op(s, o)
// {
//     reveal_sp_eval();
//     reveal_sp_code_push();
// }

lemma sp_lemma_plusEquals(s:sp_state, r:sp_state, ok:bool, o1:operand, o2:operand)
    requires ValidDestinationOperand(s, o1);
    requires ValidOperand(s, o2);
    requires ValidOperand(s, o1);
    requires sp_eval(sp_code_plusEquals(o1, o2), s, r, ok);
    requires 0 <= OperandContents(s, o1) < MaxVal();
    requires 0 <= OperandContents(s, o2) < MaxVal();
    requires 0 <= OperandContents(s, o1) + OperandContents(s, o2) < MaxVal();
    ensures evalUpdate(s, o1, OperandContents(s, o1) +
        OperandContents(s, o2), r, ok);
{
    reveal_sp_eval();
    reveal_sp_code_plusEquals();
}

lemma sp_lemma_andEquals(s:sp_state, r:sp_state, ok:bool, o1:operand, o2:operand)
    requires ValidDestinationOperand(s, o1);
    requires ValidOperand(s, o2);
    requires ValidOperand(s, o1);
    requires sp_eval(sp_code_andEquals(o1, o2), s, r, ok);
    requires 0 <= OperandContents(s, o1) < MaxVal();
    requires 0 <= OperandContents(s, o2) < MaxVal();
    ensures evalUpdate(s, o1, and32(eval_op(s, o1), eval_op(s, o2)), r, ok);
{
    reveal_sp_eval();
    reveal_sp_code_andEquals();
}

lemma sp_lemma_xorEquals(s:sp_state, r:sp_state, ok:bool, o1:operand, o2:operand)
    requires ValidDestinationOperand(s, o1);
    requires ValidOperand(s, o2);
    requires ValidOperand(s, o1);
    requires sp_eval(sp_code_xorEquals(o1, o2), s, r, ok);
    requires 0 <= OperandContents(s, o1) < MaxVal();
    requires 0 <= OperandContents(s, o2) < MaxVal();
    ensures evalUpdate(s, o1, xor32(eval_op(s, o1), eval_op(s, o2)), r, ok);
{
    reveal_sp_eval();
    reveal_sp_code_xorEquals();
}

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
