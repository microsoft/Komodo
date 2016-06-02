include "ARMdef.dfy"

type sp_int = int
type sp_bool = bool
type sp_operand = operand 
type sp_cmp = obool
type sp_code = code
type sp_codes = codes
type sp_state = state
function sp_eval_op(s:state, o:operand):int requires ValidOperand(s, o); { OperandContents(s, o) }

function pow2_32():int { 0x1_0000_0000 }
predicate isUInt32(i:int) { 0 <= i < pow2_32() }

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

function method stack(slot:int):operand {  OVar(IdStackSlot(slot)) }
function stackval(s:sp_state, o:operand):int requires ValidOperand(s, o); { sp_eval_op(s, o) }
predicate NonEmptyStack(s:sp_state) { s.stack != [] }
predicate StackContains(s:sp_state, slot:int) 
    requires NonEmptyStack(s);
    { stack(slot).x in s.stack[0].locals }


predicate ValidRegisters(s:sp_state)
{
	forall i:int :: 0 <= i <= 15 ==> ValidOperand(s, var_r(i))
}
