include "assembly.s.dfy"

//-----------------------------------------------------------------------------
// Microarchitectural State
//-----------------------------------------------------------------------------
datatype ARMReg = R(n:int) | SP(spm:Mode) | LR(lpm: Mode)
datatype Mode = User | System | Monitor |Abort | Undefined | FIQ

datatype operand = OConst(n:int) | OReg(r:ARMReg)
datatype id = GlobalVar(g:int) | LocalVar(l:int)
datatype memoperand =  MOId(x:id) | MOHeap(addr:int)

datatype frame = Frame(locals:map<id, int>)
datatype state = State(regs:map<ARMReg, int>,
					   globals:map<id, int>,
					   stack:seq<frame>,
					   heap:map<int, int>,
					   mode:Mode)

function method op_r(n:int):operand
	requires 0 <= n <= 12
	{ OReg(R(n)) }

function method op_sp(m:Mode):operand
	{ OReg(SP(m)) }

function method op_lr(m:Mode):operand
	{ OReg(LR(m)) }

//-----------------------------------------------------------------------------
// Instructions
//-----------------------------------------------------------------------------
datatype ins =
	Add(dest:operand, src1:operand, src2:operand)

//-----------------------------------------------------------------------------
// Code Representation
//-----------------------------------------------------------------------------
datatype ocmp = OEq | ONe | OLe | OGe | OLt | OGt
datatype obool = OCmp(cmp:ocmp, o1:operand, o2:operand)

datatype codes = CNil | sp_CCons(hd:code, tl:codes)

datatype code =
  Ins(ins:ins)
| Block(block:codes)
| IfElse(ifCond:obool, ifTrue:code, ifFalse:code)
| While(whileCond:obool, whileBody:code)

//-----------------------------------------------------------------------------
// Microarch-Related Utilities
//-----------------------------------------------------------------------------
function Truncate(n:int) : int { n % 0x1_0000_0000 }
function BytesPerWord() : int { 4 }
function MaxVal() : int { 0x1_0000_0000 }

//-----------------------------------------------------------------------------
// Validity
//-----------------------------------------------------------------------------
predicate ValidHeapAddr(heap:map<int,int>, addr:int)
{
    addr % MaxVal() == 0 &&
		(forall i {:trigger addr + i in heap} ::
			0 <= i < BytesPerWord() ==> addr + i in heap)
}

predicate ValidOperand(s:state, o:operand)
{
	match o
		case OConst(n) => true
		case OReg(r) => (match r
			case R(n) => r in s.regs 
			case SP(spm) => r in s.regs 
			case LR(lpm) => r in s.regs 
		)
}

predicate ValidDestinationOperand(s:state, o:operand)
	{ o.OReg? && ValidOperand(s, o) }

predicate ValidMemOperand(s:state, m:memoperand)
{
	match m
		case MOId(x) => (match x
			case GlobalVar(g) => x in s.globals
			case LocalVar(l)  => |s.stack| > 0 && x in s.stack[0].locals
		)
		case MOHeap(addr) => ValidHeapAddr(s.heap, addr)
}

//-----------------------------------------------------------------------------
// Evaluation
//-----------------------------------------------------------------------------
function {:axiom} GetValueAtHeapAddress(heap:map<int,int>, addr:int) : int
    requires ValidHeapAddr(heap, addr);
    ensures  0 <= GetValueAtHeapAddress(heap, addr) < MaxVal();
    ensures  addr in heap && GetValueAtHeapAddress(heap, addr) == heap[addr];

function OperandContents(s:state, o:operand): int
	requires ValidOperand(s,o)
{
	match o
		case OConst(n) => n
		case OReg(r) => s.regs[r]
}

function MemOperandContents(s:state, m:memoperand): int
	requires ValidMemOperand(s, m)
{
	match m
		case MOId(x) => (match x
			case GlobalVar(g) => s.globals[x]
			case LocalVar(l) => s.stack[0].locals[x]
		)
		case MOHeap(addr:int) => GetValueAtHeapAddress(s.heap, addr)
}


// eval_op and eval_memop may need to duplicate _Contents and remove requires
function eval_op(s:state, o:operand): int
	requires ValidOperand(s, o) { Truncate(OperandContents(s,o)) }

function eval_memop(s:state, m:memoperand): int
	requires ValidMemOperand(s, m) { Truncate(MemOperandContents(s,m)) }

predicate evalUpdate(s:state, o:operand, v:int, r:state, ok:bool)
	requires ValidDestinationOperand(s, o)
{
	ok && r == s.(regs := s.regs[o.r := v])
}

predicate evalMemUpdate(s:state, m:memoperand, v: int, r:state, ok:bool)
	requires ValidMemOperand(s, m);
{
	ok && match m
		case MOId(x) => (match x
			case GlobalVar(g) => r == s.(globals := s.globals[m.x := v])
			case LocalVar(l) => r == s.(stack :=
				[s.stack[0].(locals := s.stack[0].locals[m.x := v])] +
					s.stack[1..])
		)
		case MOHeap(addr:int) => false //Not sure why heap addresses aren't valid dest in x86def
}

function evalCmp(c:ocmp, i1:int, i2:int):bool
{
  match c
    case OEq => i1 == i2
    case ONe => i1 != i2
    case OLe => i1 <= i2
    case OGe => i1 >= i2
    case OLt => i1 <  i2
    case OGt => i1 >  i2
}

function evalOBool(s:state, o:obool):bool
    requires ValidOperand(s, o.o1);
    requires ValidOperand(s, o.o2);
{
    evalCmp(o.cmp, eval_op(s, o.o1), eval_op(s, o.o2))
}

predicate ValidInstruction(s:state, ins:ins)
{
	match ins
		case Add(dest, src1, src2) => ValidOperand(s, src1) &&
			ValidOperand(s, src2) && ValidDestinationOperand(s, dest)
}

predicate evalIns(ins:ins, s:state, r:state, ok:bool)
{
    if !ValidInstruction(s, ins) then !ok
    else match ins
		case Add(dst, src1, src2) => evalUpdate(s, dst,
			(OperandContents(s, src1) + OperandContents(s, src2) % MaxVal()),
			r, ok)
}

predicate evalBlock(block:codes, s:state, r:state, ok:bool)
{
    if block.CNil? then
        ok && r == s
    else
        exists r0, ok0 :: evalCode(block.hd, s, r0, ok0) &&
			(if !ok0 then !ok else evalBlock(block.tl, r0, r, ok))
}

predicate evalWhile(b:obool, c:code, n:nat, s:state, r:state, ok:bool)
  decreases c, n
{
    if ValidOperand(s, b.o1) && ValidOperand(s, b.o2) then
        if n == 0 then
            !evalOBool(s, b) && ok && r == s
        else
            exists r0, ok0 :: evalOBool(s, b) &&
				evalCode(c, s, r0, ok0) &&
				(if !ok0 then !ok else evalWhile(b, c, n - 1, r0, r, ok))
    else !ok
}

predicate evalCode(c:code, s:state, r:state, ok:bool)
  decreases c, 0
{
    match c
        case Ins(ins) => evalIns(ins, s, r, ok)
        case Block(block) => evalBlock(block, s, r, ok)
        // TODO: IfElse and While should havoc the flags
        case IfElse(cond, ifT, ifF) => if ValidOperand(s, cond.o1) && ValidOperand(s, cond.o2) then
                                           if evalOBool(s, cond) then
                                               evalCode(ifT, s, r, ok)
                                           else
                                               evalCode(ifF, s, r, ok)
                                       else
                                           !ok
        case While(cond, body) => exists n:nat :: evalWhile(cond, body, n, s, r, ok)
}

predicate{:opaque} sp_eval(c:code, s:state, r:state, ok:bool) { evalCode(c, s, r, ok) }
