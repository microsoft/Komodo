include "assembly.s.dfy"

datatype ARMReg = R(n:int)
datatype ARMtype = ARMUint32
datatype id = IdGlobal(g:int) | IdLocal(x:int)| IdStackSlot(s:int) | IdARMReg(r:ARMReg)
datatype operand = OConst(n:int) | OVar(x:id) | OHeap(addr:int)
datatype ocmp = OEq | ONe | OLe | OGe | OLt | OGt
datatype obool = OCmp(cmp:ocmp, o1:operand, o2:operand)

function method id_r(n:int): id
	requires 0 <= n <= 15
	{ IdARMReg(R(n)) }

function method var_r(n:int):operand
	requires 0 <= n <= 15
	{ OVar(id_r(n)) }

datatype ins =
	Add(dest:operand, src1:operand, src2:operand)

datatype codes = CNil | sp_CCons(hd:code, tl:codes)

datatype code =
  Ins(ins:ins)
| Block(block:codes)
| IfElse(ifCond:obool, ifTrue:code, ifFalse:code)
| While(whileCond:obool, whileBody:code)

datatype frame = Frame(locals:map<id, int>)
datatype state = State(globals:map<id, int>, stack:seq<frame>, heap:map<int, int>)

// Everything is word length. Words are 32b
function Truncate(n:int) : int { n % 0x1_0000_0000 }
function BytesPerWord() : int { 4 }
function MaxVal() : int { 0x1_0000_0000 }

predicate ValidState(s:state) 
{
	(forall r :: IdARMReg(r) in s.globals)
} 

predicate ValidHeapAddr(heap:map<int,int>, addr:int)
{
    addr % MaxVal() == 0
 	&& (forall i {:trigger addr + i in heap} :: 0 <= i < BytesPerWord() ==> addr + i in heap)
}

predicate ValidOperand(s:state, o:operand)
{
    match o
      case OVar(x) =>
        (match x
           case IdGlobal(g) => x in s.globals
           case IdLocal(l) => |s.stack| > 0 && x in s.stack[0].locals
           case IdStackSlot(n) => |s.stack| > 0 && x in s.stack[0].locals
           case IdARMReg(r) => x in s.globals)
      case OConst(n) => true
      case OHeap(addr) => ValidHeapAddr(s.heap, addr)
}

predicate ValidDestinationOperand(s:state, o:operand)
	{ o.OVar? && ValidOperand(s, o) }

function {:axiom} GetValueAtHeapAddress(heap:map<int,int>, addr:int) : int
    requires ValidHeapAddr(heap, addr);
    ensures  0 <= GetValueAtHeapAddress(heap, addr) < MaxVal();
    ensures  addr in heap && GetValueAtHeapAddress(heap, addr) == heap[addr];

function OperandContents(s:state, o:operand):int
    requires ValidOperand(s, o);
{
    match o
        case OConst(n) => n
        case OVar(x) =>
            (match x
                 case IdGlobal(g) => s.globals[x]
                 case IdLocal(l) => s.stack[0].locals[x]
                 case IdStackSlot(n) => s.stack[0].locals[x]
                 case IdARMReg(r) => s.globals[x]
            )
        case OHeap(addr) => GetValueAtHeapAddress(s.heap, addr)
}

function eval_op(s:state, o:operand):int
{
    if !ValidOperand(s, o) then 0xDEADBEEF
    else
        match o
            case OConst(n) => n
            case OVar(x) =>
                (match x
                     case IdGlobal(g)    => Truncate(s.globals[x])
                     case IdLocal(l)     => Truncate(s.stack[0].locals[x])
                     case IdStackSlot(n) => Truncate(s.stack[0].locals[x])
                     case IdARMReg(r)    => Truncate(s.globals[x])
                )
            case OHeap(addr) => GetValueAtHeapAddress(s.heap, addr)
}

predicate evalUpdate(s:state, o:operand, v:int, r:state, ok:bool)
    requires ValidDestinationOperand(s, o);
{
    if o.x.IdGlobal? || o.x.IdARMReg? then
        ok && r == s.(globals := s.globals[o.x := v])
    else
        ok && r == s.(stack := [s.stack[0].(locals := s.stack[0].locals[o.x := v])] + s.stack[1..])
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
        exists r0, ok0 :: evalCode(block.hd, s, r0, ok0) && (if !ok0 then !ok else evalBlock(block.tl, r0, r, ok))
}

predicate evalWhile(b:obool, c:code, n:nat, s:state, r:state, ok:bool)
  decreases c, n
{
    if ValidOperand(s, b.o1) && ValidOperand(s, b.o2) then
        if n == 0 then
            !evalOBool(s, b) && ok && r == s
        else
            exists r0, ok0 :: evalOBool(s, b) && evalCode(c, s, r0, ok0) && (if !ok0 then !ok else evalWhile(b, c, n - 1, r0, r, ok))
    else
        !ok
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
