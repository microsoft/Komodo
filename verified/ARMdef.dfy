include "assembly.s.dfy"

//-----------------------------------------------------------------------------
// Microarchitectural State
//-----------------------------------------------------------------------------
datatype ARMReg = R(n:int) | SP(spm:mode) | LR(lpm: mode)
// In FIQ, R8 to R12 are also banked

datatype mem = GlobalVar(g:int) | LocalVar(l:int) | Address(a:int)
datatype operand = OConst(n:int) | OReg(r:ARMReg) | OMem(x:mem) | OSP | OLR 

datatype frame = Frame(locals:map<mem, int>)
datatype state = State(regs:map<ARMReg, int>,
					   globals:map<mem, int>,
                       addresses:map<mem, int>,
					   stack:seq<frame>,
					   // heap:map<int, int>,
                       ns:bool,
                       mod:mode)
					   // cpsr:cpsr_val,
                       // spsr:map<mode, cpsr_val>)

// SCR.NS = non-secure bit

datatype cpsr_val = CPSR(
    // n:bool,             //Negative condition
    // z:bool,             //Zero condition
    // c:bool,             //Carry condition
    // v:bool,             //Overflow condition
    // a:bool,             //Abort mask
    // f:bool,             //FIQ mask
    m:mode)

datatype mode = User | Supervisor | Monitor |Abort | Undefined | FIQ
datatype priv = PL0 | PL1 // | PL2 // PL2 is only used in Hyp, not modeled


//-----------------------------------------------------------------------------
// State-related Utilities
//-----------------------------------------------------------------------------
function method op_r(n:int):operand
	requires 0 <= n <= 12
	{ OReg(R(n)) }

function method op_sp():operand
    { OSP }

function method op_lr():operand
    { OLR }

function method mode_of_state(s:state):mode
{
    // match s.cpsr
    //         case CPSR(m) => m
    s.mod
}

function method priv_of_mode(m:mode):priv
{
    match m
        case User => PL0
        case Supervisor => PL1
        case Monitor => PL1
        case Abort => PL1
        case Undefined => PL1
        case FIQ => PL1
}

function method priv_of_state(s:state):priv
    { priv_of_mode(mode_of_state(s)) }


function method mode_encoding(m:int):mode
    requires ValidMode(m)
{
         if m == 0x10 then User
    else if m == 0x11 then FIQ
    else if m == 0x13 then Supervisor
    else if m == 0x16 then Monitor
    else if m == 0x17 then Abort
    else if m == 0x1B then Undefined
    else User // should not happen
}

function addr_op(s:state, base:operand, ofs:operand):operand
    requires ValidOperand(s, base);
    requires ValidOperand(s, ofs);
{
    OMem(Address( eval_op(s, base) + eval_op(s, ofs) ))
}

//-----------------------------------------------------------------------------
// Instructions
//-----------------------------------------------------------------------------
datatype ins =
	  ADD(dstADD:operand, src1ADD:operand, src2ADD:operand)
	| SUB(dstSUB:operand, src1SUB:operand, src2SUB:operand)
	| AND(dstAND:operand, src1AND:operand, src2AND:operand)
	| ORR(dstOR:operand,  src1OR:operand,  src2OR:operand)
	| EOR(dstEOR:operand, src1EOR:operand, src2EOR:operand) // Also known as XOR
	| ROR(dstROR:operand, src1ROR:operand, src2ROR:operand)
	| LSL(dstLSL:operand, src1LSL:operand, src2LSL:operand)
	| LSR(dstLSR:operand, src1LSR:operand, src2LSR:operand)
    | MOV(dstMOV:operand, srcMOV:operand)
    | MVN(dstMVN:operand, srcMVN:operand)
	| LDR(rdLDR:operand,  baseLDR:operand, ofsLDR:operand)
	| STR(rdSTR:operand,  baseSTR:operand, ofsSTR:operand)
    | CPS(mod:operand) 

//-----------------------------------------------------------------------------
// Exception Handlers
//-----------------------------------------------------------------------------

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
predicate ValidState(s:state)
{
    (forall m:mode :: SP(m) in s.regs && LR(m) in s.regs) &&
        (forall i:int :: 0 <= i <= 12 ==> R(i) in s.regs)
}

predicate ValidOperand(s:state, o:operand)
{
	match o
		case OConst(n) => 0 <= n < MaxVal()
		case OReg(r) => (match r
			case R(n) => r in s.regs 
			case SP(m) => false // not used directly 
			case LR(m) => false // not used directly 
		)
		case OMem(x) => (match x
			case GlobalVar(g) => x in s.globals
			case LocalVar(l)  => |s.stack| > 0 && x in s.stack[0].locals
            case Address(a)   => x in s.addresses
	    )
        case OSP => SP(mode_of_state(s)) in s.regs
        case OLR => LR(mode_of_state(s)) in s.regs
}

predicate ValidShiftOperand(s:state, o:operand)
    { ( o.OConst? && 0 <= o.n <= 32) || ValidOperand(s, o) }

predicate ValidMode(m:int) {
    m == 0x10 || m == 0x11 || m == 0x13 || m == 0x16 || m == 0x17 || m == 0x17 
}

predicate ValidDestinationOperand(s:state, o:operand)
	{ !o.OConst? && ValidOperand(s, o) }

predicate IsMemOperand(o:operand)
    { o.OMem? }

predicate ValidAddress(s:state, base:operand, ofs:operand)
    requires ValidOperand(s, base);
    requires ValidOperand(s, ofs);
{
    ValidOperand(s, addr_op(s, base, ofs))
}

//-----------------------------------------------------------------------------
// Functions for bitwise operations
//-----------------------------------------------------------------------------
function xor32(x:int, y:int) : int  
    requires 0 <= x < 0x1_0000_0000 && 0 <= y < 0x1_0000_0000;
    { int(BitwiseXor(uint32(x), uint32(y))) }

function and32(x:int, y:int) : int  
    requires 0 <= x < 0x1_0000_0000 && 0 <= y < 0x1_0000_0000;
    { int(BitwiseAnd(uint32(x), uint32(y))) }

function or32(x:int, y:int) : int  
    requires 0 <= x < 0x1_0000_0000 && 0 <= y < 0x1_0000_0000;
    { int(BitwiseOr(uint32(x), uint32(y))) }

function not32(x:int) : int  
    requires 0 <= x < 0x1_0000_0000;
    { int(BitwiseNot(uint32(x))) }

function rol32(x:int, amount:int) : int 
    requires 0 <= x < 0x1_0000_0000 && 0 <= amount < 32;
    { int(RotateLeft(uint32(x), uint32(amount))) }

function ror32(x:int, amount:int) : int 
    requires 0 <= x < 0x1_0000_0000 && 0 <= amount < 32;
    { int(RotateRight(uint32(x), uint32(amount))) }

function shl32(x:int, amount:int) : int 
    requires 0 <= x < 0x1_0000_0000 && 0 <= amount < 32;
    { int(LeftShift(uint32(x), uint32(amount))) }

function shr32(x:int, amount:int) : int 
    requires 0 <= x < 0x1_0000_0000 && 0 <= amount < 32;
    { int(RightShift(uint32(x), uint32(amount))) }

//-----------------------------------------------------------------------------
// Evaluation
//-----------------------------------------------------------------------------
function OperandContents(s:state, o:operand): int
	requires ValidOperand(s,o)
{
	match o
		case OConst(n) => n
		case OReg(r) => s.regs[r]
		case OMem(x) => (match x
			case GlobalVar(g) => s.globals[x]
			case LocalVar(l) => s.stack[0].locals[x]
            case Address(a) => s.addresses[x]
		)
        case OSP => s.regs[SP(mode_of_state(s))]
        case OLR => s.regs[LR(mode_of_state(s))]
}


// eval_op and eval_memop may need to duplicate _Contents and remove requires
function eval_op(s:state, o:operand): int
	requires ValidOperand(s, o)
    { Truncate(OperandContents(s,o)) }


predicate evalUpdate(s:state, o:operand, v:int, r:state, ok:bool)
	requires ValidDestinationOperand(s, o);
{
    ok && match o
        case OReg(reg) => r == s.(regs := s.regs[o.r := v])
        case OLR => r == s.(regs := s.regs[LR(mode_of_state(s)) := v])
        case OSP => r == s.(regs := s.regs[SP(mode_of_state(s)) := v])
        case OMem(x) => ( match x
            case Address(a) => r == s.(addresses:= s.addresses[o.x := v])
			case GlobalVar(g) => r == s.(globals := s.globals[o.x := v])
			case LocalVar(l) => r == s.(stack :=
				[s.stack[0].(locals := s.stack[0].locals[o.x := v])] +
					s.stack[1..])
		)
}

predicate evalModeUpdate(s:state, newmode:int, r:state, ok:bool)
{
    // ok && r == s.(cpsr := s.cpsr.(m := newmode))
    ok && ValidMode(newmode) && r == s.(mod := mode_encoding(newmode))
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
    //TODO check mem vs non-mem
	match ins
		case ADD(dest, src1, src2) => ValidOperand(s, src1) &&
			ValidOperand(s, src2) && ValidDestinationOperand(s, dest)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
		case SUB(dest, src1, src2) => ValidOperand(s, src1) &&
			ValidOperand(s, src2) && ValidDestinationOperand(s, dest)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case AND(dest, src1, src2) => ValidOperand(s, src1) &&
			ValidOperand(s, src2) && ValidDestinationOperand(s, dest)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case ORR(dest, src1, src2) => ValidOperand(s, src1) &&
			ValidOperand(s, src2) && ValidDestinationOperand(s, dest)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case EOR(dest, src1, src2) => ValidOperand(s, src1) &&
			ValidOperand(s, src2) && ValidDestinationOperand(s, dest)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case ROR(dest, src1, src2) => ValidOperand(s, src1) &&
			ValidShiftOperand(s, src2) && ValidDestinationOperand(s, dest)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case LSL(dest, src1, src2) => ValidOperand(s, src1) &&
			ValidShiftOperand(s, src2) && ValidDestinationOperand(s, dest)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case LSR(dest, src1, src2) => ValidOperand(s, src1) &&
			ValidShiftOperand(s, src2) && ValidDestinationOperand(s, dest)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case MVN(dest, src) => ValidOperand(s, src) &&
			ValidDestinationOperand(s, dest)
            //!IsMemOperand(src) && !IsMemOperand(dest)
		case LDR(rd, base, ofs) => 
            ValidDestinationOperand(s, rd) &&
			ValidOperand(s, base) && ValidOperand(s, ofs) &&
            ValidOperand(s,  addr_op(s, base, ofs))
            //IsMemOperand(addr) && !IsMemOperand(rd)
		case STR(rd, base, ofs) =>
            ValidOperand(s, rd) &&
            ValidOperand(s, ofs) && ValidOperand(s, base) &&
            ValidDestinationOperand(s, addr_op(s, base, ofs))
            //IsMemOperand(addr) && !IsMemOperand(rd)
		case MOV(dst, src) => ValidDestinationOperand(s, dst) &&
			ValidOperand(s, src)
            //!IsMemOperand(src) && !IsMemOperand(dst)
        case CPS(mod) => ValidOperand(s, mod) &&
            ValidMode(OperandContents(s, mod))
}

predicate evalIns(ins:ins, s:state, r:state, ok:bool)
{
    if !ValidInstruction(s, ins) then !ok
    else match ins
		case ADD(dst, src1, src2) => evalUpdate(s, dst,
			((OperandContents(s, src1) + OperandContents(s, src2)) % MaxVal()),
			r, ok)
		case SUB(dst, src1, src2) => evalUpdate(s, dst,
			((OperandContents(s, src1) - OperandContents(s, src2)) % MaxVal()),
			r, ok)
		case AND(dst, src1, src2) => evalUpdate(s, dst,
            and32(eval_op(s, src1), eval_op(s, src2)),
			r, ok)
		case ORR(dst, src1, src2) => evalUpdate(s, dst,
            or32(eval_op(s, src1), eval_op(s, src2)),
			r, ok)
		case EOR(dst, src1, src2) => evalUpdate(s, dst,
            xor32(eval_op(s, src1), eval_op(s, src2)),
			r, ok)
		case ROR(dst, src1, src2) => if !(src2.OConst? && 0 <= src2.n <32) then !ok
            else evalUpdate(s, dst,
                ror32(eval_op(s, src1), eval_op(s, src2)),
			    r, ok)
		case LSL(dst, src1, src2) => if !(src2.OConst? && 0 <= src2.n <32) then !ok 
            else evalUpdate(s, dst,
                shl32(eval_op(s, src1), eval_op(s, src2)),
			    r, ok)
		case LSR(dst, src1, src2) => if !(src2.OConst? && 0 <= src2.n <32) then !ok
            else evalUpdate(s, dst,
                shr32(eval_op(s, src1), eval_op(s, src2)),
			    r, ok)
		case MVN(dst, src) => evalUpdate(s, dst,
            not32(eval_op(s, src)), r, ok)
		case LDR(rd, base, ofs) => 
            evalUpdate(s, rd, eval_op(s, addr_op(s, base, ofs)), r, ok)
		case STR(rd, base, ofs) => 
            evalUpdate(s, addr_op(s, base, ofs), eval_op(s, rd), r, ok)
		case MOV(dst, src) => evalUpdate(s, dst,
			OperandContents(s, src) % MaxVal(),
			r, ok)
        case CPS(mod) => evalModeUpdate(s,
            OperandContents(s, mod),
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
