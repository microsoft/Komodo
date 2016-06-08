include "assembly.s.dfy"

//-----------------------------------------------------------------------------
// Microarchitectural State
//-----------------------------------------------------------------------------
datatype ARMReg = R(n:int) | SP(spm:mode) | LR(lpm: mode)
// In FIQ, R8 to R12 are also banked

datatype id = GlobalVar(g:int) | LocalVar(l:int)
datatype operand = OConst(n:int) | OReg(r:ARMReg) | OId(x:id) | OSP | OLR

datatype frame = Frame(locals:map<id, int>)
datatype state = State(regs:map<ARMReg, int>,
					   globals:map<id, int>,
					   stack:seq<frame>,
					   heap:map<int, int>,
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
{
    //TODO get an actual encoding from spec
    if m == 0x10 then User
    else if m == 0x13 then Supervisor
    else if m == 0x16 then Monitor
    else if m == 0x17 then Abort
    else if m == 0x1B then Undefined
    else  FIQ //0x11
}

//-----------------------------------------------------------------------------
// Instructions
//-----------------------------------------------------------------------------
datatype ins =
	  ADD(dstADD:operand, src1ADD:operand, src2ADD:operand)
	| SUB(dstSUB:operand, src1SUB:operand, src2SUB:operand)
	| MOV(dstMOV:operand, srcMOV:operand)
	| LDR(rdLDR:operand,  addrLDR:operand)
	| STR(rdSTR:operand,  addrSTR:operand)
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
		case OId(x) => (match x
			case GlobalVar(g) => x in s.globals
			case LocalVar(l)  => |s.stack| > 0 && x in s.stack[0].locals
	    )
        case OSP => SP(mode_of_state(s)) in s.regs
        case OLR => LR(mode_of_state(s)) in s.regs
}

predicate ValidDestinationOperand(s:state, o:operand)
	{ !o.OConst? && ValidOperand(s, o) }

predicate IsMemOperand(o:operand)
    { o.OId? }

//-----------------------------------------------------------------------------
// Evaluation
//-----------------------------------------------------------------------------
function OperandContents(s:state, o:operand): int
	requires ValidOperand(s,o)
{
	match o
		case OConst(n) => n
		case OReg(r) => s.regs[r]
		case OId(x) => (match x
			case GlobalVar(g) => s.globals[x]
			case LocalVar(l) => s.stack[0].locals[x]
		)
        case OSP => s.regs[SP(mode_of_state(s))]
        case OLR => s.regs[LR(mode_of_state(s))]
}


// eval_op and eval_memop may need to duplicate _Contents and remove requires
function eval_op(s:state, o:operand): int
	requires ValidOperand(s, o) { Truncate(OperandContents(s,o)) }


predicate evalUpdate(s:state, o:operand, v:int, r:state, ok:bool)
	requires ValidDestinationOperand(s, o);
{
    ok && match o
        case OReg(reg) => r == s.(regs := s.regs[o.r := v])
        case OLR => r == s.(regs := s.regs[LR(mode_of_state(s)) := v])
        case OSP => r == s.(regs := s.regs[SP(mode_of_state(s)) := v])
        case OId(x) => ( match x
			case GlobalVar(g) => r == s.(globals := s.globals[o.x := v])
			case LocalVar(l) => r == s.(stack :=
				[s.stack[0].(locals := s.stack[0].locals[o.x := v])] +
					s.stack[1..])
		)
}

predicate evalModeUpdate(s:state, newmode:int, r:state, ok:bool)
{
    // ok && r == s.(cpsr := s.cpsr.(m := newmode))
    ok && r == s.(mod := mode_encoding(newmode))
}

// predicate evalCPSRUpdate(s:state, newcpsr:cpsr_val, newspsr_entry:cpsr_val,
//     spsr_changed:mode, r:state, ok:bool)
// {
//     ok && r == s.(cpsr := newcpsr).(spsr := s.spsr[spsr_changed := newspsr_entry])
// }

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
			ValidOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            !IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
		case SUB(dest, src1, src2) => ValidOperand(s, src1) &&
			ValidOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            !IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
		case LDR(rd, addr) => ValidDestinationOperand(s, rd) &&
			ValidOperand(s, addr) && IsMemOperand(addr) && !IsMemOperand(rd)
		case STR(rd, addr) => ValidOperand(s, rd) &&
			ValidDestinationOperand(s, addr) &&
            IsMemOperand(addr) && !IsMemOperand(rd)
		case MOV(dst, src) => ValidDestinationOperand(s, dst) &&
			ValidOperand(s, src) && !IsMemOperand(src) && !IsMemOperand(dst)
        case CPS(mod) => ValidOperand(s, mod)
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
		case LDR(rd, addr) => evalUpdate(s, rd,
			OperandContents(s, addr) % MaxVal(),
			r, ok)
		case STR(rd, addr) => evalUpdate(s, addr,
			OperandContents(s, rd) % MaxVal(),
			r, ok)
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
