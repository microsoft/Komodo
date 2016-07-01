include "assembly.s.dfy"
include "Maybe.dfy"

//-----------------------------------------------------------------------------
// Microarchitectural State
//-----------------------------------------------------------------------------
datatype ARMReg = R(n:int) | SP(spm:mode) | LR(lpm: mode)
// In FIQ, R8 to R12 are also banked

datatype mem = Address(addr:int)
datatype operand = OConst(n:int) | OReg(r:ARMReg) | OSP | OLR | OSymbol(sym:string)

datatype frame = Frame(locals:map<mem, int>)
datatype state = State(regs:map<ARMReg, int>,
                       addresses:map<mem, int>,
                       globals:map<string, seq<int>>,
                       // stack:seq<frame>,
                       // ns:bool,
                       // cpsr:cpsr_val,
                       // spsr:map<mode, cpsr_val>,
                       mod:mode)

// SCR.NS = non-secure bit

datatype cpsr_val = CPSR(
    // n:bool,             //Negative condition
    // z:bool,             //Zero condition
    // c:bool,             //Carry condition
    // v:bool,             //Overflow condition
    // a:bool,             //Abort mask
    // f:bool,             //FIQ mask
    m:mode)

// System mode is not modelled
datatype mode = User | FIQ | IRQ | Supervisor | Abort | Undefined | Monitor
datatype priv = PL0 | PL1 // PL2 is only used in Hyp, not modeled


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

// function method addr(base:int, ofs:int):mem
//     { Address(base + ofs) }

function method mode_of_state(s:state):mode
{
    // match s.cpsr
    //         case CPSR(m) => m
    s.mod
}

function method priv_of_mode(m:mode):priv
{
    if m == User then PL0 else PL1
}

function method priv_of_state(s:state):priv
    { priv_of_mode(mode_of_state(s)) }

function method decode_mode'(e:int):Maybe<mode>
{
    if e == 0x10 then Just(User)
    else if e == 0x11 then Just(FIQ)
    else if e == 0x12 then Just(IRQ)
    else if e == 0x13 then Just(Supervisor)
    else if e == 0x17 then Just(Abort)
    else if e == 0x1b then Just(Undefined)
    else if e == 0x16 then Just(Monitor)
    else Nothing
}

predicate ValidModeEncoding(e:int)
{
    decode_mode'(e).Just?
}

function method decode_mode(e:int):mode
    requires ValidModeEncoding(e)
{
    fromJust(decode_mode'(e))
}

function addr_mem(s:state, base:operand, ofs:operand):mem
    requires ValidOperand(s, base);
    requires ValidOperand(s, ofs);
{
    Address( OperandContents(s, base) + OperandContents(s, ofs) )
}

//-----------------------------------------------------------------------------
// Instructions
//-----------------------------------------------------------------------------
datatype ins =
      ADD(dstADD:operand, src1ADD:operand, src2ADD:operand)
    | SUB(dstSUB:operand, src1SUB:operand, src2SUB:operand)
    | MUL(dstMUL:operand, src1MUL:operand, src2MUL:operand)
    | UDIV(dstDIV:operand, src1DIV:operand, src2DIV:operand)
    | AND(dstAND:operand, src1AND:operand, src2AND:operand)
    | ORR(dstOR:operand,  src1OR:operand,  src2OR:operand)
    | EOR(dstEOR:operand, src1EOR:operand, src2EOR:operand) // Also known as XOR
    | ROR(dstROR:operand, src1ROR:operand, src2ROR:operand)
    | LSL(dstLSL:operand, src1LSL:operand, src2LSL:operand)
    | LSR(dstLSR:operand, src1LSR:operand, src2LSR:operand)
    | MOV(dstMOV:operand, srcMOV:operand)
    | MVN(dstMVN:operand, srcMVN:operand)
    | LDR(rdLDR:operand,  baseLDR:operand, ofsLDR:operand)
    | LDR_global(rdLDR_global:operand, global:operand,
                 baseLDR_global:operand, ofsLDR_global:operand)
    | LDR_reloc(rdLDR_reloc:operand, symLDR_reloc:operand)
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
function MaxVal() : int { 0x1_0000_0000 }
predicate isUInt32(i:int) { 0 <= i < MaxVal() }
//function Truncate(n:int) : int { n % MaxVal() }
function BytesPerWord() : int ensures BytesPerWord() == 4 { 4 }

//-----------------------------------------------------------------------------
// Validity
//-----------------------------------------------------------------------------
predicate ValidState(s:state)
{
    (forall m:mode {:trigger SP(m)} {:trigger LR(m)} ::
        SP(m) in s.regs && 0 <= s.regs[SP(m)] < MaxVal() &&
        LR(m) in s.regs && 0 <= s.regs[LR(m)] < MaxVal()) &&
     (forall i:int {:trigger R(i)} :: 0 <= i <= 12 ==> R(i) in s.regs && 
            0 <= s.regs[R(i)] < MaxVal())
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
        case OSP => SP(mode_of_state(s)) in s.regs
        case OLR => LR(mode_of_state(s)) in s.regs
        case OSymbol(s) => false
}

function method SymbolName(o:operand): string
    requires o.OSymbol?
{
    match o case OSymbol(name) => name
}

predicate ValidGlobal(s:state, o:operand)
{
    o.OSymbol?
        // defined name
        && SymbolName(o) in s.globals
        // each word is 32-bit
        && forall v :: v in s.globals[SymbolName(o)] ==> isUInt32(v)
}

function SizeOfGlobal(s:state, g:operand): int
    requires ValidGlobal(s, g)
    ensures WordAligned(SizeOfGlobal(s,g))
{
    |s.globals[SymbolName(g)]| * BytesPerWord()
}

predicate ValidGlobalOffset(s:state, g:operand, offset:int)
{
    ValidGlobal(s, g) && WordAligned(offset) && 0 <= offset < SizeOfGlobal(s, g)
}

predicate {:axiom} AddressOfGlobal(s:state, g:operand, a:int)

predicate Is32BitOperand(s:state, o:operand)
    requires ValidOperand(s, o);
{
    0 <= OperandContents(s, o) < MaxVal()
}

predicate ValidMem(s:state, m:mem)
{
    m in s.addresses
}

predicate WordAligned(addr:int) { addr % BytesPerWord() == 0}

predicate ValidShiftOperand(s:state, o:operand)
    { ( o.OConst? && 0 <= o.n <= 32) || ValidOperand(s, o) }

predicate ValidDestinationOperand(s:state, o:operand)
    { !o.OConst? && ValidOperand(s, o) }

// MUL only operates on regs
// Currently the same as ValidDestinationOperand, but in the future globals
// might be valid destinations but not registers. 
predicate ValidRegOperand(s:state, o:operand)
    { !o.OConst? && ValidOperand(s, o) }


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
        case OSP => s.regs[SP(mode_of_state(s))]
        case OLR => s.regs[LR(mode_of_state(s))]
}

function MemContents(s:state, m:mem): int
    requires ValidMem(s, m)
    requires WordAligned(m.addr)
{
    s.addresses[m]
}

function GlobalContents(s:state, g:operand, offset:int): int
    requires ValidGlobalOffset(s, g, offset)
    ensures isUInt32(GlobalContents(s, g, offset))
{
    (s.globals[SymbolName(g)])[offset / BytesPerWord()]
}

function eval_op(s:state, o:operand): int
    requires ValidOperand(s, o)
    { OperandContents(s,o) }

// function eval_mem(s:state, m:mem): int
//     requires ValidMem(s, m)
// { Truncate(MemContents(s, m)) }


predicate evalUpdate(s:state, o:operand, v:int, r:state, ok:bool)
    requires ValidDestinationOperand(s, o);
{
    ok && match o
        case OReg(reg) => r == s.(regs := s.regs[o.r := v])
        case OLR => r == s.(regs := s.regs[LR(mode_of_state(s)) := v])
        case OSP => r == s.(regs := s.regs[SP(mode_of_state(s)) := v])
}

predicate evalHavocReg(s:state, o:operand, r:state, ok:bool)
    requires ValidDestinationOperand(s, o);
{
    ok && ValidDestinationOperand(r, o) && match o
        case OReg(reg) => r == s.(regs := s.regs[o.r := r.regs[o.r]])
        case OLR => r == s.(regs := s.regs[LR(mode_of_state(s)) := r.regs[LR(mode_of_state(r))]])
        case OSP => r == s.(regs := s.regs[SP(mode_of_state(s)) := r.regs[SP(mode_of_state(r))]])
}

predicate evalMemUpdate(s:state, m:mem, v:int, r:state, ok:bool)
    requires ValidMem(s, m)
    requires WordAligned(m.addr)
    ensures  ValidMem(s, m)
{
    ok && r == s.(addresses := s.addresses[m := v])
}

predicate evalGlobalUpdate(s:state, g:operand, offset:nat, v:int, r:state, ok:bool)
    requires ValidGlobalOffset(s, g, offset)
{
    var n := SymbolName(g);
    var oldval := s.globals[n];
    var wordidx := offset / BytesPerWord();
    assert offset < SizeOfGlobal(s, g);
    assert |oldval| * BytesPerWord() == SizeOfGlobal(s, g);
    assert wordidx * BytesPerWord() < SizeOfGlobal(s, g);
    assert |oldval| == SizeOfGlobal(s, g) / BytesPerWord();
    assert wordidx < |oldval|;
    var newval := oldval[wordidx := v];
    ok && r == s.(globals := s.globals[n := newval])
}

predicate evalModeUpdate(s:state, newmode:int, r:state, ok:bool)
{
    // ok && r == s.(cpsr := s.cpsr.(m := newmode))
    ok && ValidModeEncoding(newmode) && r == s.(mod := decode_mode(newmode))
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
    evalCmp(o.cmp, OperandContents(s, o.o1), OperandContents(s, o.o2))
}

predicate ValidInstruction(s:state, ins:ins)
{
    match ins
        case ADD(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            (0 <= (eval_op(s,src1) + eval_op(s,src2)) < MaxVal())
        case SUB(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            (0 <= (eval_op(s,src1) - eval_op(s,src2)) < MaxVal())
        case MUL(dest,src1,src2) => ValidRegOperand(s, src1) &&
            ValidRegOperand(s, src2) && ValidDestinationOperand(s,dest) &&
            (0 <= (eval_op(s,src1) * eval_op(s,src2)) < MaxVal())
        case UDIV(dest,src1,src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s,dest) &&
            (eval_op(s,src2) > 0) &&
            (0 <= (eval_op(s,src1) / eval_op(s,src2)) < MaxVal())
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case AND(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            Is32BitOperand(s, src1) && Is32BitOperand(s, src2)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case ORR(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            Is32BitOperand(s, src1) && Is32BitOperand(s, src2)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case EOR(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            Is32BitOperand(s, src1) && Is32BitOperand(s, src2)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case ROR(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidShiftOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            Is32BitOperand(s, src1) && Is32BitOperand(s, src2)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case LSL(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidShiftOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            Is32BitOperand(s, src1) && Is32BitOperand(s, src2)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case LSR(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidShiftOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            Is32BitOperand(s, src1) && Is32BitOperand(s, src2)
            //!IsMemOperand(src1) && !IsMemOperand(src2) && !IsMemOperand(dest)
        case MVN(dest, src) => ValidOperand(s, src) &&
            ValidDestinationOperand(s, dest) &&
            Is32BitOperand(s, src)
            //!IsMemOperand(src) && !IsMemOperand(dest)
        case LDR(rd, base, ofs) => 
            ValidDestinationOperand(s, rd) &&
            ValidOperand(s, base) && ValidOperand(s, ofs) &&
            WordAligned(OperandContents(s, base) + OperandContents(s, ofs)) &&
            ValidMem(s, Address(OperandContents(s, base) + OperandContents(s, ofs)))
            //IsMemOperand(addr) && !IsMemOperand(rd)
        case LDR_global(rd, global, base, ofs) => 
            ValidDestinationOperand(s, rd) &&
            ValidOperand(s, base) && ValidOperand(s, ofs) &&
            AddressOfGlobal(s, global, OperandContents(s, base)) &&
            ValidGlobalOffset(s, global, OperandContents(s, ofs))
        case LDR_reloc(rd, global) => 
            ValidDestinationOperand(s, rd) && ValidGlobal(s, global)
        case STR(rd, base, ofs) =>
            ValidRegOperand(s, rd) &&
            ValidOperand(s, ofs) && ValidOperand(s, base) &&
            WordAligned(OperandContents(s, base) + OperandContents(s, ofs)) &&
            ValidMem(s, Address(OperandContents(s, base) + OperandContents(s, ofs)))
            //ValidDestinationOperand(s, addr_op(s, base, ofs))
            //IsMemOperand(addr) && !IsMemOperand(rd)
        case MOV(dst, src) => ValidDestinationOperand(s, dst) &&
            ValidOperand(s, src) && Is32BitOperand(s, src)
            //!IsMemOperand(src) && !IsMemOperand(dst)
        case CPS(mod) => ValidOperand(s, mod) &&
            ValidModeEncoding(OperandContents(s, mod))
}

predicate evalIns(ins:ins, s:state, r:state, ok:bool)
{
    if !ValidInstruction(s, ins) then !ok
    else match ins
        case ADD(dst, src1, src2) => evalUpdate(s, dst,
            ((OperandContents(s, src1) + OperandContents(s, src2))),
            r, ok)
        case SUB(dst, src1, src2) => evalUpdate(s, dst,
            ((OperandContents(s, src1) - OperandContents(s, src2))),
            r, ok)
        case MUL(dst, src1, src2) => evalUpdate(s, dst,
            ((OperandContents(s, src1) * OperandContents(s, src2))),
            r, ok)
        case UDIV(dst, src1, src2) => evalUpdate(s, dst,
            ((OperandContents(s, src1) / OperandContents(s, src2))),
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
            evalUpdate(s, rd, MemContents(s, Address(OperandContents(s, base) +
                OperandContents(s, ofs))), r, ok)
        case LDR_global(rd, global, base, ofs) => 
            evalUpdate(s, rd, GlobalContents(s, global, OperandContents(s, ofs)), r, ok)
        case LDR_reloc(rd, name) =>
            evalHavocReg(s, rd, r, ok)
            && AddressOfGlobal(s, name, OperandContents(s, rd))
        case STR(rd, base, ofs) => 
            evalMemUpdate(s, Address(OperandContents(s, base) +
                OperandContents(s, ofs)), OperandContents(s, rd), r, ok)
        case MOV(dst, src) => evalUpdate(s, dst,
            OperandContents(s, src),
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

predicate{:opaque} sp_eval(c:code, s:state, r:state, ok:bool)
{
    evalCode(c, s, r, ok)
}
