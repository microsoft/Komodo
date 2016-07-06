include "assembly.s.dfy"
include "Maybe.dfy"
include "Seq.dfy"

//-----------------------------------------------------------------------------
// Microarchitectural State
//-----------------------------------------------------------------------------
datatype ARMReg = R(n:int) | SP(spm:mode) | LR(lpm: mode)
// In FIQ, R8 to R12 are also banked

datatype mem = Address(addr:int)
datatype operand = OConst(n:int) | OReg(r:ARMReg) | OSP | OLR | OSymbol(sym:string)

//datatype frame = Frame(locals:map<mem, int>)
datatype globals = Globals(map<operand, seq<int>>)
datatype state = State(regs:map<ARMReg, int>,
                       addresses:map<mem, int>,
                       globals:globals,
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

function method op_sym(sym:string):operand
    { OSymbol(sym) }

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
    | LDR_global(rdLDR_global:operand, globalLDR:operand,
                 baseLDR_global:operand, ofsLDR_global:operand)
    | LDR_reloc(rdLDR_reloc:operand, symLDR_reloc:operand)
    | STR(rdSTR:operand,  baseSTR:operand, ofsSTR:operand)
    | STR_global(rdSTRR_global:operand, globalSTR:operand,
                 baseSTR_global:operand, ofsSTR_global:operand)
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
predicate isUInt32(i:int) { 0 <= i < 0x1_0000_0000 }
function BytesPerWord() : int { 4 }
predicate WordAligned(addr:int) { addr % 4 == 0}
function WordsToBytes(w:int) : int { 4 * w }
function BytesToWords(b:int) : int requires WordAligned(b) { b / 4 }

//-----------------------------------------------------------------------------
// Validity
//-----------------------------------------------------------------------------
predicate ValidState(s:state)
{
    (forall m:mode {:trigger SP(m)} {:trigger LR(m)} ::
        SP(m) in s.regs && isUInt32(s.regs[SP(m)]) &&
        LR(m) in s.regs && isUInt32(s.regs[LR(m)]))
        && (forall i:int {:trigger R(i)} :: 0 <= i <= 12
            ==> R(i) in s.regs && isUInt32(s.regs[R(i)]))
        && ValidGlobalState(s)
}

predicate ValidGlobalState(s:state)
{
    match TheGlobalDecls() case GlobalDecls(decls) =>
    match s.globals case Globals(gmap) =>
        // same names as decls
        forall g :: g in decls ==> g in gmap
        // correct size, all uint32 values
        && forall g :: g in gmap ==> (g in decls
            && WordsToBytes(|gmap[g]|) == decls[g]
            && forall v :: v in gmap[g] ==> isUInt32(v))
}

predicate ValidOperand(s:state, o:operand)
{
    match o
        case OConst(n) => isUInt32(n)
        case OReg(r) => (match r
            case R(n) => 0 <= n <= 12 && r in s.regs
            case SP(m) => false // not used directly 
            case LR(m) => false // not used directly 
        )
        case OSP => SP(mode_of_state(s)) in s.regs
        case OLR => LR(mode_of_state(s)) in s.regs
        case OSymbol(s) => false
}

predicate ValidMem(s:state, m:mem)
{
    WordAligned(m.addr) && m in s.addresses && isUInt32(MemContents(s, m))
}

predicate ValidMemRange(s:state, base:int, limit:int)
{
    forall i:int :: base <= i < limit && WordAligned(i) ==>
        ValidMem(s, Address(i))
}

predicate ValidShiftOperand(s:state, o:operand)
    { ValidOperand(s, o) && OperandContents(s, o) < 32 }

predicate ValidDestinationOperand(s:state, o:operand)
    { !o.OConst? && ValidOperand(s, o) }

// MUL only operates on regs
// Currently the same as ValidDestinationOperand, but in the future globals
// might be valid destinations but not registers. 
predicate ValidRegOperand(s:state, o:operand)
    { !o.OConst? && ValidOperand(s, o) }

//-----------------------------------------------------------------------------
// Globals
//-----------------------------------------------------------------------------

datatype globaldecls = GlobalDecls(map<operand, int>)

function method SymbolName(o:operand): string
    requires o.OSymbol?
{
    match o case OSymbol(name) => name
}

predicate ValidGlobal(o:operand)
{
    match TheGlobalDecls() case GlobalDecls(declmap) =>
        o.OSymbol? && o in declmap
}

predicate ValidGlobalDecls(gd:globaldecls)
{
    gd.GlobalDecls? && match gd case GlobalDecls(decls) =>
        forall d :: d in decls ==> d.OSymbol? && decls[d] > 0 && WordAligned(decls[d])
}

predicate ValidGlobalOffset(g:operand, offset:int)
{
    ValidGlobal(g) && WordAligned(offset) && 0 <= offset < SizeOfGlobal(g)
}

// globals have an unknown (uint32) address, only establised by LDR-reloc
function {:axiom} AddressOfGlobal(g:operand): int
    ensures isUInt32(AddressOfGlobal(g));

/*
function InitialGlobals(): globals
    requires ValidGlobalDecls(TheGlobalDecls())
    ensures ValidGlobalState(InitialGlobals())
{
    match TheGlobalDecls() case GlobalDecls(decls) =>
        Globals(map sym | sym in decls :: SeqRepeat<int>(decls[sym], 0))
}
*/

function SizeOfGlobal(g:operand): int
    requires ValidGlobal(g)
    ensures WordAligned(SizeOfGlobal(g))
{
    match TheGlobalDecls() case GlobalDecls(declmap) => declmap[g]
}

// global declarations are the responsibility of the program, as long as they're valid
function {:axiom} TheGlobalDecls(): globaldecls
    ensures ValidGlobalDecls(TheGlobalDecls());

//-----------------------------------------------------------------------------
// Functions for bitwise operations
//-----------------------------------------------------------------------------
function xor32(x:int, y:int) : int  
    requires isUInt32(x) && isUInt32(y);
    { int(BitwiseXor(uint32(x), uint32(y))) }

function and32(x:int, y:int) : int  
    requires isUInt32(x) && isUInt32(y);
    { int(BitwiseAnd(uint32(x), uint32(y))) }

function or32(x:int, y:int) : int  
    requires isUInt32(x) && isUInt32(y);
    { int(BitwiseOr(uint32(x), uint32(y))) }

function not32(x:int) : int  
    requires isUInt32(x);
    { int(BitwiseNot(uint32(x))) }

function rol32(x:int, amount:int) : int 
    requires isUInt32(x) && 0 <= amount < 32;
    { int(RotateLeft(uint32(x), uint32(amount))) }

function ror32(x:int, amount:int) : int 
    requires isUInt32(x) && 0 <= amount < 32;
    { int(RotateRight(uint32(x), uint32(amount))) }

function shl32(x:int, amount:int) : int 
    requires isUInt32(x) && 0 <= amount < 32;
    { int(LeftShift(uint32(x), uint32(amount))) }

function shr32(x:int, amount:int) : int 
    requires isUInt32(x) && 0 <= amount < 32;
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
    requires m in s.addresses
    requires WordAligned(m.addr)
{
    s.addresses[m]
}

function GlobalContents(s:state, g:operand, offset:int): int
    requires ValidGlobalOffset(g, offset)
    requires ValidGlobalState(s)
    ensures isUInt32(GlobalContents(s, g, offset))
{
    match s.globals case Globals(gmap) =>
        (gmap[g])[BytesToWords(offset)]
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

// predicate evalHavocReg(s:state, o:operand, r:state, ok:bool)
//     requires ValidDestinationOperand(s, o);
// {
//     ok && ValidDestinationOperand(r, o) && match o
//         case OReg(reg) => r == s.(regs := s.regs[o.r := r.regs[o.r]])
//         case OLR => r == s.(regs := s.regs[LR(mode_of_state(s)) := r.regs[LR(mode_of_state(r))]])
//         case OSP => r == s.(regs := s.regs[SP(mode_of_state(s)) := r.regs[SP(mode_of_state(r))]])
// }

predicate evalMemUpdate(s:state, m:mem, v:int, r:state, ok:bool)
    requires WordAligned(m.addr)
    requires ValidMem(s, m)
    requires isUInt32(v)
    ensures  ValidMem(s, m)
{
    ok && r == s.(addresses := s.addresses[m := v])
}

predicate evalGlobalUpdate(s:state, g:operand, offset:nat, v:int, r:state, ok:bool)
    requires ValidGlobalOffset(g, offset)
    requires ValidGlobalState(s)
    requires isUInt32(v)
    ensures ValidGlobalState(s)
{
    match s.globals case Globals(gmap) =>
        var oldval := gmap[g];
        var newval := oldval[BytesToWords(offset) := v];
        assert |newval| == |oldval|;
        ok && r == s.(globals := Globals(gmap[g := newval]))
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
    ValidState(s) && match ins
        case ADD(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            isUInt32(eval_op(s,src1) + eval_op(s,src2))
        case SUB(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s, dest) &&
            isUInt32(eval_op(s,src1) - eval_op(s,src2))
        case MUL(dest,src1,src2) => ValidRegOperand(s, src1) &&
            ValidRegOperand(s, src2) && ValidDestinationOperand(s,dest) &&
            isUInt32(eval_op(s,src1) * eval_op(s,src2))
        case UDIV(dest,src1,src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s,dest) &&
            (eval_op(s,src2) > 0) && isUInt32(eval_op(s,src1) / eval_op(s,src2))
        case AND(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s, dest)
        case ORR(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s, dest)
        case EOR(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidOperand(s, src2) && ValidDestinationOperand(s, dest)
        case ROR(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidShiftOperand(s, src2) && ValidDestinationOperand(s, dest)
        case LSL(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidShiftOperand(s, src2) && ValidDestinationOperand(s, dest)
        case LSR(dest, src1, src2) => ValidOperand(s, src1) &&
            ValidShiftOperand(s, src2) && ValidDestinationOperand(s, dest)
        case MVN(dest, src) => ValidOperand(s, src) &&
            ValidDestinationOperand(s, dest)
        case LDR(rd, base, ofs) => 
            ValidDestinationOperand(s, rd) &&
            ValidOperand(s, base) && ValidOperand(s, ofs) &&
            WordAligned(OperandContents(s, base) + OperandContents(s, ofs)) &&
            ValidMem(s, Address(OperandContents(s, base) + OperandContents(s, ofs)))
        case LDR_global(rd, global, base, ofs) => 
            ValidDestinationOperand(s, rd) && ValidGlobalState(s) &&
            ValidOperand(s, base) && ValidOperand(s, ofs) &&
            AddressOfGlobal(global) == OperandContents(s, base) &&
            ValidGlobalOffset(global, OperandContents(s, ofs))
        case LDR_reloc(rd, global) => 
            ValidDestinationOperand(s, rd) && ValidGlobal(global)
        case STR(rd, base, ofs) =>
            ValidRegOperand(s, rd) && isUInt32(OperandContents(s, rd)) &&
            ValidOperand(s, ofs) && ValidOperand(s, base) &&
            WordAligned(OperandContents(s, base) + OperandContents(s, ofs)) &&
            ValidMem(s, Address(OperandContents(s, base) + OperandContents(s, ofs)))
        case STR_global(rd, global, base, ofs) => 
            ValidRegOperand(s, rd) && isUInt32(OperandContents(s, rd)) &&
            ValidOperand(s, base) && ValidOperand(s, ofs) &&
            AddressOfGlobal(global) == OperandContents(s, base) &&
            ValidGlobalOffset(global, OperandContents(s, ofs))
        case MOV(dst, src) => ValidDestinationOperand(s, dst) &&
            ValidOperand(s, src)
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
            evalUpdate(s, rd, AddressOfGlobal(name), r, ok)
        case STR(rd, base, ofs) => 
            evalMemUpdate(s, Address(OperandContents(s, base) +
                OperandContents(s, ofs)), OperandContents(s, rd), r, ok)
        case STR_global(rd, global, base, ofs) => 
            evalGlobalUpdate(s, global, OperandContents(s, ofs), OperandContents(s, rd), r, ok)
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
