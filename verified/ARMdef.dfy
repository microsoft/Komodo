include "assembly.s.dfy"
include "Maybe.dfy"
include "Seq.dfy"

//-----------------------------------------------------------------------------
// Microarchitectural State
//-----------------------------------------------------------------------------
// NB: In FIQ mode, R8 to R12 are also banked, but we don't model this
datatype ARMReg = R0|R1|R2|R3|R4|R5|R6|R7|R8|R9|R10|R11|R12 | SP(spm:mode) | LR(lrm:mode)

// Special register instruction operands
datatype SReg = ttbr0 | cpsr | spsr | scr // Not a valid operand ever. // MRC/MCR are used instead. 
    // | ttbcr // Used in C implementation of monitor, but not strictly necessary

// A model of the relevant configuration register state
// References refer to armv7a spec
datatype config = Config(m:mode, ns:world, spsr:map<mode,mode>, l1p:int)
// m:    stored in the 5 LSBs of the CPSR. See B1.3.3
// ns:   current world. Stored in lsb of SCR. See B4.1.129
// spsr: saved cpsr for when current mode returns from handling an exception
    // should be mapping from mode -> cpsr. See B1.3.3
// l1pt: Base of addr of translation table 0. Stored in TTBR0. See B4.1.154

type mem = int
datatype operand = OConst(n:int) 
    | OReg(r:ARMReg) 
    | OSymbol(sym:string)
    | OSReg(sr:SReg)
    | OSP | OLR 

datatype memstate = MemState(addresses:map<mem, int>,
                             globals:map<operand, seq<int>>)

datatype state = State(regs:map<ARMReg, int>,
                       m:memstate,
                       conf:config)

// System mode is not modelled
datatype mode = User | FIQ | IRQ | Supervisor | Abort | Undefined | Monitor
datatype priv = PL0 | PL1 // PL2 is only used in Hyp, not modeled
datatype world = Secure | NotSecure

//-----------------------------------------------------------------------------
// State-related Utilities
//-----------------------------------------------------------------------------
function method op_r(r:ARMReg):operand
    { OReg(r) }

function method op_sp():operand
    { OSP }

function method op_lr():operand
    { OLR }

function method op_sym(sym:string):operand
    { OSymbol(sym) }

// See B1.5.1
function world_of_state(s:state):world
{
    if mode_of_state(s) == Monitor then Secure 
    else s.conf.ns 
}

function mode_of_state(s:state):mode
{
    s.conf.m
}

function priv_of_mode(m:mode):priv
{
    if m == User then PL0 else PL1
}

function priv_of_state(s:state):priv
    { priv_of_mode(mode_of_state(s)) }

function encode_sreg(s:state, sr:SReg):int
    requires ValidConfig(s.conf)
    requires ValidSpecialOperand(s, OSReg(sr))
    ensures  isUInt32(encode_sreg(s,sr))
{
    reveal_ValidConfig();
    match sr
        case ttbr0 => s.conf.l1p
        case cpsr  => encode_mode(s.conf.m)
        case spsr  => encode_mode(s.conf.spsr[s.conf.m])
        case scr   => encode_ns(s.conf.ns)
}

function decode_sreg(s:state, sr:SReg, v:int) : config
    requires ValidConfig(s.conf)
    requires ValidSpecialOperand(s, OSReg(sr))
    requires isUInt32(v)
    requires (sr.cpsr? || sr.spsr?) ==> ValidModeEncoding(and32(v, 0x1f))
    ensures ValidConfig(decode_sreg(s, sr, v))
{
    reveal_ValidConfig();
    match sr
        case ttbr0 => s.conf.(l1p := v)
        case cpsr  => s.conf.(m := decode_mode(and32(v,0x1f)))
        case spsr  => 
            var m := s.conf.m;
            var spsr' := s.conf.spsr[ m := decode_mode(and32(v,0x1f))];
            s.conf.(spsr := spsr') 
        case scr =>
            var ns' := if(and32(v,1) == 1) then NotSecure else Secure;
            s.conf.(ns := ns')
}

function method encode_ns(ns:world):int
    { if ns == NotSecure then 1 else 0 }

function method encode_mode(m:mode):int
{
    match m
        case User => 0x10
        case FIQ => 0x11
        case IRQ => 0x12
        case Supervisor => 0x13
        case Abort => 0x17
        case Undefined => 0x1b
        case Monitor => 0x16
}

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

// sanity-check the above
lemma mode_encodings_are_sane()
    ensures forall m :: decode_mode'(encode_mode(m)) == Just(m)
{}

predicate ValidModeEncoding(e:int)
{
    decode_mode'(e).Just?
}

function method decode_mode(e:int):mode
    requires ValidModeEncoding(e)
{
    fromJust(decode_mode'(e))
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
    // | CPS(mod:operand) // TODO deprecate
    | MRS(dstMRS:operand, srcMRS: operand)
    | MSR(dstMSR:operand, srcMSR: operand)
    // Only accesses to SCR are supported
    // (See armv7a ref manual B4.1.129 "Accessing the SCR")
    | MRC(dstMRC:operand,srcMRC:operand)
    | MCR(dstMCR:operand,srcMCR:operand)
    // Only the special case where rd is pc
    // (See armv7a ref manual A8.8.105 and B9.3.20)
    | MOVS

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
    ValidRegState(s.regs) && ValidMemState(s.m) && ValidConfig(s.conf)
}

predicate {:opaque} ValidRegState(regs:map<ARMReg, int>)
{
    (forall m:mode {:trigger SP(m)} {:trigger LR(m)} ::
        SP(m) in regs && isUInt32(regs[SP(m)]) &&
        LR(m) in regs && isUInt32(regs[LR(m)]))
    && R0 in regs && isUInt32(regs[R0])
    && R1 in regs && isUInt32(regs[R1])
    && R2 in regs && isUInt32(regs[R2])
    && R3 in regs && isUInt32(regs[R3])
    && R4 in regs && isUInt32(regs[R4])
    && R5 in regs && isUInt32(regs[R5])
    && R6 in regs && isUInt32(regs[R6])
    && R7 in regs && isUInt32(regs[R7])
    && R8 in regs && isUInt32(regs[R8])
    && R9 in regs && isUInt32(regs[R9])
    && R10 in regs && isUInt32(regs[R10])
    && R11 in regs && isUInt32(regs[R11])
    && R12 in regs && isUInt32(regs[R12])
}

predicate {:opaque} ValidConfig(c:config)
{
    isUInt32(c.l1p) &&
    User !in c.spsr &&
    (forall m:mode :: m != User ==> m in c.spsr )
}

predicate {:opaque} ValidMemState(s:memstate)
{
    // regular mem
    (forall m:mem :: m in s.addresses
        ==> WordAligned(m) && isUInt32(m) && isUInt32(s.addresses[m]))
    // globals
    && (match TheGlobalDecls() case GlobalDecls(decls) =>
        // same names as decls
        forall g :: g in decls ==> g in s.globals
        // correct size, all uint32 values
        && forall g :: g in s.globals ==> (g in decls
            && WordsToBytes(|s.globals[g]|) == decls[g]
            && forall v :: v in s.globals[g] ==> isUInt32(v)))
}

predicate ValidOperand(o:operand)
{
    match o
        case OConst(n) => isUInt32(n)
        case OReg(r) => !(r.SP? || r.LR?) // not used directly
        case OSP => true
        case OLR => true
        case OSymbol(s) => false
        case OSReg(sr) => false
}

predicate ValidSpecialOperand(s:state, o:operand)
{
    o.OSReg? && ValidConfig(s.conf) && mode_of_state(s) != User && (
        (o.sr.scr? && world_of_state(s) == Secure) 
    ||  (!o.sr.scr?))
}

predicate ValidMcrMrcOperand(s:state,o:operand)
{
    ValidSpecialOperand(s,o) && o.sr.scr?
}

predicate ValidMem(s:memstate, m:mem)
{
    isUInt32(m) && WordAligned(m) && m in s.addresses
}

predicate ValidMemRange(s:memstate, base:int, limit:int)
{
    forall i:int :: base <= i < limit && WordAligned(i) ==>
        ValidMem(s, i)
}

predicate ValidShiftOperand(s:state, o:operand)
    requires ValidState(s)
    { ValidOperand(o) && OperandContents(s, o) < 32 }

predicate ValidDestinationOperand(o:operand)
    { !o.OConst? && ValidOperand(o) }

// MUL only operates on regs
// Currently the same as ValidDestinationOperand, but in the future globals
// might be valid destinations but not registers. 
predicate ValidRegOperand(o:operand)
    { !o.OConst? && ValidOperand(o) }

//-----------------------------------------------------------------------------
// Globals
//-----------------------------------------------------------------------------
datatype globaldecls = GlobalDecls(map<operand, int>)

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
    requires ValidOperand(o) || ValidSpecialOperand(s, o)
    requires ValidState(s)
    ensures  isUInt32(OperandContents(s,o))
{
    reveal_ValidRegState();
    match o
        case OConst(n) => n
        case OReg(r) => s.regs[r]
        case OSP => s.regs[SP(mode_of_state(s))]
        case OLR => s.regs[LR(mode_of_state(s))]
        case OSReg(sr) => encode_sreg(s, sr)
}

function MemContents(s:memstate, m:mem): int
    requires ValidMemState(s)
    requires ValidMem(s,m)
    ensures isUInt32(MemContents(s,m))
{
    reveal_ValidMemState();
    assert m in s.addresses;
    assert isUInt32(s.addresses[m]);
    s.addresses[m]
}

function GlobalFullContents(s:memstate, g:operand): seq<int>
    requires ValidMemState(s)
    requires ValidGlobal(g)
    ensures forall w :: w in GlobalFullContents(s, g) ==> isUInt32(w)
    ensures WordsToBytes(|GlobalFullContents(s, g)|) == SizeOfGlobal(g)
{
    reveal_ValidMemState();
    s.globals[g]
}

function GlobalWord(s:memstate, g:operand, offset:int): int
    requires ValidGlobalOffset(g, offset)
    requires ValidMemState(s)
    ensures isUInt32(GlobalWord(s, g, offset))
{
    reveal_ValidMemState();
    GlobalFullContents(s, g)[BytesToWords(offset)]
}

function eval_op(s:state, o:operand): int
    requires ValidState(s)
    requires ValidOperand(o) || ValidSpecialOperand(s,o)
    ensures isUInt32(eval_op(s,o))
    { OperandContents(s,o) }


predicate evalUpdate(s:state, o:operand, v:int, r:state, ok:bool)
    requires ValidState(s)
    requires ValidDestinationOperand(o)
    requires isUInt32(v)
    ensures evalUpdate(s, o, v, r, ok) ==> ValidState(r)
{
    reveal_ValidRegState();
    ok && match o
        case OReg(reg) => r == s.(regs := s.regs[o.r := v])
        case OLR => r == s.(regs := s.regs[LR(mode_of_state(s)) := v])
        case OSP => r == s.(regs := s.regs[SP(mode_of_state(s)) := v])
}


predicate evalSRegUpdate(s:state, o:operand, v:int, r:state, ok:bool)
    requires ValidState(s)
    requires ValidSpecialOperand(s, o)
    requires isUInt32(v)
    requires o.sr.cpsr? || o.sr.spsr? ==> ValidModeEncoding(and32(v,0x1f))
    ensures  evalSRegUpdate(s, o, v, r, ok) ==> ValidState(r)
{
    ok && r == s.( conf := decode_sreg(s, o.sr, v) )
}

predicate evalMemUpdate(s:state, m:mem, v:int, r:state, ok:bool)
    requires ValidState(s)
    requires ValidMem(s.m, m)
    requires isUInt32(v)
    ensures evalMemUpdate(s, m, v, r, ok) ==> ValidState(r)
{
    reveal_ValidMemState();
    ok && r == s.(m := s.m.(addresses := s.m.addresses[m := v]))
}

predicate evalGlobalUpdate(s:state, g:operand, offset:nat, v:int, r:state, ok:bool)
    requires ValidState(s)
    requires ValidGlobalOffset(g, offset)
    requires isUInt32(v)
    ensures evalGlobalUpdate(s, g, offset, v, r, ok) ==> ValidState(r) && GlobalWord(r.m, g, offset) == v
{
    reveal_ValidMemState();
    var oldval := s.m.globals[g];
    var newval := oldval[BytesToWords(offset) := v];
    assert |newval| == |oldval|;
    ok && r == s.(m := s.m.(globals := s.m.globals[g := newval]))
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
    requires ValidState(s)
    requires ValidOperand(o.o1)
    requires ValidOperand(o.o2)
{
    evalCmp(o.cmp, OperandContents(s, o.o1), OperandContents(s, o.o2))
}

predicate ValidModeChange(m:mode, v:int)
{
    // See B9.1.2
    isUInt32(v) &&
    ValidModeEncoding(and32(v,0x1f)) &&
    (var m' := decode_mode(and32(v,0x1f));
    m != User && !(m != Monitor && m' == Monitor))
}

predicate ValidInstruction(s:state, ins:ins)
{
    ValidState(s) && match ins
        case ADD(dest, src1, src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidDestinationOperand(dest) &&
            isUInt32(eval_op(s,src1) + eval_op(s,src2))
        case SUB(dest, src1, src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidDestinationOperand(dest) &&
            isUInt32(eval_op(s,src1) - eval_op(s,src2))
        case MUL(dest,src1,src2) => ValidRegOperand(src1) &&
            ValidRegOperand(src2) && ValidDestinationOperand(dest) &&
            isUInt32(eval_op(s,src1) * eval_op(s,src2))
        case UDIV(dest,src1,src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidDestinationOperand(dest) &&
            (eval_op(s,src2) > 0) && isUInt32(eval_op(s,src1) / eval_op(s,src2))
        case AND(dest, src1, src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidDestinationOperand(dest)
        case ORR(dest, src1, src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidDestinationOperand(dest)
        case EOR(dest, src1, src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidDestinationOperand(dest)
        case ROR(dest, src1, src2) => ValidOperand(src1) &&
            ValidShiftOperand(s, src2) && ValidDestinationOperand(dest)
        case LSL(dest, src1, src2) => ValidOperand(src1) &&
            ValidShiftOperand(s, src2) && ValidDestinationOperand(dest)
        case LSR(dest, src1, src2) => ValidOperand(src1) &&
            ValidShiftOperand(s, src2) && ValidDestinationOperand(dest)
        case MVN(dest, src) => ValidOperand(src) &&
            ValidDestinationOperand(dest)
        case LDR(rd, base, ofs) => 
            ValidDestinationOperand(rd) &&
            ValidOperand(base) && ValidOperand(ofs) &&
            WordAligned(OperandContents(s, base) + OperandContents(s, ofs)) &&
            ValidMem(s.m, OperandContents(s, base) + OperandContents(s, ofs))
        case LDR_global(rd, global, base, ofs) => 
            ValidDestinationOperand(rd) &&
            ValidOperand(base) && ValidOperand(ofs) &&
            AddressOfGlobal(global) == OperandContents(s, base) &&
            ValidGlobalOffset(global, OperandContents(s, ofs))
        case LDR_reloc(rd, global) => 
            ValidDestinationOperand(rd) && ValidGlobal(global)
        case STR(rd, base, ofs) =>
            ValidRegOperand(rd) &&
            ValidOperand(ofs) && ValidOperand(base) &&
            WordAligned(OperandContents(s, base) + OperandContents(s, ofs)) &&
            ValidMem(s.m, OperandContents(s, base) + OperandContents(s, ofs))
        case STR_global(rd, global, base, ofs) => 
            ValidRegOperand(rd) &&
            ValidOperand(base) && ValidOperand(ofs) &&
            AddressOfGlobal(global) == OperandContents(s, base) &&
            ValidGlobalOffset(global, OperandContents(s, ofs))
        case MOV(dst, src) => ValidDestinationOperand(dst) &&
            ValidOperand(src)
        case MRS(dst, src) =>
            ValidSpecialOperand(s, src) &&
            !ValidMcrMrcOperand(s, src) &&
            ValidRegOperand(dst) 
        case MSR(dst, src) =>
            ValidRegOperand(src) && 
            ValidSpecialOperand(s, dst) && 
            !ValidMcrMrcOperand(s, dst) &&
            (dst.sr.cpsr? || dst.sr.spsr? ==>
                ValidModeChange(s.conf.m, OperandContents(s, src)))
        case MRC(dst, src) =>
            ValidMcrMrcOperand(s, src) &&
            ValidRegOperand(dst) 
        case MCR(dst, src) =>
            ValidMcrMrcOperand(s, dst) &&
            ValidRegOperand(src)
        case MOVS => 
            ValidSpecialOperand(s, OSReg(spsr)) &&
            ValidModeChange(s.conf.m, OperandContents(s, OSReg(spsr))) &&
            !(mode_of_state(s) == User)
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
            evalUpdate(s, rd, MemContents(s.m, OperandContents(s, base) +
                OperandContents(s, ofs)), r, ok)
        case LDR_global(rd, global, base, ofs) => 
            evalUpdate(s, rd, GlobalWord(s.m, global, OperandContents(s, ofs)), r, ok)
        case LDR_reloc(rd, name) =>
            evalUpdate(s, rd, AddressOfGlobal(name), r, ok)
        case STR(rd, base, ofs) => 
            evalMemUpdate(s, OperandContents(s, base) +
                OperandContents(s, ofs), OperandContents(s, rd), r, ok)
        case STR_global(rd, global, base, ofs) => 
            evalGlobalUpdate(s, global, OperandContents(s, ofs), OperandContents(s, rd), r, ok)
        case MOV(dst, src) => evalUpdate(s, dst,
            OperandContents(s, src),
            r, ok)
        case MRS(dst, src) => evalUpdate(s, dst, OperandContents(s, src), r, ok)
        case MSR(dst, src) => evalSRegUpdate(s, dst, OperandContents(s, src), r, ok)
        case MRC(dst, src) => evalUpdate(s, dst, OperandContents(s, OSReg(scr)), r, ok)
        case MCR(dst, src) => evalSRegUpdate(s, dst, OperandContents(s, src), r, ok)
        // The program counter update in MOVS is not modeled because the PC is
        // not modeled directly. This models the CPSR update
        case MOVS => evalSRegUpdate(s, OSReg(cpsr), OperandContents(s,OSReg(spsr)), r, ok)
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
    if ValidState(s) && ValidOperand(b.o1) && ValidOperand(b.o2) then
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
        case IfElse(cond, ifT, ifF) => if ValidState(s) && ValidOperand(cond.o1) && ValidOperand(cond.o2) then
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
