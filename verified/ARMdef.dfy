include "assembly.s.dfy"
include "Maybe.dfy"
include "Seq.dfy"

//-----------------------------------------------------------------------------
// Microarchitectural State
//-----------------------------------------------------------------------------
// NB: In FIQ mode, R8 to R12 are also banked, but we don't model this
datatype ARMReg = R0|R1|R2|R3|R4|R5|R6|R7|R8|R9|R10|R11|R12 | SP(spm:mode) | LR(lrm:mode)

// Special register instruction operands
datatype SReg = cpsr | spsr(m:mode) | scr | ttbr0

// A model of the relevant configuration register state. References refer to armv7a spec
// **NOTE** The configuration registers are stored in the state in two places:
// 1) abstractly in state.config and 2) as concrete integers in state.sregs.
// The abstract representation should be used for reasoning about the status of
// the processor and the concrete representation should be used only for
// ensuring that the correct values are stored/returned by instructions
datatype config = Config(cpsr:PSR, spsr:map<mode,PSR>, scr:SCR, ttbr0:TTBR, 
    ex:exception, excount:nat, exstep:nat)
datatype PSR  = PSR(m:mode)           // See B1.3.3
datatype SCR  = SCR(ns:world, irq:bool, fiq:bool) // See B4.1.129
datatype TTBR = TTBR(ptbase:mem)      // See B4.1.154

type mem = int
datatype operand = OConst(n:int) 
    | OReg(r:ARMReg) 
    | OSymbol(sym:string)
    | OSReg(sr:SReg)
    | OSP | OLR 

datatype memstate = MemState(addresses:map<mem, int>,
                             globals:map<operand, seq<int>>)

datatype state = State(regs:map<ARMReg, int>,
                       sregs:map<SReg, int>,
                       m:memstate,
                       conf:config,
                       ok:bool,
                       steps:nat)

// System mode is not modeled
datatype mode = User | FIQ | IRQ | Supervisor | Abort | Undefined | Monitor
datatype priv = PL0 | PL1 // PL2 is only used in Hyp, not modeled
datatype world = Secure | NotSecure
datatype exception = ExAbt | ExUnd | ExIRQ | ExFIQ | ExSVC

//-----------------------------------------------------------------------------
// TODO: get rid of these.
//-----------------------------------------------------------------------------
function method op_r(r:ARMReg):operand
    { OReg(r) }

function method op_sp():operand
    { OSP }

function method op_lr():operand
    { OLR }

function method op_sym(sym:string):operand
    { OSymbol(sym) }

function op_spsr(s:state):operand
    { OSReg(spsr(mode_of_state(s))) }

//-----------------------------------------------------------------------------
// Configuration State
//-----------------------------------------------------------------------------

// See B1.5.1
function world_of_state(s:state):world
{
    if mode_of_state(s) == Monitor then Secure 
    else s.conf.scr.ns 
}

function mode_of_state(s:state):mode
{
    s.conf.cpsr.m
}

function priv_of_mode(m:mode):priv
{
    if m == User then PL0 else PL1
}

function priv_of_state(s:state):priv
    { priv_of_mode(mode_of_state(s)) }

//-----------------------------------------------------------------------------
// Configuration Register Decoding
//-----------------------------------------------------------------------------

// In real life these are more complicated. Add more as needed!

// See B1.3.3
function decode_psr(v:int) : PSR
    requires isUInt32(v)
    requires ValidModeEncoding(and32(v,0x1f))
    { PSR(decode_mode(and32(v, 0x1f))) }

// See B4.1.129
function decode_scr(v:int) : SCR
    requires isUInt32(v)
{
    SCR(
        if and32(v, 1) != 0 then NotSecure else Secure,
        and32(v, 2) != 0, // IRQ bit
        and32(v, 4) != 0 // FIQ bit
        )
}

function decode_ttbr(v:int): TTBR
    requires isUInt32(v)
    ensures PageAligned(decode_ttbr(v).ptbase)
    // assuming 4k alignment, n == 2 / x == 12
    { MaskWithSizeIsAligned(v, 0x1000); TTBR(and32(v, 0xffff_f000)) }

function decode_sreg(s:state, sr:SReg, v:int) : config
    requires ValidConfig(s.conf)
    requires ValidSpecialOperand(s, OSReg(sr))
    requires isUInt32(v)
    requires (sr.cpsr? || sr.spsr?) ==> ValidModeEncoding(and32(v, 0x1f))
    ensures ValidConfig(decode_sreg(s, sr, v))
{
    reveal_ValidConfig();
    match sr
        case ttbr0 => s.conf.(ttbr0 := decode_ttbr(v))
        case cpsr  => s.conf.(cpsr := decode_psr(v))
        case spsr(m)  => 
            assert m != User;
            var spsr' := s.conf.spsr[ m := decode_psr(v) ];
            s.conf.(spsr := spsr') 
        case scr => s.conf.(scr := decode_scr(v))
}

//-----------------------------------------------------------------------------
// Mode / Security State Decoding / Encoding
//-----------------------------------------------------------------------------
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
    // TODO: reinstate | CPSID_IAF(mod:operand)
    | MRS(dstMRS:operand, srcMRS: operand)
    | MSR(dstMSR:operand, srcMSR: operand)
    // Only accesses to SCR are supported
    // (See armv7a ref manual B4.1.129 "Accessing the SCR")
    | MRC(dstMRC:operand,srcMRC:operand)
    | MCR(dstMCR:operand,srcMCR:operand)
    // go to usermode, take an exception, and return
    // Only the special case where rd is pc
    // (See armv7a ref manual A8.8.105 and B9.3.20)
    | MOVS_PCLR_TO_USERMODE_AND_CONTINUE

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

// FIXME: delete or move elsewhere
lemma WordAlignedAdd(x1:int,x2:int)
    requires WordAligned(x1) && WordAligned(x2)
    ensures  WordAligned(x1+x2)
    {}

// FIXME: delete or move elsewhere
lemma WordAlignedAdd_(x1:int,x2:int,y:int)
    requires WordAligned(x1) && WordAligned(x2) && y == x1+x2
    ensures WordAligned(y)
    {}

//-----------------------------------------------------------------------------
// Validity
//-----------------------------------------------------------------------------
predicate ValidState(s:state)
{
    ValidRegState(s.regs) && ValidMemState(s.m) &&
    ValidConfig(s.conf) && ValidSRegState(s.sregs)
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
    isUInt32(c.ttbr0.ptbase) && PageAligned(c.ttbr0.ptbase) &&
    User !in c.spsr &&
    (forall m:mode :: m != User ==> m in c.spsr )
}

predicate {:opaque} ValidSRegState(sregs:map<SReg, int>)
{
    (forall m:mode {:trigger spsr(m)} :: m != User ==> 
        spsr(m) in sregs && isUInt32(sregs[spsr(m)]))
    && spsr(User) !in sregs
    && ttbr0 in sregs && isUInt32(sregs[ttbr0])
    && scr   in sregs && isUInt32(sregs[scr])
    && cpsr  in sregs && isUInt32(sregs[cpsr])
    && ValidModeEncoding(and32(sregs[cpsr], 0x1f))
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
    o.OSReg? && ValidConfig(s.conf) && mode_of_state(s) != User
    &&(
        (o.sr.spsr? && mode_of_state(s) == o.sr.m)
     || (o.sr.scr?  && world_of_state(s) == Secure)
     || (!o.sr.spsr? && !o.sr.scr?))
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
// Exceptions
//-----------------------------------------------------------------------------
function mode_of_exception(conf:config, e:exception): mode
{
    match e
        case ExAbt => Abort
        case ExUnd => Undefined
        case ExIRQ => if conf.scr.irq then Monitor else IRQ
        case ExFIQ => if conf.scr.fiq then Monitor else FIQ
        case ExSVC => Supervisor
}

predicate evalExceptionTaken(s:state, e:exception, r:state)
    requires ValidState(s)
    ensures evalExceptionTaken(s, e, r) ==> ValidState(r)
{
    reveal_ValidRegState();
    reveal_ValidConfig();
    reveal_ValidSRegState();
    var oldmode := mode_of_state(s);
    var newmode := mode_of_exception(s.conf, e);
    // this does not model all of the CPSR update, since we don't model all the bits
    var newpsr := or32(and32(s.sregs[cpsr], 0xffffffe0), encode_mode(newmode));
    ValidState(r) &&
    // update mode, copy CPSR of oldmode to SPSR of newmode, havoc LR
    r == s.(conf := s.conf.(cpsr := PSR(newmode),
                            spsr := s.conf.spsr[newmode := s.conf.cpsr],
                            ex := e, excount := s.conf.excount + 1, exstep := s.steps),
            sregs := s.sregs[cpsr := newpsr][spsr(newmode) := s.sregs[cpsr]],
            regs := s.regs[LR(newmode) := r.regs[LR(newmode)]])
}

//-----------------------------------------------------------------------------
// Userspace execution model
//-----------------------------------------------------------------------------

predicate evalEnterUserspace(s:state, r:state)
    requires ValidState(s)
{
    mode_of_state(s) != User && ValidModeChange'(s, User) &&
    var spsr := op_spsr(s);
    assert ValidSpecialOperand(s, spsr);
    decode_mode'(and32(SpecialOperandContents(s, spsr), 0x1f)) == Just(User) &&
    evalSRegUpdate(s, OSReg(cpsr), SpecialOperandContents(s,spsr), r)
}

predicate evalUserspaceExecution(s:state, r:state)
    requires ValidState(s)
    requires mode_of_state(s) == User
    ensures evalUserspaceExecution(s, r) ==> ValidState(r) && mode_of_state(r) == User
{
    reveal_ValidMemState();
    reveal_ValidRegState();
    // if we can't extract a page table, we know nothing
    var pt := ExtractAbsPageTable(s);
    pt.Just? &&
    var pages := WritablePagesInTable(fromJust(pt));
    ValidState(r) && (forall m:mem :: m in s.m.addresses <==> m in r.m.addresses) &&
    // havoc writable pages and user regs, and take some steps
    r == s.(m := s.m.(addresses := havocPages(pages, s.m.addresses, r.m.addresses)),
            regs := r.regs,
            steps := r.steps)
    && r.steps > s.steps
    && (forall m:mode {:trigger SP(m)} {:trigger LR(m)} :: m != User
        ==> r.regs[SP(m)] == s.regs[SP(m)] && r.regs[LR(m)] == s.regs[LR(m)])
}

function havocPages(pages:set<mem>, s:map<mem, int>, r:map<mem, int>): map<mem, int>
    requires forall m :: m in s <==> m in r
{
    (map m | isUInt32(m) && m in s
        :: if and32(m, 0xffff_f000) in pages then r[m] else s[m])
}

// XXX: To be defined by application code
predicate ApplicationUsermodeContinuationInvariant(s:state, r:state)
    requires ValidState(s)
    ensures ApplicationUsermodeContinuationInvariant(s,r) ==> ValidState(r)

//-----------------------------------------------------------------------------
// Model of page tables for userspace execution
//-----------------------------------------------------------------------------

function method PAGESIZE():int { 0x1000 }

predicate PageAligned(addr:mem)
    ensures PageAligned(addr) ==> WordAligned(addr)
{
    // FIXME: help out poor dafny
    assume addr % 0x1000 == 0 ==> addr % 4 == 0;
    addr % 0x1000 == 0
}

// We model a trivial memory map (for our own code and page tables)
// with a flat 1:1 mapping of virtual to physical addresses.
function {:axiom} PhysBase(): mem
    ensures PageAligned(PhysBase());

// Our model of page tables is also very abstract, because it just needs to encode
// which pages are mapped and their permissions
type AbsPTable = seq<Maybe<AbsL2PTable>>
type AbsL2PTable = seq<Maybe<AbsPTE>>
datatype AbsPTE = AbsPTE(phys: mem, write: bool, exec: bool)

function method ARM_L1PTES(): int { 1024 }
function ARM_L1PTABLE_BYTES(): int { ARM_L1PTES() * BytesPerWord() }
function method ARM_L2PTES(): int { 256 }
function ARM_L2PTABLE_BYTES(): int { ARM_L2PTES() * BytesPerWord() }

predicate WellformedAbsPTable(pt: AbsPTable)
{
    |pt| == ARM_L1PTES()
        && forall i :: 0 <= i < |pt| && pt[i].Just? ==> WellformedAbsL2PTable(fromJust(pt[i]))
}

predicate WellformedAbsL2PTable(pt: AbsL2PTable)
{
    |pt| == ARM_L2PTES() &&
        forall i :: 0 <= i < |pt| && pt[i].Just? ==> WellformedAbsPTE(fromJust(pt[i]))
}

predicate WellformedAbsPTE(pte: AbsPTE)
{
    PageAligned(pte.phys)
}

function ExtractAbsPageTable(s:state): Maybe<AbsPTable>
    requires ValidState(s)
    ensures var r := ExtractAbsPageTable(s);
        r.Just? ==> WellformedAbsPTable(fromJust(r))
{
    reveal_ValidConfig();
    var vbase := s.conf.ttbr0.ptbase + PhysBase();
    if ValidMemRange(s.m, vbase, vbase + ARM_L1PTABLE_BYTES()) then
        ExtractAbsL1PTable(s.m, vbase, 0)
    else
        Nothing
}

function WritablePagesInTable(pt:AbsPTable): set<mem>
    requires WellformedAbsPTable(pt)
    ensures forall m :: m in WritablePagesInTable(pt) ==> PageAligned(m)
{
    (set i, j | 0 <= i < |pt| && pt[i].Just? && 0 <= j < |fromJust(pt[i])|
        && fromJust(pt[i])[j].Just? && fromJust(fromJust(pt[i])[j]).write
        :: fromJust(fromJust(pt[i])[j]).phys + PhysBase())
}

function ExtractAbsL1PTable(m:memstate, vbase:mem, index:nat): Maybe<AbsPTable>
    requires ValidMemState(m)
    requires WordAligned(vbase)
        && ValidMemRange(m, vbase, vbase + ARM_L1PTABLE_BYTES())
    requires 0 <= index <= ARM_L1PTES()
    ensures var r := ExtractAbsL1PTable(m, vbase, index);
        r.Just? ==> |fromJust(r)| == ARM_L1PTES() - index
            && forall i :: 0 <= i < |fromJust(r)| && fromJust(r)[i].Just?
                ==> WellformedAbsL2PTable(fromJust(fromJust(r)[i]))
    decreases ARM_L1PTES() - index
{
    // stopping condition
    if index == ARM_L1PTES() then Just([]) else
    // extract L1 PTE and check its validity
    var pte' := ExtractAbsL1PTE(MemContents(m, vbase + index * BytesPerWord()));
    if pte'.Nothing? then Nothing else
    var pte := fromJust(pte');
    // extract the rest (recursive step)
    var rest := ExtractAbsL1PTable(m, vbase, index + 1);
    if rest.Nothing? then Nothing else
    if pte.Nothing? then
        Just([Nothing] + fromJust(rest))
    else
        // check validity of mem pointed to by L1 PTE
        var l2vbase := fromJust(pte) + PhysBase();
        if !ValidMemRange(m, l2vbase, l2vbase + ARM_L2PTABLE_BYTES()) then Nothing
        else
            // extract L2 table that it points to, and check its validity
            var l2table := ExtractAbsL2PTable(m, l2vbase, 0);
            if l2table.Nothing? then Nothing
            else Just([l2table] + fromJust(rest))
}

/* ARM ref B3.5.1 short descriptor format for first-level page table */
function ExtractAbsL1PTE(pte:int): Maybe<Maybe<int>>
    requires isUInt32(pte)
    ensures var r := ExtractAbsL1PTE(pte);
        r.Just? && fromJust(r).Just? ==> WordAligned(fromJust(fromJust(r)))
{
    // for now, we just consider secure L1 tables in domain zero
    // (i.e., no other bits set)
    var typebits := and32(pte, 0x3);
    var lowbits := and32(pte, 0x3ff);
    MaskWithSizeIsAligned(pte, 0x400);
    var ptbase := and32(pte, 0xfffffc00);
    // if the type is zero, it's an invalid entry, which is fine (maps nothing)
    if typebits == 0 then Just(Nothing)
    // otherwise, the lowbits must be 1 (it maps a page table)
    else if lowbits == 1 then Just(Just(ptbase))
    // anything else is invalid
    else Nothing
}

function ExtractAbsL2PTable(m:memstate, vbase:int, index:nat): Maybe<AbsL2PTable>
    requires ValidMemState(m)
    requires WordAligned(vbase)
        && ValidMemRange(m, vbase, vbase + ARM_L2PTABLE_BYTES())
    requires 0 <= index <= ARM_L2PTES()
    ensures var r := ExtractAbsL2PTable(m, vbase, index);
        r.Just? ==> |fromJust(r)| == ARM_L2PTES() - index
            && forall i :: 0 <= i < |fromJust(r)| && fromJust(r)[i].Just?
                ==> WellformedAbsPTE(fromJust(fromJust(r)[i]))
    decreases ARM_L2PTES() - index
{
    // stopping condition
    if index == ARM_L2PTES() then Just([]) else
    // extract PTE and check its validity
    var pte := ExtractAbsL2PTE(MemContents(m, vbase + index * BytesPerWord()));
    if pte.Nothing? then Nothing else
    // extract the rest (recursive step)
    var rest := ExtractAbsL2PTable(m, vbase, index + 1);
    if rest.Nothing? then Nothing else
    Just([fromJust(pte)] + fromJust(rest))
}

function ExtractAbsL2PTE(pte:int): Maybe<Maybe<AbsPTE>>
    requires isUInt32(pte)
    ensures var r := ExtractAbsL2PTE(pte);
        r.Just? && fromJust(r).Just? ==> WellformedAbsPTE(fromJust(fromJust(r)))
{
    var typebits := and32(pte, 0x3);
    // if the type is zero, it's an invalid entry, which is fine (maps nothing)
    if typebits == 0 then Just(Nothing) else
    // large pages aren't supported
    if typebits == 1 then Nothing else
    var lowbits := and32(pte, 0xfdfc);
    if lowbits != ARM_L2PTE_CONST_BITS() then Nothing else
    var exec := and32(pte, 1) == 0; // !XN bit
    var write := and32(pte, 0x200) == 0; // !AP2 bit
    MaskWithSizeIsAligned(pte, 0x1000);
    var pagebase := and32(pte, 0xfffff000);
    Just(Just(AbsPTE(pagebase, write, exec)))
}

function ARM_L2PTE_CONST_BITS(): int
{
    0x4 /* B */
        + 0x30 /* AP0, AP1 */
        + 0x140 /* TEX */
        + 0x400 /* S */
        + 0x800 /* NG */
}

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

// FIXME! replace this when Dafny gains bitvector support
lemma {:axiom} MaskWithSizeIsAligned(x:int, s:int)
    requires isUInt32(x) && isUInt32(s)
    // s must be a power of two. this is a cheesy approximation for that
    requires s == 0x1000 || s == 0x400
    ensures and32(x, 0x1_0000_0000 - s) % s == 0

//-----------------------------------------------------------------------------
// Evaluation
//-----------------------------------------------------------------------------
function OperandContents(s:state, o:operand): int
    requires ValidOperand(o)
    requires ValidState(s)
    ensures  isUInt32(OperandContents(s,o))
{
    reveal_ValidRegState();
    match o
        case OConst(n) => n
        case OReg(r) => s.regs[r]
        case OSP => s.regs[SP(mode_of_state(s))]
        case OLR => s.regs[LR(mode_of_state(s))]
}

function SpecialOperandContents(s:state, o:operand): int
    requires ValidSpecialOperand(s, o)
    requires ValidState(s)
    ensures  isUInt32(SpecialOperandContents(s,o))
{
    reveal_ValidSRegState();
    match o
        case OSReg(sr) => s.sregs[sr] 
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
    requires ValidOperand(o)
    ensures isUInt32(eval_op(s,o))
    { OperandContents(s,o) }

function takestep(s:state): state
    { s.(steps := s.steps + 1) }

predicate evalUpdate(s:state, o:operand, v:int, r:state)
    requires ValidState(s)
    requires ValidDestinationOperand(o)
    requires isUInt32(v)
    ensures evalUpdate(s, o, v, r) ==> ValidState(r)
{
    reveal_ValidRegState();
    match o
        case OReg(reg) => r == takestep(s).(regs := s.regs[o.r := v])
        case OLR => r == takestep(s).(regs := s.regs[LR(mode_of_state(s)) := v])
        case OSP => r == takestep(s).(regs := s.regs[SP(mode_of_state(s)) := v])
}


predicate evalSRegUpdate(s:state, o:operand, v:int, r:state)
    requires ValidState(s)
    requires ValidSpecialOperand(s, o)
    requires isUInt32(v)
    requires o.sr.cpsr? || o.sr.spsr? ==> ValidModeEncoding(and32(v,0x1f))
    ensures  evalSRegUpdate(s, o, v, r) ==> ValidState(r)
{
    reveal_ValidSRegState();
    r == takestep(s).( conf := decode_sreg(s, o.sr, v),
        sregs := s.sregs[ o.sr := v] )
}

predicate evalMemUpdate(s:state, m:mem, v:int, r:state)
    requires ValidState(s)
    requires ValidMem(s.m, m)
    requires isUInt32(v)
    ensures evalMemUpdate(s, m, v, r) ==> ValidState(r)
{
    reveal_ValidMemState();
    r == takestep(s).(m := s.m.(addresses := s.m.addresses[m := v]))
}

predicate evalGlobalUpdate(s:state, g:operand, offset:nat, v:int, r:state)
    requires ValidState(s)
    requires ValidGlobalOffset(g, offset)
    requires isUInt32(v)
    ensures evalGlobalUpdate(s, g, offset, v, r) ==> ValidState(r) && GlobalWord(r.m, g, offset) == v
{
    reveal_ValidMemState();
    var oldval := s.m.globals[g];
    var newval := oldval[BytesToWords(offset) := v];
    assert |newval| == |oldval|;
    r == takestep(s).(m := s.m.(globals := s.m.globals[g := newval]))
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

predicate evalGuard(s:state, o:obool, r:state)
    requires ValidOperand(o.o1)
    requires ValidOperand(o.o2)
{
    // TODO: this is where we havoc the flags for the comparison, once we model them
    r == takestep(s)
}

predicate ValidModeChange'(s:state, m:mode)
{
    // See B9.1.2
    priv_of_state(s) == PL1 && !(m == Monitor && world_of_state(s) != Secure)
}

predicate ValidModeChange(s:state, v:int)
    requires isUInt32(v)
{
    var enc := and32(v,0x1f);
    ValidModeEncoding(enc) && ValidModeChange'(s, decode_mode(enc))
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
                ValidModeChange(s, OperandContents(s, src)))
        case MRC(dst, src) =>
            ValidMcrMrcOperand(s, src) &&
            ValidRegOperand(dst) 
        case MCR(dst, src) =>
            ValidMcrMrcOperand(s, dst) &&
            ValidRegOperand(src)
        case MOVS_PCLR_TO_USERMODE_AND_CONTINUE =>
            mode_of_state(s) != User &&
            var spsr := OSReg(spsr(mode_of_state(s)));
            assert ValidSpecialOperand(s, spsr);
            var mode := and32(SpecialOperandContents(s, spsr), 0x1f);
            decode_mode'(mode) == Just(User) && ValidModeChange'(s, User)
}

predicate evalIns(ins:ins, s:state, r:state)
{
    if !s.ok || !ValidInstruction(s, ins) then !r.ok
    else match ins
        case ADD(dst, src1, src2) => evalUpdate(s, dst,
            ((OperandContents(s, src1) + OperandContents(s, src2))),
            r)
        case SUB(dst, src1, src2) => evalUpdate(s, dst,
            ((OperandContents(s, src1) - OperandContents(s, src2))),
            r)
        case MUL(dst, src1, src2) => evalUpdate(s, dst,
            ((OperandContents(s, src1) * OperandContents(s, src2))),
            r)
        case UDIV(dst, src1, src2) => evalUpdate(s, dst,
            ((OperandContents(s, src1) / OperandContents(s, src2))),
            r)
        case AND(dst, src1, src2) => evalUpdate(s, dst,
            and32(eval_op(s, src1), eval_op(s, src2)),
            r)
        case ORR(dst, src1, src2) => evalUpdate(s, dst,
            or32(eval_op(s, src1), eval_op(s, src2)),
            r)
        case EOR(dst, src1, src2) => evalUpdate(s, dst,
            xor32(eval_op(s, src1), eval_op(s, src2)),
            r)
        case ROR(dst, src1, src2) => if !(src2.OConst? && 0 <= src2.n <32) then !r.ok
            else evalUpdate(s, dst,
                ror32(eval_op(s, src1), eval_op(s, src2)),
                r)
        case LSL(dst, src1, src2) => if !(src2.OConst? && 0 <= src2.n <32) then !r.ok 
            else evalUpdate(s, dst,
                shl32(eval_op(s, src1), eval_op(s, src2)),
                r)
        case LSR(dst, src1, src2) => if !(src2.OConst? && 0 <= src2.n <32) then !r.ok
            else evalUpdate(s, dst,
                shr32(eval_op(s, src1), eval_op(s, src2)),
                r)
        case MVN(dst, src) => evalUpdate(s, dst,
            not32(eval_op(s, src)), r)
        case LDR(rd, base, ofs) => 
            evalUpdate(s, rd, MemContents(s.m, OperandContents(s, base) +
                OperandContents(s, ofs)), r)
        case LDR_global(rd, global, base, ofs) => 
            evalUpdate(s, rd, GlobalWord(s.m, global, OperandContents(s, ofs)), r)
        case LDR_reloc(rd, name) =>
            evalUpdate(s, rd, AddressOfGlobal(name), r)
        case STR(rd, base, ofs) => 
            evalMemUpdate(s, OperandContents(s, base) +
                OperandContents(s, ofs), OperandContents(s, rd), r)
        case STR_global(rd, global, base, ofs) => 
            evalGlobalUpdate(s, global, OperandContents(s, ofs), OperandContents(s, rd), r)
        case MOV(dst, src) => evalUpdate(s, dst,
            OperandContents(s, src),
            r)
        case MRS(dst, src) => evalUpdate(s, dst, SpecialOperandContents(s, src), r)
        case MSR(dst, src) => evalSRegUpdate(s, dst, OperandContents(s, src), r)
        case MRC(dst, src) => evalUpdate(s, dst, SpecialOperandContents(s, OSReg(scr)), r)
        case MCR(dst, src) => evalSRegUpdate(s, dst, OperandContents(s, src), r)
        case MOVS_PCLR_TO_USERMODE_AND_CONTINUE => 
            exists ex, s2, s3, s4
                :: ValidState(s2) && ValidState(s3) && ValidState(s4)
                && evalEnterUserspace(s, s2)
                && evalUserspaceExecution(s2, s3)
                && evalExceptionTaken(s3, ex, s4)
                && ApplicationUsermodeContinuationInvariant(s4, r)
}

predicate evalBlock(block:codes, s:state, r:state)
{
    if block.CNil? then
        r == s
    else
        exists r' :: evalCode(block.hd, s, r') && evalBlock(block.tl, r', r)
}

predicate evalIfElse(cond:obool, ifT:code, ifF:code, s:state, r:state)
    decreases if ValidState(s) && ValidOperand(cond.o1) && ValidOperand(cond.o2) && evalOBool(s, cond) then ifT else ifF
{
    if ValidState(s) && s.ok && ValidOperand(cond.o1) && ValidOperand(cond.o2) then
        exists s' :: evalGuard(s, cond, s') && (if evalOBool(s, cond) then evalCode(ifT, s', r) else evalCode(ifF, s', r))
    else
        !r.ok
}

predicate evalWhile(b:obool, c:code, n:nat, s:state, r:state)
    decreases c, n
{
    if ValidState(s) && s.ok && ValidOperand(b.o1) && ValidOperand(b.o2) then
        if n == 0 then
            !evalOBool(s, b) && evalGuard(s, b, r)
        else
            exists s':state, r':state :: evalGuard(s, b, s') && evalOBool(s, b) && evalCode(c, s', r') && evalWhile(b, c, n - 1, r', r)
    else
        !r.ok
}

predicate evalCode(c:code, s:state, r:state)
    decreases c, 0
{
    match c
        case Ins(ins) => evalIns(ins, s, r)
        case Block(block) => evalBlock(block, s, r)
        case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
        case While(cond, body) => exists n:nat :: evalWhile(cond, body, n, s, r)
}
