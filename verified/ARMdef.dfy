include "Maybe.dfy"
include "Seq.dfy"
include "bitvectors.s.dfy"
include "alignment.s.dfy"
include "words_and_bytes.s.dfy"

//-----------------------------------------------------------------------------
// Core types (for a 32-bit word-aligned machine)
//-----------------------------------------------------------------------------
const WORDSIZE:int := 4;
predicate WordAligned(i:int) { i % WORDSIZE == 0 }
function  WordsToBytes(w:int): int
    ensures WordAligned(WordsToBytes(w))
{ WORDSIZE * w }
function  BytesToWords(b:int): int
    requires WordAligned(b)
{ b / WORDSIZE }

function {:opaque} TruncateWord(x:int): word
{ x % UINT32_LIM }

type addr = x | isUInt32(x) && WordAligned(x)
type shift_amount = s | 0 <= s < 32 // Some shifts allow s=32, but we'll be conservative for simplicity

//-----------------------------------------------------------------------------
// Microarchitectural State
//-----------------------------------------------------------------------------
// NB: In FIQ mode, R8 to R12 are also banked, but we don't model this
datatype ARMReg = R0|R1|R2|R3|R4|R5|R6|R7|R8|R9|R10|R11|R12| SP(spm:mode) | LR(lrm:mode)

// Special register instruction operands
// TODO (style nit): uppercase constructors
datatype SReg = cpsr | spsr(m:mode) | SCR | ttbr0

// A model of the relevant configuration register state. References refer to armv7a spec
// **NOTE** The configuration registers are stored in the state in two places:
// 1) abstractly in state.config and 2) as concrete integers in state.sregs.
// The abstract representation should be used for reasoning about the status of
// the processor and the concrete representation should be used only for
// ensuring that the correct values are stored/returned by instructions
datatype config = Config(cpsr:PSR, spsr:map<mode,PSR>, scr:SCR, ttbr0:TTBR, 
    ex:exception, excount:nat, exstep:nat)
datatype PSR  = PSR(m:mode, f:bool, i:bool) // See B1.3.3
datatype SCR  = SCRT(ns:world, irq:bool, fiq:bool) // See B4.1.129
datatype TTBR = TTBR(ptbase:addr)      // See B4.1.154

datatype Shift = LSLShift(amount_lsl:shift_amount)
               | LSRShift(amount_lsr:shift_amount)
               | RORShift(amount_ror:shift_amount)

datatype operand = OConst(n:word)
    | OReg(r:ARMReg)
    | OShift(reg:ARMReg, s:Shift)
    | OSReg(sr:SReg)
    | OSP | OLR

type memmap = map<addr, word>
type symbol = string
type globalsmap = map<symbol, seq<word>>
datatype memstate = MemState(addresses:memmap,
                             globals:globalsmap)

datatype state = State(regs:map<ARMReg, word>,
                       sregs:map<SReg, word>,
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

function spsr_of_state(s:state): PSR
    requires ValidState(s)
    requires mode_of_state(s) != User
{
    reveal_ValidSRegState();
    s.conf.spsr[mode_of_state(s)]
}

predicate interrupts_enabled(s:state)
{
    !s.conf.cpsr.f || !s.conf.cpsr.i
}

//-----------------------------------------------------------------------------
// Configuration Register Decoding
//-----------------------------------------------------------------------------

// In real life these are more complicated. Add more as needed!

function psr_mask_mode(v:word): word
{
    BitwiseAnd(v, 0x1f)
}

predicate ValidPsrWord(v:word)
{
    ValidModeEncoding(psr_mask_mode(v))
}

// See B1.3.3
function decode_psr(v:word) : PSR
    requires ValidPsrWord(v)
{
    PSR(decode_mode(psr_mask_mode(v)),
        BitwiseAnd(v, 0x40) != 0, // FIQ mask bit
        BitwiseAnd(v, 0x80) != 0  // IRQ mask bit
        )
}

// See B4.1.129
function decode_scr(v:word) : SCR
{
    SCRT(
        if BitwiseAnd(v, 1) != 0 then NotSecure else Secure,
        BitwiseAnd(v, 2) != 0, // IRQ bit
        BitwiseAnd(v, 4) != 0 // FIQ bit
        )
}

function decode_ttbr(v:word): TTBR
    ensures PageAligned(decode_ttbr(v).ptbase)
    // assuming 4k alignment, n == 2 / x == 12
{
    var ptbase := BitwiseMaskHigh(v, 12);
    reveal_PageAligned();
    TTBR(ptbase)
}

predicate ValidSReg(sr:SReg)
{
    sr.spsr? ==> sr.m != User
}

function update_config_from_sreg(s:state, sr:SReg, v:word): config
    requires ValidSRegState(s.sregs, s.conf) && ValidSReg(sr)
    requires (sr.cpsr? || sr.spsr?) ==> ValidPsrWord(v)
{
    reveal_ValidSRegState();
    match sr
        case ttbr0 => s.conf.(ttbr0 := decode_ttbr(v))
        case cpsr  => s.conf.(cpsr := decode_psr(v))
        case spsr(m)  => 
            assert m != User;
            var spsr' := s.conf.spsr[ m := decode_psr(v) ];
            s.conf.(spsr := spsr') 
        case SCR => s.conf.(scr := decode_scr(v))
}

//-----------------------------------------------------------------------------
// Mode / Security State Decoding / Encoding
//-----------------------------------------------------------------------------
function method encode_ns(ns:world): word
    { if ns == NotSecure then 1 else 0 }

function method encode_mode(m:mode): word
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

function method decode_mode'(e:word):Maybe<mode>
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

predicate ValidModeEncoding(e:word)
{
    decode_mode'(e).Just?
}

function method decode_mode(e:word):mode
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
    | LSL(dstLSL:operand, src1LSL:operand, src2LSL:operand)
    | LSR(dstLSR:operand, src1LSR:operand, src2LSR:operand)
    | REV(dstREV:operand, srcREV:operand)
    | MOV(dstMOV:operand, srcMOV:operand)
    | MVN(dstMVN:operand, srcMVN:operand)
    | LDR(rdLDR:operand,  baseLDR:operand, ofsLDR:operand)
    | LDR_global(rdLDR_global:operand, globalLDR:symbol,
                 baseLDR_global:operand, ofsLDR_global:operand)
    | LDR_reloc(rdLDR_reloc:operand, symLDR_reloc:symbol)
    | STR(rdSTR:operand,  baseSTR:operand, ofsSTR:operand)
    | STR_global(rdSTRR_global:operand, globalSTR:symbol,
                 baseSTR_global:operand, ofsSTR_global:operand)
    | MRS(dstMRS:operand, srcMRS: operand)
    | MSR(dstMSR:operand, srcMSR: operand)
    // Accesses to banked regs and SCR are supported
    // (See armv7a ref manual B4.1.129 "Accessing the SCR")
    | MRC(dstMRC:operand,srcMRC:operand)
    | MCR(dstMCR:operand,srcMCR:operand)
    | CPSID_IAF(mod:operand)
    // go to usermode, take an exception, and return
    // Only the special case where rd is pc and src is lr
    // (See armv7a ref manual A8.8.105 and B9.3.20)
    | MOVS_PCLR_TO_USERMODE_AND_CONTINUE

//-----------------------------------------------------------------------------
// Code Representation
//-----------------------------------------------------------------------------
datatype ocmp = OEq | ONe | OLe | OGe | OLt | OGt | OTstEq | OTstNe
datatype obool = OCmp(cmp:ocmp, o1:operand, o2:operand)

datatype codes = CNil | va_CCons(hd:code, tl:codes)

datatype code =
  Ins(ins:ins)
| Block(block:codes)
| IfElse(ifCond:obool, ifTrue:code, ifFalse:code)
| While(whileCond:obool, whileBody:code)

//-----------------------------------------------------------------------------
// Validity
//-----------------------------------------------------------------------------
predicate ValidState(s:state)
{
    ValidRegState(s.regs) && ValidMemState(s.m) && ValidSRegState(s.sregs, s.conf)
}

predicate {:opaque} ValidRegState(regs:map<ARMReg, word>)
{
    forall r:ARMReg :: r in regs
}

predicate {:opaque} ValidSRegState(sregs:map<SReg, word>, c:config)
{
    cpsr in sregs
    && ValidPsrWord(sregs[cpsr]) && c.cpsr == decode_psr(sregs[cpsr])
    && (forall m:mode :: (m != User) == (spsr(m) in sregs) == (m in c.spsr))
    && (forall m:mode :: m != User ==>
        ValidPsrWord(sregs[spsr(m)]) && c.spsr[m] == decode_psr(sregs[spsr(m)]))
    && ttbr0 in sregs && c.ttbr0 == decode_ttbr(sregs[ttbr0])
    && SCR in sregs && c.scr == decode_scr(sregs[SCR])
}

// All valid states have the same memory address domain, but we don't care what 
// it is (at this level).
function {:axiom} TheValidAddresses(): set<addr>

predicate {:opaque} ValidMemState(s:memstate)
{
    ValidAddrMemState(s.addresses) && ValidGlobalState(s.globals)
}

predicate ValidAddrMemState(mem: memmap)
{
    (forall a:addr :: a in TheValidAddresses() <==> a in mem)
}

predicate ValidGlobalState(globals: globalsmap)
{
    // globals: same names/sizes as decls
    (forall g :: g in TheGlobalDecls() <==> g in globals)
    && (forall g :: g in TheGlobalDecls()
        ==> |globals[g]| == BytesToWords(TheGlobalDecls()[g]))
}

// XXX: ValidOperand is just the subset used in "normal" integer instructions
predicate ValidOperand(o:operand)
{
    match o
        case OConst(n) => true
        case OReg(r) => !(r.SP? || r.LR?) // not used directly
        case OShift(_,_) => false
        case OSP => true
        case OLR => true
        case OSReg(sr) => false
}

predicate ValidSecondOperand(o:operand)
{
    ValidOperand(o) 
 || (o.OShift? && !(o.reg.SP? || o.reg.LR?))
}

predicate ValidBankedRegOperand(s:state, o:operand)
{
    // See B9.2.2 Usage restrictions on the Banked register transfer instructions
    // to simplify the spec, we only consider secure PL1 modes
    priv_of_state(s) == PL1 && world_of_state(s) == Secure
    && ( (o.OReg? && (
            (o.r.SP? && o.r.spm != mode_of_state(s))
            || (o.r.LR? && o.r.lrm != mode_of_state(s))
            ) )
       || (o.OSReg? && ValidSReg(o.sr) && o.sr.spsr? && o.sr.m != mode_of_state(s))
      )
}

predicate ValidMrsMsrOperand(s:state,o:operand)
{
    ValidBankedRegOperand(s,o)
        || (o.OSReg? && ValidSReg(o.sr)
            && (o.sr.cpsr? || (o.sr.spsr? && mode_of_state(s) == o.sr.m)))
}

predicate ValidMcrMrcOperand(s:state,o:operand)
{
    // to simplify the spec, we only consider secure PL1 modes
    o.OSReg? && priv_of_state(s) == PL1 && world_of_state(s) == Secure
    && (o.sr.SCR? || o.sr.ttbr0?)
}

predicate ValidAnySrcOperand(s:state, o:operand)
{
    ValidOperand(o) || ValidSecondOperand(o)
    || ValidBankedRegOperand(s,o) || ValidMrsMsrOperand(s,o) || ValidMcrMrcOperand(s,o)
}

predicate ValidMem(addr:int)
{
    isUInt32(addr) && WordAligned(addr) && addr in TheValidAddresses()
}

predicate ValidMemRange(base:int, limit:int)
{
    ValidMem(base) && ValidMem(limit - WORDSIZE)
    && forall a:addr :: base <= a < limit && WordAligned(a) ==> ValidMem(a)
}

predicate ValidShiftOperand(s:state, o:operand)
    requires ValidState(s)
    { ValidOperand(o) && OperandContents(s, o) < 32 }

predicate ValidRegOperand(o:operand)
    { !o.OConst? && !o.OShift? && ValidOperand(o) }

//-----------------------------------------------------------------------------
// Globals
//-----------------------------------------------------------------------------
type globaldecls = map<symbol, addr>

predicate ValidGlobal(g:symbol)
{
    g in TheGlobalDecls()
}

predicate ValidGlobalDecls(decls:globaldecls)
{
    forall d :: d in decls ==> decls[d] != 0
}

predicate ValidGlobalAddr(g:symbol, addr:int)
{
    ValidGlobal(g) && WordAligned(addr) 
 && AddressOfGlobal(g) <= addr < AddressOfGlobal(g) + SizeOfGlobal(g)
}

predicate ValidGlobalOffset(g:symbol, offset:int)
{
    ValidGlobal(g) && WordAligned(offset) 
 && 0 <= offset < SizeOfGlobal(g)
}

// globals have an unknown (uint32) address, only establised by LDR-reloc
function {:axiom} AddressOfGlobal(g:symbol): addr

function SizeOfGlobal(g:symbol): word
    requires ValidGlobal(g)
    ensures WordAligned(SizeOfGlobal(g))
{
    TheGlobalDecls()[g]
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

function {:opaque} update_psr(oldpsr:word, newmode:word, maskfiq:bool, maskirq:bool): word
    requires ValidPsrWord(oldpsr)
    requires ValidModeEncoding(newmode)
    //ensures ValidPsrWord(update_psr(oldpsr, newmode, maskfiq, maskirq))
{
    var maskbits := BitsAsWord(BitOr(if maskfiq then 0x40 else 0,
                                     if maskirq then 0x80 else 0));
    BitwiseOr(BitwiseAnd(oldpsr, 0xffffffe0), BitwiseOr(newmode, maskbits))
}

function psr_of_exception(s:state, e:exception): word
    requires ValidState(s)
{
    reveal_ValidSRegState();

    // per B1.9 exception descriptions, this models the CPSR updates
    // as they affect our limited view of the PSRs; summary: all
    // exceptions we care about mask IRQs, but FIQs are only masked by
    // a FIQ exception or any exception taken to monitor mode
    var newmode := mode_of_exception(s.conf, e);
    var maskfiq := e == ExFIQ || newmode == Monitor;
    var oldpsr := s.sregs[cpsr];
    update_psr(s.sregs[cpsr], encode_mode(newmode), maskfiq, true)
}

predicate evalExceptionTaken(s:state, e:exception, r:state)
    requires ValidState(s)
    ensures evalExceptionTaken(s, e, r) ==> ValidState(r)
    //ensures evalExceptionTaken(s, e, r) && s.ok ==> r.ok
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
    var oldmode := mode_of_state(s);
    var newmode := mode_of_exception(s.conf, e);
    // this does not model all of the CPSR update, since we don't model all the bits
    var newpsr := psr_of_exception(s, e);
    ValidPsrWord(newpsr) && ValidState(r) &&
    // update mode, copy CPSR of oldmode to SPSR of newmode, havoc LR
    r == takestep(s).(conf := s.conf.(cpsr := decode_psr(newpsr),
                            spsr := s.conf.spsr[newmode := s.conf.cpsr],
                            ex := e, excount := s.conf.excount + 1, exstep := s.steps),
            sregs := s.sregs[cpsr := newpsr][spsr(newmode) := s.sregs[cpsr]],
            regs := s.regs[LR(newmode) := nondeterministic_word(s, -2)])
}

//-----------------------------------------------------------------------------
// Userspace execution model
//-----------------------------------------------------------------------------

predicate evalEnterUserspace(s:state, r:state)
    requires ValidState(s)
    ensures evalEnterUserspace(s, r) ==> ValidState(r) && mode_of_state(r) == User
{
    var spsr := OSReg(spsr(mode_of_state(s)));
    mode_of_state(s) != User
    && decode_mode'(psr_mask_mode(OperandContents(s, spsr))) == Just(User)
    && evalMOVSPCLR(s, r)
}

predicate evalMOVSPCLR(s:state, r:state)
    requires ValidState(s)
{
    priv_of_state(s) == PL1 &&
    var spsr_reg := OSReg(spsr(mode_of_state(s)));
    assert ValidSReg(spsr_reg.sr);
    var spsr_val := OperandContents(s, spsr_reg);
    ValidPsrWord(spsr_val) &&
    ValidModeChange(s, spsr_val) &&
    evalUpdate(takestep(s), OSReg(cpsr), spsr_val, r)
}

predicate {:opaque} evalUserspaceExecution(s:state, r:state)
    requires ValidState(s)
    ensures  evalUserspaceExecution(s, r) ==> ValidState(r)
    //ensures  evalUserspaceExecution(s, r) && s.ok ==> r.ok
{
    reveal_ValidMemState();
    reveal_ValidRegState();
    mode_of_state(s) == User &&
    // if we can't extract a page table, we know nothing
    var pt := ExtractAbsPageTable(s);
    pt.Just? &&
    var pages := WritablePagesInTable(fromJust(pt));
    ValidState(r) &&
    // havoc writable pages and user regs, and take some steps
    r == s.(m := s.m.(addresses := havocPages(pages, s)),
            regs := r.regs,
            steps := r.steps)
    && r.steps > s.steps
    && (forall m:mode {:trigger SP(m)} {:trigger LR(m)} :: m != User
        ==> r.regs[SP(m)] == s.regs[SP(m)] && r.regs[LR(m)] == s.regs[LR(m)])
}

function havocPages(pages:set<addr>, s:state): memmap
    requires ValidState(s)
{
    // XXX: inlined part of ValidMem to help Dafny's heuristics see a bounded set
    (map a:addr | ValidMem(a) && a in TheValidAddresses() ::
     if BitwiseMaskHigh(a, 12) in pages then nondeterministic_word(s, a)
     else MemContents(s.m, a))
}

// To be defined/established by "application" code (i.e. komodo exception handlers)
// XXX: for soundness, application must prove the essential properties

predicate EssentialContinuationInvariantProperties(s:state, r:state)
{
    (ValidState(s) ==> ValidState(r)) && (s.ok ==> r.ok)
}

predicate {:axiom} UsermodeContinuationInvariant(s:state, r:state)
    requires ValidState(s)
    ensures UsermodeContinuationInvariant(s, r)
        ==> EssentialContinuationInvariantProperties(s, r)

predicate {:axiom} InterruptContinuationInvariant(s:state, r:state)
    requires ValidState(s)
    ensures InterruptContinuationInvariant(s, r)
    ==> (EssentialContinuationInvariantProperties(s, r)
        // B1.8.3 "Link values saved on exception entry"
        // these are necessary to get MOVS PC, LR to restore the same PC
        // (this is needed here, because we don't model the PC explicitly)
        && OperandContents(r, OLR) == TruncateWord(OperandContents(s, OLR) - 4))

//-----------------------------------------------------------------------------
// Model of page tables for userspace execution
//-----------------------------------------------------------------------------

const PAGESIZE:int := 0x1000;

predicate {:opaque} PageAligned(addr:int)
    ensures PageAligned(addr) ==> WordAligned(addr)
{
    lemma_PageAlignedImpliesWordAligned(addr);
    addr % PAGESIZE == 0
}

// We model a trivial memory map (for our own code and page tables)
// with a flat 1:1 mapping of virtual to physical addresses.
function {:axiom} PhysBase(): addr
    ensures PageAligned(PhysBase());

// Our model of page tables is also very abstract, because it just needs to encode
// which pages are mapped and their permissions
type AbsPTable = seq<Maybe<AbsL2PTable>>
type AbsL2PTable = seq<Maybe<AbsPTE>>
datatype AbsPTE = AbsPTE(phys: addr, write: bool, exec: bool)

const ARM_L1PTES:int := 1024;
const ARM_L1PTABLE_BYTES:int := PAGESIZE; // WordsToBytes(ARM_L1PTES)
const ARM_L2PTES:int := 256;
const ARM_L2PTABLE_BYTES:int := 0x400; // WordsToBytes(ARM_L2PTES)

predicate WellformedAbsPTable(pt: AbsPTable)
{
    |pt| == ARM_L1PTES
        && forall i :: 0 <= i < |pt| && pt[i].Just? ==> WellformedAbsL2PTable(fromJust(pt[i]))
}

predicate WellformedAbsL2PTable(pt: AbsL2PTable)
{
    |pt| == ARM_L2PTES && forall i :: 0 <= i < |pt| ==> WellformedAbsPTE(pt[i])
}

predicate WellformedAbsPTE(pte: Maybe<AbsPTE>)
{
    pte.Just? ==> PageAligned(pte.v.phys) && isUInt32(pte.v.phys + PhysBase())
}

function ExtractAbsPageTable(s:state): Maybe<AbsPTable>
    requires ValidState(s)
    ensures var r := ExtractAbsPageTable(s);
        r.Just? ==> WellformedAbsPTable(fromJust(r))
{
    var vbase := s.conf.ttbr0.ptbase + PhysBase();
    if ValidAbsL1PTable(s.m, vbase) then
        Just(ExtractAbsL1PTable(s.m, vbase))
    else
        Nothing
}

function WritablePagesInTable(pt:AbsPTable): set<addr>
    requires WellformedAbsPTable(pt)
    //ensures forall m:addr :: m in WritablePagesInTable(pt) ==> PageAligned(m)
{
    (set i, j | 0 <= i < |pt| && pt[i].Just? && 0 <= j < |pt[i].v|
        && pt[i].v[j].Just? && pt[i].v[j].v.write
        :: pt[i].v[j].v.phys + PhysBase())
}

function WordOffset(a:addr, i:int): addr
    requires isUInt32(a + WordsToBytes(i))
    ensures WordAligned(WordOffset(a, i))
{ a + WordsToBytes(i) }

predicate ValidAbsL1PTable(m:memstate, vbase:int)
    requires ValidMemState(m)
{
    WordAligned(vbase) && ValidMemRange(vbase, vbase + ARM_L1PTABLE_BYTES)
    // all L1 PTEs are valid, and all non-zero PTEs point to valid L2 tables
    && forall i | 0 <= i < ARM_L1PTES :: (
        var ptew := MemContents(m, WordOffset(vbase, i));
        ValidAbsL1PTEWord(ptew) &&
            var ptem := ExtractAbsL1PTE(ptew);
            ptem.Just? ==> (
                var l2ptr:int := ptem.v + PhysBase();
                isUInt32(l2ptr) && WordAligned(l2ptr) && ValidAbsL2PTable(m, l2ptr)))
}

function ExtractAbsL1PTable(m:memstate, vbase:addr): AbsPTable
    requires ValidMemState(m)
    requires ValidAbsL1PTable(m, vbase)
    ensures WellformedAbsPTable(ExtractAbsL1PTable(m, vbase))
{
    var f := imap i | 0 <= i < ARM_L1PTES :: (
        var pte := ExtractAbsL1PTE(MemContents(m, WordOffset(vbase, i)));
        if pte.Nothing? then Nothing else Just(ExtractAbsL2PTable(m, pte.v + PhysBase()))
        );
    var indices := SeqOfNumbersInRightExclusiveRange(0, ARM_L1PTES);
    IMapSeqToSeq(indices, f)
}

/* ARM ref B3.5.1 short descriptor format for first-level page table */
predicate ValidAbsL1PTEWord(pte:word)
{
    var typebits := BitwiseAnd(pte, 0x3);
    var lowbits := BitwiseAnd(pte, 0x3fc);
    // for now, we just consider secure L1 tables in domain zero
    // (i.e., no other bits set)
    typebits == 0 || (typebits == 1 && lowbits == 0)
}

function ExtractAbsL1PTE(pte:word): Maybe<addr>
    requires ValidAbsL1PTEWord(pte)
    ensures var r := ExtractAbsL1PTE(pte); r.Just? ==> WordAligned(r.v)
{
    var typebits := BitwiseAnd(pte, 0x3);
    // if the type is zero, it's an invalid entry, which is fine (maps nothing)
    if typebits == 0 then Nothing else
    // otherwise, it must map a page table
    var ptbase := BitwiseMaskHigh(pte, 10); // BitwiseAnd(pte, 0xfffffc00);
    lemma_1KAlignedImpliesWordAligned(ptbase); // XXX: help Dafny see WordAligned
    Just(ptbase)
}

predicate ValidAbsL2PTable(m:memstate, vbase:addr)
    requires ValidMemState(m)
{
    WordAligned(vbase)
        && ValidMemRange(vbase, vbase + ARM_L2PTABLE_BYTES)
        && forall i | 0 <= i < ARM_L2PTES :: ValidAbsL2PTEWord(MemContents(m, WordOffset(vbase, i)))
}

function ExtractAbsL2PTable(m:memstate, vbase:addr): AbsL2PTable
    requires ValidMemState(m)
    requires ValidAbsL2PTable(m, vbase)
    ensures WellformedAbsL2PTable(ExtractAbsL2PTable(m, vbase))
{
    var f := imap i | 0 <= i < ARM_L2PTES :: ExtractAbsL2PTE(MemContents(m, WordOffset(vbase, i)));
    var indices := SeqOfNumbersInRightExclusiveRange(0, ARM_L2PTES);
    IMapSeqToSeq(indices, f)
}

const ARM_L2PTE_NX_BIT: bv32 := 0x1; // XN
const ARM_L2PTE_RO_BIT: bv32 := 0x200; // AP2
const ARM_L2PTE_CONST_BITS: bv32 := 0xd74; // B, AP0, AP1, TEX, S, NG

predicate ValidAbsL2PTEWord(pteword:word)
{
    var pte := WordAsBits(pteword);
    var typebits := BitAnd(pte, 0x3);
    var lowbits := BitAnd(pte, 0xdfc);
    var pagebase := BitwiseMaskHigh(pteword, 12);
    typebits == 0 || (typebits != 1 && lowbits == ARM_L2PTE_CONST_BITS && isUInt32(pagebase + PhysBase()))
}

function ExtractAbsL2PTE(pteword:word): Maybe<AbsPTE>
    requires ValidAbsL2PTEWord(pteword)
    ensures WellformedAbsPTE(ExtractAbsL2PTE(pteword))
{
    var pte := WordAsBits(pteword);
    var typebits := BitAnd(pte, 0x3);
    var exec := BitAnd(pte, ARM_L2PTE_NX_BIT) == 0;
    var write := BitAnd(pte, ARM_L2PTE_RO_BIT) == 0;
    var pagebase := BitwiseMaskHigh(pteword, 12); // BitwiseAnd(pteword, 0xfffff000);
    assert PageAligned(pagebase) by { reveal_PageAligned(); }
    // if the type is zero, it's an invalid entry, which is fine (maps nothing)
    if typebits == 0 then Nothing else Just(AbsPTE(pagebase, write, exec))
}

//-----------------------------------------------------------------------------
// Functions for bitwise operations
//-----------------------------------------------------------------------------

function BitwiseXor(x:word, y:word): word
    { BitsAsWord(BitXor(WordAsBits(x), WordAsBits(y))) }

function BitwiseAnd(x:word, y:word): word
    { BitsAsWord(BitAnd(WordAsBits(x), WordAsBits(y))) }

function BitwiseOr(x:word, y:word): word
    { BitsAsWord(BitOr(WordAsBits(x), WordAsBits(y))) }

function BitwiseNot(x:word): word
    { BitsAsWord(BitNot(WordAsBits(x))) }

function LeftShift(x:word, amount:word): word
    requires 0 <= amount < 32;
    { BitsAsWord(BitShiftLeft(WordAsBits(x), amount)) }

function RightShift(x:word, amount:word): word
    requires 0 <= amount < 32;
    { BitsAsWord(BitShiftRight(WordAsBits(x), amount)) }

function RotateRight(x:word, amount:shift_amount) : word
    requires 0 <= amount < 32;
    { BitsAsWord(BitRotateRight(WordAsBits(x), amount)) }

//-----------------------------------------------------------------------------
// Functions for bytewise operations
//-----------------------------------------------------------------------------

function bswap32(x:word) : word { 
    var bytes := WordToBytes(x);
    BytesToWord(bytes[3], bytes[2], bytes[1], bytes[0])
}

//-----------------------------------------------------------------------------
// Evaluation
//-----------------------------------------------------------------------------

function EvalShift(w:word, shift:Shift) : word
{
    match shift
        case LSLShift(amount) => LeftShift(w, amount)
        case LSRShift(amount) => RightShift(w, amount)
        case RORShift(amount) => RotateRight(w, amount)
}

function OperandContents(s:state, o:operand): word
    requires ValidState(s)
    requires ValidAnySrcOperand(s, o)
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
    match o
        case OConst(n) => n
        case OReg(r) => s.regs[r]
        case OSReg(sr) => s.sregs[sr] 
        case OShift(r, amount) => EvalShift(s.regs[r], amount)
        case OSP => s.regs[SP(mode_of_state(s))]
        case OLR => s.regs[LR(mode_of_state(s))]
}

function MemContents(s:memstate, m:addr): word
    requires ValidMemState(s)
    requires ValidMem(m)
{
    reveal_ValidMemState();
    //assert m in s.addresses;
    s.addresses[m]
}

function GlobalFullContents(s:memstate, g:symbol): seq<word>
    requires ValidMemState(s)
    requires ValidGlobal(g)
    ensures WordsToBytes(|GlobalFullContents(s, g)|) == SizeOfGlobal(g)
{
    reveal_ValidMemState();
    s.globals[g]
}

function GlobalWord(s:memstate, g:symbol, offset:word): word
    requires ValidGlobalOffset(g, offset)
    requires ValidMemState(s)
{
    reveal_ValidMemState();
    GlobalFullContents(s, g)[BytesToWords(offset)]
}

function takestep(s:state): state
    { s.(steps := s.steps + 1) }

predicate evalUpdate(s:state, o:operand, v:word, r:state)
    requires ValidState(s)
    requires ValidRegOperand(o) || ValidBankedRegOperand(s,o)
        || ValidMrsMsrOperand(s,o) || ValidMcrMrcOperand(s,o)
    requires o.OSReg? ==> (ValidSReg(o.sr)
        && (o.sr.cpsr? || o.sr.spsr? ==> ValidPsrWord(v)))
    ensures evalUpdate(s, o, v, r) ==> ValidState(r)
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
    match o
        case OReg(reg) => r == s.(regs := s.regs[o.r := v])
        case OLR => r == s.(regs := s.regs[LR(mode_of_state(s)) := v])
        case OSP => r == s.(regs := s.regs[SP(mode_of_state(s)) := v])
        case OSReg(sr) => r == s.(sregs := s.sregs[sr := v],
                                conf := update_config_from_sreg(s, sr, v))
}

predicate evalMemUpdate(s:state, m:addr, v:word, r:state)
    requires ValidState(s)
    requires ValidMem(m)
    ensures evalMemUpdate(s, m, v, r) ==> ValidState(r)
{
    reveal_ValidMemState();
    r == s.(m := s.m.(addresses := s.m.addresses[m := v]))
}

predicate evalGlobalUpdate(s:state, g:symbol, offset:word, v:word, r:state)
    requires ValidState(s)
    requires ValidGlobalOffset(g, offset)
    ensures evalGlobalUpdate(s, g, offset, v, r) ==> ValidState(r) && GlobalWord(r.m, g, offset) == v
{
    reveal_ValidMemState();
    var oldval := s.m.globals[g];
    var newval := oldval[BytesToWords(offset) := v];
    assert |newval| == |oldval|;
    r == s.(m := s.m.(globals := s.m.globals[g := newval]))
}

function evalCmp(c:ocmp, i1:word, i2:word):bool
{
  match c
    case OEq => i1 == i2
    case ONe => i1 != i2
    case OLe => i1 <= i2
    case OGe => i1 >= i2
    case OLt => i1 <  i2
    case OGt => i1 >  i2
    case OTstEq => BitwiseAnd(i1, i2) == 0
    case OTstNe => BitwiseAnd(i1, i2) != 0
}

function evalOBool(s:state, o:obool):bool
    requires ValidState(s)
    requires ValidOperand(o.o1)
    requires ValidOperand(o.o2)
{
    evalCmp(o.cmp, OperandContents(s, o.o1), OperandContents(s, o.o2))
}

predicate evalGuard(s:state, o:obool, r:state)
    requires ValidState(s) && ValidOperand(o.o1) && ValidOperand(o.o2)
{
    // TODO: this is where we havoc the flags for the comparison, once we model them
    maybeHandleInterrupt(s, r)
}

predicate ValidModeChange'(s:state, m:mode)
{
    // See B9.1.2
    // Mode change into monitor is only allowed through an exception.
    // evalExceptionTaken does not require ValidModeChange
    priv_of_state(s) == PL1 && !(m == Monitor && world_of_state(s) != Secure)
}

predicate ValidModeChange(s:state, v:word)
{
    var enc := psr_mask_mode(v);
    ValidModeEncoding(enc) && ValidModeChange'(s, decode_mode(enc))
}

predicate ValidInstruction(s:state, ins:ins)
{
    ValidState(s) && match ins
        case ADD(dest, src1, src2) => ValidOperand(src1) &&
            ValidSecondOperand(src2) && ValidRegOperand(dest)
        case SUB(dest, src1, src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidRegOperand(dest)
        case MUL(dest,src1,src2) => ValidRegOperand(src1) &&
            ValidRegOperand(src2) && ValidRegOperand(dest)
        case UDIV(dest,src1,src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidRegOperand(dest) &&
            (OperandContents(s,src2) != 0)
        case AND(dest, src1, src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidRegOperand(dest)
        case ORR(dest, src1, src2) => ValidOperand(src1) &&
            ValidOperand(src2) && ValidRegOperand(dest)
        case EOR(dest, src1, src2) => ValidOperand(src1) &&
            ValidSecondOperand(src2) && ValidRegOperand(dest)
        case LSL(dest, src1, src2) => ValidOperand(src1) &&
            ValidShiftOperand(s, src2) && ValidRegOperand(dest)
        case LSR(dest, src1, src2) => ValidOperand(src1) &&
            ValidShiftOperand(s, src2) && ValidRegOperand(dest)
        case REV(dest, src) => ValidRegOperand(src) &&
            ValidRegOperand(dest)
        case MVN(dest, src) => ValidOperand(src) &&
            ValidRegOperand(dest)
        case LDR(rd, base, ofs) => 
            ValidRegOperand(rd) &&
            ValidOperand(base) && ValidOperand(ofs) &&
            WordAligned(OperandContents(s, base) + OperandContents(s, ofs)) &&
            ValidMem(OperandContents(s, base) + OperandContents(s, ofs))
        case LDR_global(rd, global, base, ofs) => 
            ValidRegOperand(rd) &&
            ValidOperand(base) && ValidOperand(ofs) &&
            ValidGlobalAddr(global, OperandContents(s, base) + OperandContents(s, ofs))
        case LDR_reloc(rd, global) => 
            ValidRegOperand(rd) && ValidGlobal(global)
        case STR(rd, base, ofs) =>
            ValidRegOperand(rd) &&
            ValidOperand(ofs) && ValidOperand(base) &&
            WordAligned(OperandContents(s, base) + OperandContents(s, ofs)) &&
            ValidMem(OperandContents(s, base) + OperandContents(s, ofs))
        case STR_global(rd, global, base, ofs) => 
            ValidRegOperand(rd) &&
            ValidOperand(base) && ValidOperand(ofs) &&
            ValidGlobalAddr(global, OperandContents(s, base) + OperandContents(s, ofs))
        case MOV(dst, src) => ValidRegOperand(dst) &&
            ValidSecondOperand(src)
        case MRS(dst, src) =>
            ValidRegOperand(dst) && ValidMrsMsrOperand(s,src)
        case MSR(dst, src) =>
            ValidRegOperand(src) && ValidMrsMsrOperand(s,dst)
            && (dst.OSReg? && dst.sr.spsr? ==> ValidPsrWord(OperandContents(s, src)))
            && (dst.OSReg? && dst.sr.cpsr? ==>
                ValidModeChange(s, OperandContents(s, src)))
        case MRC(dst, src) =>
            ValidMcrMrcOperand(s, src) &&
            ValidRegOperand(dst) 
        case MCR(dst, src) =>
            ValidMcrMrcOperand(s, dst) &&
            ValidRegOperand(src)
        case CPSID_IAF(mod) =>
            mod.OConst? && ValidModeEncoding(mod.n)
            && ValidModeChange'(s, decode_mode(mod.n))
        case MOVS_PCLR_TO_USERMODE_AND_CONTINUE =>
            ValidModeChange'(s, User) && spsr_of_state(s).m == User
}

function {:axiom} nondeterministic_word(s:state, x:int): word

predicate handleInterrupt(s:state, ex:exception, r:state)
    requires ValidState(s)
{
    exists s1, s2 :: evalExceptionTaken(s, ex, s1)
        && InterruptContinuationInvariant(s1, s2)
        && evalMOVSPCLR(s2, r)
}

predicate maybeHandleInterrupt(s:state, r:state)
    requires ValidState(s)
    ensures !interrupts_enabled(s) && maybeHandleInterrupt(s, r) ==> r == takestep(s)
{
    if !s.conf.cpsr.f && nondeterministic_word(s, -1) == 0
        then handleInterrupt(s, ExFIQ, r)
    else if !s.conf.cpsr.i && nondeterministic_word(s, -1) == 1
        then handleInterrupt(s, ExIRQ, r)
    else r == takestep(s)
}

predicate evalIns'(ins:ins, s:state, r:state)
{
    if !s.ok || !ValidInstruction(s, ins) then !r.ok
    else match ins
        case ADD(dst, src1, src2) => evalUpdate(s, dst,
            TruncateWord(OperandContents(s, src1) + OperandContents(s, src2)), r)
        case SUB(dst, src1, src2) => evalUpdate(s, dst,
            TruncateWord(OperandContents(s, src1) - OperandContents(s, src2)), r)
        case MUL(dst, src1, src2) => evalUpdate(s, dst,
            TruncateWord(OperandContents(s, src1) * OperandContents(s, src2)), r)
        case UDIV(dst, src1, src2) => evalUpdate(s, dst,
            TruncateWord(OperandContents(s, src1) / OperandContents(s, src2)), r)
        case AND(dst, src1, src2) => evalUpdate(s, dst,
            BitwiseAnd(OperandContents(s, src1), OperandContents(s, src2)), r)
        case ORR(dst, src1, src2) => evalUpdate(s, dst,
            BitwiseOr(OperandContents(s, src1), OperandContents(s, src2)), r)
        case EOR(dst, src1, src2) => evalUpdate(s, dst,
            BitwiseXor(OperandContents(s, src1), OperandContents(s, src2)), r)
        case LSL(dst, src1, src2) => if !(src2.OConst? && 0 <= src2.n <32) then !r.ok 
            else evalUpdate(s, dst,
                LeftShift(OperandContents(s, src1), OperandContents(s, src2)), r)
        case LSR(dst, src1, src2) => if !(src2.OConst? && 0 <= src2.n <32) then !r.ok
            else evalUpdate(s, dst,
                RightShift(OperandContents(s, src1), OperandContents(s, src2)), r)
        case REV(dst, src) => evalUpdate(s, dst, bswap32(OperandContents(s, src)), r)
        case MVN(dst, src) => evalUpdate(s, dst,
            BitwiseNot(OperandContents(s, src)), r)
        case LDR(rd, base, ofs) => 
            evalUpdate(s, rd, MemContents(s.m, OperandContents(s, base) +
                OperandContents(s, ofs)), r)
        case LDR_global(rd, global, base, ofs) => 
            evalUpdate(s, rd, GlobalWord(s.m, global, OperandContents(s, base)
                + OperandContents(s, ofs) - AddressOfGlobal(global)), r)
        case LDR_reloc(rd, name) =>
            evalUpdate(s, rd, AddressOfGlobal(name), r)
        case STR(rd, base, ofs) => 
            evalMemUpdate(s, OperandContents(s, base) +
                OperandContents(s, ofs), OperandContents(s, rd), r)
        case STR_global(rd, global, base, ofs) => 
            evalGlobalUpdate(s, global, OperandContents(s, base)
                + OperandContents(s, ofs) - AddressOfGlobal(global),
                OperandContents(s, rd), r)
        case MOV(dst, src) => evalUpdate(s, dst, OperandContents(s, src), r)
        case MRS(dst, src) => evalUpdate(s, dst, OperandContents(s, src), r)
        case MSR(dst, src) => evalUpdate(s, dst, OperandContents(s, src), r)
        case MRC(dst, src) => evalUpdate(s, dst, OperandContents(s, src), r)
        case MCR(dst, src) => evalUpdate(s, dst, OperandContents(s, src), r)
        case CPSID_IAF(mod) => evalCPSID_IAF(s, mod.n, r)
        case MOVS_PCLR_TO_USERMODE_AND_CONTINUE => evalMOVSPCLRUC(s, r)
}

/* FIXME: this spec allows at most one interrupt prior to instruction execution,
 * however, on real hardware we can take an unbounded number of interrupts if
 * the handler re-enables them... to fix this, we should either call evalIns
 * recursively, or require the handler to leave interrupts disabled.
 */
predicate evalIns(ins:ins, s:state, r:state)
{
    if !s.ok || !ValidInstruction(s, ins) then !r.ok
    else exists s' :: maybeHandleInterrupt(s, s') && evalIns'(ins, s', r)
}

predicate evalCPSID_IAF(s:state, mod:word, r:state)
    requires ValidState(s) && ValidModeEncoding(mod)
    ensures  evalCPSID_IAF(s, mod, r) ==> ValidState(r)
    //ensures  evalCPSID_IAF(s, mod, r) && s.ok ==> r.ok
{
    reveal_ValidSRegState();
    var newpsr := update_psr(s.sregs[cpsr], mod, true, true);
    ValidModeChange'(s, decode_mode(mod)) && ValidPsrWord(newpsr)
    && evalUpdate(s, OSReg(cpsr), newpsr, r)
}

predicate {:opaque} evalMOVSPCLRUC(s:state, r:state)
    requires ValidState(s)
    ensures evalMOVSPCLRUC(s, r) ==> ValidState(r)
{
    exists ex, s2, s3, s4 ::
        evalEnterUserspace(s, s2)
        && evalUserspaceExecution(s2, s3)
        && evalExceptionTaken(s3, ex, s4)
        && UsermodeContinuationInvariant(s4, r)
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
