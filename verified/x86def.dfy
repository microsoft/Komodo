include "assembly.s.dfy"

datatype x86reg = X86Eax | X86Ebx | X86Ecx | X86Edx | X86Esi | X86Edi | X86Ebp | X86Eflags | X86Xmm(xmm:int)
datatype x86type = X86Uint8 | X86Uint16 | X86Uint32 | X86Uint64 | X86Uint128
datatype id = IdGlobal(g:int) | IdLocal(x:int)| IdStackSlot(s:int) | IdX86Reg(r:x86reg)
datatype oexp = OEVar(x:id) | OEAdd(e1:oexp, e2:oexp) | OEScale(i:int, e:oexp)
datatype oprnd = OConst(n:int) | OVar(x:id) | OHeap(addr:int, t:x86type)
datatype ocmp = OEq | ONe | OLe | OGe | OLt | OGt
datatype obool = OCmp(cmp:ocmp, o1:oprnd, o2:oprnd)

function method id_eax():id { IdX86Reg(X86Eax) }
function method var_eax():oprnd { OVar(id_eax()) }
function method id_ebx():id { IdX86Reg(X86Ebx) }
function method var_ebx():oprnd { OVar(id_ebx()) }
function method id_ecx():id { IdX86Reg(X86Ecx) }
function method var_ecx():oprnd { OVar(id_ecx()) }
function method id_edx():id { IdX86Reg(X86Edx) }
function method var_edx():oprnd { OVar(id_edx()) }
function method id_edi():id { IdX86Reg(X86Edi) }
function method var_edi():oprnd { OVar(id_edi()) }
function method id_esi():id { IdX86Reg(X86Esi) }
function method var_esi():oprnd { OVar(id_esi()) }
function method id_ebp():id { IdX86Reg(X86Ebp) }
function method var_ebp():oprnd { OVar(id_ebp()) }

datatype ins =
  Rand(xRand:oprnd)
| Mov32(dstMov:oprnd, srcMov:oprnd)
| Add32(dstAdd:oprnd, srcAdd:oprnd)
| Sub32(dstSub:oprnd, srcSub:oprnd)
| Mul32(srcMul:oprnd)
| AddCarry(dstAddCarry:oprnd, srcAddCarry:oprnd)
| Xor32(dstXor:oprnd, srcXor:oprnd)
| And32(dstAnd:oprnd, srcAnd:oprnd)
| Not32(dstNot:oprnd)
| GetCf(dstCf:oprnd) // corresponds to SETC instruction
| Rol32(dstRolConst:oprnd, amountRolConst:oprnd)
| Ror32(dstRorConst:oprnd, amountRorConst:oprnd)
| Shl32(dstShlConst:oprnd, amountShlConst:oprnd)
| Shr32(dstShrConst:oprnd, amountShrConst:oprnd)

datatype codes = CNil | sp_CCons(hd:code, tl:codes)

datatype code =
  Ins(ins:ins)
| Block(block:codes)
| IfElse(ifCond:obool, ifTrue:code, ifFalse:code)
| While(whileCond:obool, whileBody:code)

datatype frame = Frame(decls:map<id, x86type>, locals:map<id, int>)
datatype state = State(decls:map<id, x86type>, globals:map<id, int>, stack:seq<frame>, heap:map<int, int>)

function GetNumBytesForX86Type(t:x86type) : int
{
    match t
        case X86Uint8 =>   1
        case X86Uint16 =>  2
        case X86Uint32 =>  4
        case X86Uint64 =>  8
        case X86Uint128 => 16
}

function GetValueLimitForX86Type(t:x86type) : int
{
    match t
        case X86Uint8 =>   0x1_00
        case X86Uint16 =>  0x1_0000
        case X86Uint32 =>  0x1_0000_0000
        case X86Uint64 =>  0x1_0000_0000_0000_0000
        case X86Uint128 => 0x1_0000_0000_0000_0000_0000_0000_0000_0000
}

// Note: Explicitly expand the mod amounts (rather than call GetValueLimitForX86Type)
//       so that mod by a constant is clear
function TruncateToX86Type(n:int, t:x86type) : int
{
    match t
        case X86Uint8 =>   n % 0x1_00
        case X86Uint16 =>  n % 0x1_0000
        case X86Uint32 =>  n % 0x1_0000_0000
        case X86Uint64 =>  n % 0x1_0000_0000_0000_0000
        case X86Uint128 => n % 0x1_0000_0000_0000_0000_0000_0000_0000_0000
}

function GetRegisterType(r:x86reg) : x86type
{
    if r.X86Xmm? then X86Uint128 else X86Uint32
}

predicate Is32bitId(s:state, i:id)
{
    match i
        case IdGlobal(g) => i in s.decls && s.decls[i].X86Uint32?
        case IdLocal(x) => |s.stack| > 0 && i in s.stack[0].decls && s.stack[0].decls[i].X86Uint32?
        case IdStackSlot(n) => true
        case IdX86Reg(r) => GetRegisterType(r).X86Uint32?
}

predicate Is32bitExp(s:state, exp:oexp)
{
    match exp
        case OEVar(x) => Is32bitId(s, x)
        case OEAdd(e1, e2) => Is32bitExp(s, e1) && Is32bitExp(s, e2)
        case OEScale(i, e) => 0 <= i < 0x1_0000_0000 && Is32bitExp(s, e)
}

predicate Is32bitOprnd(s:state, o:oprnd)
{
  match o
    case OConst(n) => 0 <= n < 0x1_0000_0000 
    case OVar(v) => Is32bitId(s, v)
    case OHeap(addr, t) => t.X86Uint32?
}

predicate ValidState(s:state)
{
    (forall r :: IdX86Reg(r) in s.globals)
}

predicate ValidHeapAddr(heap:map<int,int>, addr:int, t:x86type)
{
    addr % GetValueLimitForX86Type(t) == 0
 && (forall i {:trigger addr + i in heap} :: 0 <= i < GetNumBytesForX86Type(t) ==> addr + i in heap)
}

predicate ValidOperand(s:state, o:oprnd)
{
    match o
      case OVar(x) =>
        (match x
           case IdGlobal(g) => x in s.decls && x in s.globals
           case IdLocal(l) => |s.stack| > 0 && x in s.stack[0].decls && x in s.stack[0].locals
           case IdStackSlot(n) => |s.stack| > 0 && x in s.stack[0].locals
           case IdX86Reg(r) => !r.X86Eflags? && x in s.globals)
      case OConst(n) => true
      case OHeap(addr, t) => ValidHeapAddr(s.heap, addr, t)
}

function {:axiom} GetValueAtHeapAddress(heap:map<int,int>, addr:int, t:x86type) : int
    requires ValidHeapAddr(heap, addr, t);
    ensures  0 <= GetValueAtHeapAddress(heap, addr, t) < GetValueLimitForX86Type(t);
    ensures  addr in heap && GetValueAtHeapAddress(heap, addr, t) == heap[addr];

predicate Valid32BitOperand(s:state, o:oprnd)
{
       ValidOperand(s, o)
    && Is32bitOprnd(s, o)
}

predicate ValidShiftAmountOperand(s:state, o:oprnd)
{
       (   o.OConst?
        && 0 <= o.n < 32)
    || (   o == OVar(IdX86Reg(X86Ecx))
        && o.x in s.decls
        && o.x in s.globals)
}

predicate ValidDestinationOperand(s:state, o:oprnd)
{
       o.OVar?
    && ValidOperand(s, o)
}

predicate Valid32BitDestinationOperand(s:state, o:oprnd)
{
       ValidDestinationOperand(s, o)
    && Is32bitOprnd(s, o)
}

function OperandContents(s:state, o:oprnd):int
    requires ValidOperand(s, o);
{
    match o
        case OConst(n) => n
        case OVar(x) =>
            (match x
                 case IdGlobal(g) => s.globals[x]
                 case IdLocal(l) => s.stack[0].locals[x]
                 case IdStackSlot(n) => s.stack[0].locals[x]
                 case IdX86Reg(r) => s.globals[x]
            )
        case OHeap(addr, t) => GetValueAtHeapAddress(s.heap, addr, t)
}

function eval_op(s:state, o:oprnd):int
{
    if !ValidOperand(s, o) then
        42
    else
        match o
            case OConst(n) => n
            case OVar(x) =>
                (match x
                     case IdGlobal(g) => TruncateToX86Type(s.globals[x], s.decls[x])
                     case IdLocal(l) => TruncateToX86Type(s.stack[0].locals[x], s.stack[0].decls[x])
                     case IdStackSlot(n) => TruncateToX86Type(s.stack[0].locals[x], X86Uint32())
                     case IdX86Reg(r) => TruncateToX86Type(s.globals[x], GetRegisterType(r))
                )
            case OHeap(addr, t) => GetValueAtHeapAddress(s.heap, addr, t)
}

predicate evalUpdateAndMaintainFlags(s:state, o:oprnd, v:int, r:state, ok:bool)
    requires ValidDestinationOperand(s, o);
{
    if o.x.IdGlobal? || o.x.IdX86Reg? then
        ok && r == s.(globals := s.globals[o.x := v])
    else
        ok && r == s.(stack := [s.stack[0].(locals := s.stack[0].locals[o.x := v])] + s.stack[1..])
}

predicate evalUpdateAndHavocFlags(s:state, o:oprnd, v:int, r:state, ok:bool)
    requires ValidDestinationOperand(s, o);
{
    if o.x.IdGlobal? || o.x.IdX86Reg? then
           ok
        && IdX86Reg(X86Eflags) in r.globals
        && r == s.(globals := s.globals[o.x := v][IdX86Reg(X86Eflags) := r.globals[IdX86Reg(X86Eflags)]])
    else
           ok
        && IdX86Reg(X86Eflags) in r.globals
        && r == s.(stack := [s.stack[0].(locals := s.stack[0].locals[o.x := v])] + s.stack[1..],
                      globals := s.globals[IdX86Reg(X86Eflags) := r.globals[IdX86Reg(X86Eflags)]])
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

function clear_low_byte(n:int) : int
{
    (n / 256) * 256
}

function flags(s:state) : int
{
    if IdX86Reg(X86Eflags) in s.globals then s.globals[IdX86Reg(X86Eflags)] else 13
}

function xor32(x:int, y:int) : int  
    requires 0 <= x < 0x1_0000_0000 && 0 <= y < 0x1_0000_0000;
    { int(BitwiseXor(uint32(x), uint32(y))) }

function and32(x:int, y:int) : int  
    requires 0 <= x < 0x1_0000_0000 && 0 <= y < 0x1_0000_0000;
    { int(BitwiseAnd(uint32(x), uint32(y))) }

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

// Is the carry flag (CF) set?
predicate{:axiom} Cf(flags:int)

// Temporary workaround for the old version of Dafny that's currently checked in                                            
predicate{:axiom} Flags(flags:int)

predicate ValidInstruction(s:state, ins:ins)
{
    match ins
        case Rand(xRand) => Valid32BitDestinationOperand(s, xRand)
        case Mov32(dstMov, srcMov) => Valid32BitDestinationOperand(s, dstMov) && Valid32BitOperand(s, srcMov)
        case Add32(dstAdd, srcAdd) => Valid32BitDestinationOperand(s, dstAdd) && Valid32BitOperand(s, srcAdd)
        case Sub32(dstSub, srcSub) => Valid32BitDestinationOperand(s, dstSub) && Valid32BitOperand(s, srcSub)
        case Mul32(srcMul) => Valid32BitOperand(s, srcMul) && Valid32BitDestinationOperand(s, OVar(IdX86Reg(X86Eax))) && Valid32BitDestinationOperand(s, OVar(IdX86Reg(X86Edx)))
        case AddCarry(dstAddCarry, srcAddCarry) => Valid32BitDestinationOperand(s, dstAddCarry) && Valid32BitOperand(s, srcAddCarry)
        case Xor32(dstXor, srcXor) => Valid32BitDestinationOperand(s, dstXor) && Valid32BitOperand(s, srcXor)
        case And32(dstAnd, srcAnd) => Valid32BitDestinationOperand(s, dstAnd) && Valid32BitOperand(s, srcAnd)
        case Not32(dstNot) => Valid32BitDestinationOperand(s, dstNot)
        case GetCf(dstCf) => Valid32BitDestinationOperand(s, dstCf)
        case Rol32(dstRolConst, amountRol) => Valid32BitDestinationOperand(s, dstRolConst) && ValidShiftAmountOperand(s, amountRol)
        case Ror32(dstRorConst, amountRor) => Valid32BitDestinationOperand(s, dstRorConst) && ValidShiftAmountOperand(s, amountRor)
        case Shl32(dstShlConst, amountShl) => Valid32BitDestinationOperand(s, dstShlConst) && ValidShiftAmountOperand(s, amountShl)
        case Shr32(dstShrConst, amountShr) => Valid32BitDestinationOperand(s, dstShrConst) && ValidShiftAmountOperand(s, amountShr)
}

predicate evalIns(ins:ins, s:state, r:state, ok:bool)
{
    if !ValidInstruction(s, ins) then
        !ok
    else
        match ins
            case Rand(x) => exists n :: 0 <= n < GetValueLimitForX86Type(X86Uint32) && evalUpdateAndHavocFlags(s, x, n, r, ok)
            case Mov32(dst, src) =>    0 <= OperandContents(s, src) < GetValueLimitForX86Type(X86Uint32)
                                    && evalUpdateAndMaintainFlags(s, dst, OperandContents(s, src), r, ok) // mov doesn't change flags
            case Add32(dst, src) => evalUpdateAndHavocFlags(s, dst, (OperandContents(s, dst) + OperandContents(s, src)) % 0x1_0000_0000, r, ok)
            case Sub32(dst, src) => evalUpdateAndHavocFlags(s, dst, (OperandContents(s, dst) - OperandContents(s, src)) % 0x1_0000_0000, r, ok)
            case Mul32(src)      => var product := s.globals[IdX86Reg(X86Eax)] * OperandContents(s, src);
                                    var hi := product / 0x1_0000_0000;
                                    var lo := product % 0x1_0000_0000;
                                       ok
                                    && IdX86Reg(X86Eflags) in r.globals
                                    && r == s.(globals := s.globals[IdX86Reg(X86Edx) := hi]
                                                                   [IdX86Reg(X86Eax) := lo]
                                                                   [IdX86Reg(X86Eflags) := r.globals[IdX86Reg(X86Eflags)]])
            // Add with carry (ADC) instruction
            case AddCarry(dst, src) => var old_carry := if Cf(flags(s)) then 1 else 0;
                                       var sum := OperandContents(s, dst) + OperandContents(s, src) + old_carry;
                                       evalUpdateAndHavocFlags(s, dst, sum % 0x1_0000_0000, r, ok)
                                    && Cf(r.globals[IdX86Reg(X86Eflags)]) == (sum >= 0x1_0000_0000)
            case Xor32(dst, src) => evalUpdateAndHavocFlags(s, dst, xor32(eval_op(s, dst), eval_op(s, src)), r, ok)
            case And32(dst, src) => evalUpdateAndHavocFlags(s, dst, and32(eval_op(s, dst), eval_op(s, src)), r, ok)
            case Not32(dst)      => evalUpdateAndHavocFlags(s, dst, not32(eval_op(s, dst)), r, ok)
            // Sticks the carry flag (CF) in a register (see SETC instruction)
            case GetCf(dst)      => // Instruction only writes the first byte
                                    evalUpdateAndMaintainFlags(s, dst, clear_low_byte(OperandContents(s, dst)) + if Cf(flags(s)) then 1 else 0, r, ok)
            case Rol32(dst, amount)  =>
                var n := if amount.OConst? then amount.n else s.globals[IdX86Reg(X86Ecx)];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, rol32(eval_op(s, dst), n), r, ok) else !ok

            case Ror32(dst, amount) =>
                var n := if amount.OConst? then amount.n else s.globals[IdX86Reg(X86Ecx)];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, ror32(eval_op(s, dst), n), r, ok) else !ok

            case Shl32(dst, amount)  =>
                var n := if amount.OConst? then amount.n else s.globals[IdX86Reg(X86Ecx)];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, shl32(eval_op(s, dst), n), r, ok) else !ok

            case Shr32(dst, amount) =>
                var n := if amount.OConst? then amount.n else s.globals[IdX86Reg(X86Ecx)];
                if 0 <= n < 32 then evalUpdateAndHavocFlags(s, dst, shr32(eval_op(s, dst), n), r, ok) else !ok
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

// evaluation (zero or more steps) may succeed and change s to r where ok == true
// evaluation (zero or more steps) may fail where ok == false
predicate{:opaque} sp_eval(c:code, s:state, r:state, ok:bool) { evalCode(c, s, r, ok) }


