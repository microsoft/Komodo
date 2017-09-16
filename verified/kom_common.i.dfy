include "ARMdef.s.dfy"
include "kom_common.s.dfy"
include "pagedb.s.dfy"

//-----------------------------------------------------------------------------
// Constants
//-----------------------------------------------------------------------------

const PAGEDB_ENTRY_SHIFT:int := 3;

//-----------------------------------------------------------------------------
// Useful invariants on architectural state
//-----------------------------------------------------------------------------
predicate AllMemInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.m == s'.m
}

predicate GlobalsInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.m.globals == s'.m.globals
}

predicate AddrMemInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.m.addresses == s'.m.addresses
}

predicate SRegsInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.sregs == s'.sregs && s.conf.(tlb_consistent := s'.conf.tlb_consistent) == s'.conf
}

predicate SpsrsInvariant(s:state, r:state)
    requires ValidState(s) && ValidState(r)
{
    reveal ValidSRegState();
    forall m | m != User :: s.sregs[spsr(m)] == r.sregs[spsr(m)]
}

predicate AllRegsInvariant(s:state, s':state)
    requires ValidState(s) && ValidState(s')
{
    s.regs == s'.regs && SRegsInvariant(s, s')
}

//-----------------------------------------------------------------------------
// Stack/procedure invariants
//-----------------------------------------------------------------------------

predicate StackPointerBytesRemaining(sp:word, bytes:int)
{
    SaneStackPointer(sp) && StackLimit() + bytes < sp <= StackBase()
}

predicate StackBytesRemaining(s:state,bytes:int)
{
    ValidState(s) && 
    (reveal ValidRegState();
    var sp := s.regs[SP(Monitor)];
    StackPointerBytesRemaining(sp, bytes))
}

predicate ParentStackPreserving(s:state, r:state)
    requires ValidState(s) && ValidState(r) && SaneConstants()
{
    reveal ValidRegState();
    var sp := s.regs[SP(Monitor)];
    SaneStack(s) &&
    forall a:addr | sp <= a < StackBase() :: MemContents(s.m, a) == MemContents(r.m, a)
}

predicate StackPreserving(s:state, r:state)
    requires ValidState(s) && ValidState(r) && SaneConstants()
{
    reveal ValidRegState();
    s.regs[SP(Monitor)] == r.regs[SP(Monitor)] && ParentStackPreserving(s, r)
}

predicate DistinctRegOperands(operands:set<operand>, count:nat)
{
    |operands| == count && forall o :: o in operands ==> ValidRegOperand(o) && o != OSP
}

predicate CoreRegPreservingExcept(s:state, r:state, trashed:set<operand>)
    requires ValidState(s) && ValidState(r);
    requires forall o :: o in trashed ==> ValidRegOperand(o);
{
    (forall reg {:trigger OReg(reg)} :: OReg(reg) !in trashed && ValidRegOperand(OReg(reg))
        ==> OperandContents(s, OReg(reg)) == OperandContents(r, OReg(reg)))
    && (OSP !in trashed ==> OperandContents(s, OSP) == OperandContents(r, OSP))
    && (OLR !in trashed ==> OperandContents(s, OLR) == OperandContents(r, OLR))
}

predicate RegPreservingExcept(s:state, r:state, trashed:set<operand>)
    requires ValidState(s) && ValidState(r);
    requires forall o :: o in trashed ==> ValidRegOperand(o);
{
    CoreRegPreservingExcept(s, r, trashed)
    && SRegsInvariant(s, r)
    && BankedRegsInvariant(s, r)
}

predicate GlobalsPreservingExcept(s:state, r:state, trashed:set<symbol>)
    requires ValidState(s) && ValidState(r);
    requires forall g :: g in trashed ==> ValidGlobal(g);
{
    reveal ValidMemState();
    forall glob | glob !in trashed && ValidGlobal(glob) ::
        s.m.globals[glob] == r.m.globals[glob]
}

predicate BankedRegsInvariant(s:state, r:state)
    requires ValidState(s) && ValidState(r)
{
    reveal ValidRegState();

    // LR and SP invariant for all modes other than the current one (i.e. monitor)
    forall m | m != mode_of_state(s) ::
        s.regs[LR(m)] == r.regs[LR(m)] && s.regs[SP(m)] == r.regs[SP(m)]
}

// typical procedure calls used in an SMC handler should preserve this
predicate SmcProcedureInvariant(s:state, r:state)
    requires SaneState(s) && SaneState(r);
{
    mode_of_state(r) == mode_of_state(s) // implied by SaneState
        && StackPreserving(s,r)
        && BankedRegsInvariant(s, r)
        && SRegsInvariant(s,r)
        && InsecureMemInvariant(s,r)
}

predicate EnterResumeSmcProcedureInvariant(s:state, r:state)
    requires SaneState(s) && SaneState(r)
{
    mode_of_state(r) == mode_of_state(s) // implied by SaneState
        && StackPreserving(s,r)
        && BankedRegsInvariant(s, r)
        && SpsrsInvariant(s, r)
        && r.conf.scr.ns == NotSecure
}

predicate MemPreservingExcept(s:state, r:state, base:int, limit:int)
    requires ValidState(s) && ValidState(r);
    requires limit >= base;
{
    forall m:addr :: ValidMemForRead(m) && !(base <= m < limit)
        ==> MemContents(s.m, m) == MemContents(r.m, m)
}

predicate NonStackMemPreserving(s:state, r:state)
    requires ValidState(s) && ValidState(r);
{
    MemPreservingExcept(s, r, StackLimit(), StackBase())
}

predicate OnlySecureMemInPageTable(s:state)
    requires ValidState(s)
{
    forall a:addr | AddrInPageTable(s, a) :: address_is_secure(a)
}

predicate ValidMemRangeExPageTable(s:state, base:int, limit:int)
    requires ValidState(s)
{
    ExtractAbsPageTable(s).Just? && ValidMemRange(base, limit)
    && forall a:addr | base <= a < limit :: !AddrInPageTable(s, a)
}

//-----------------------------------------------------------------------------
// Common functions
//-----------------------------------------------------------------------------

function monvaddr_page(mva:addr): PageNr
    requires PageAligned(mva)
    requires address_is_secure(mva)
    ensures validPageNr(monvaddr_page(mva))
    //ensures page_monvaddr(monvaddr_page(mva)) == mva
{
    (mva - KOM_DIRECTMAP_VBASE - SecurePhysBase()) / PAGESIZE
}

function paddr_page(p:addr): PageNr
    requires PageAligned(p)
    requires SecurePhysBase() <= p < SecurePhysBase() + KOM_SECURE_RESERVE
    ensures validPageNr(paddr_page(p))
    ensures page_paddr(paddr_page(p)) == p
{
    (p - SecurePhysBase()) / PAGESIZE
}

// workarounds for Spartan's lack of Dafny language features
function specPageDb(t: (PageDb, int)): PageDb { t.0 }
function specErr(t: (PageDb, int)): int { t.1 }

function firstOf2<T,U>(t:(T, U)) : T { t.0 }
function secondOf2<T,U>(t:(T, U)) : U { t.1 }

//-----------------------------------------------------------------------------
// Common lemmas
//-----------------------------------------------------------------------------

lemma lemma_WordAlignedAdd(x1:int, x2:int)
    requires WordAligned(x1) && WordAligned(x2) 
    ensures WordAligned(x1+x2)
{ reveal WordAligned(); }

lemma lemma_WordAlignedSub(x1:int, x2:int)
    requires WordAligned(x1) && WordAligned(x2) && x1 >= x2
    ensures WordAligned(x1 - x2)
{ reveal WordAligned(); }

lemma lemma_AddrInPageTable_persists1(s1:state, s2:state, a:addr)
    requires ValidState(s1) && ValidState(s2) && ValidMem(a)
    requires !AddrInPageTable(s1, a)
    requires s1.conf.ttbr0 == s2.conf.ttbr0
    requires s2.m.addresses == (reveal_ValidMemState(); s1.m.addresses[a := s2.m.addresses[a]])
    ensures !AddrInPageTable(s2, a)
{
    var vbase := s1.conf.ttbr0.ptbase + PhysBase();
    forall i | 0 <= i < ARM_L1PTES
        ensures MemContents(s1.m, WordOffset(vbase, i)) == MemContents(s2.m, WordOffset(vbase, i))
    {
        assert !(vbase <= a < vbase + ARM_L1PTABLE_BYTES);
    }
}

lemma lemma_AddrInPageTable_persists(s1:state, s2:state, base:addr, limit:addr)
    requires ValidState(s1) && ValidState(s2) && limit >= base
    requires ValidMemRangeExPageTable(s1, base, limit)
    requires s1.conf.ttbr0 == s2.conf.ttbr0
    requires MemPreservingExcept(s1, s2, base, limit)
    ensures ValidMemRangeExPageTable(s2, base, limit)
{
    var vbase := WordAlignedAdd(s1.conf.ttbr0.ptbase, PhysBase());
    assert ValidAbsL1PTable(s1.m, vbase);

    forall a:addr | base <= a < limit
        ensures !(vbase <= a < vbase + ARM_L1PTABLE_BYTES)
        ensures !AddrInL2PageTable(s1.m, vbase, a)
    {
        assert !AddrInPageTable(s1, a);
    }

    forall i, ptew | 0 <= i < ARM_L1PTES && ptew == MemContents(s1.m, WordOffset(vbase, i))
        ensures ptew == MemContents(s2.m, WordOffset(vbase, i))
        ensures ExtractAbsL1PTE(ptew).Just? ==> ValidAbsL2PTable(s2.m, ExtractAbsL1PTE(ptew).v + PhysBase())
    {
        assert vbase <= WordOffset(vbase, i) < vbase + ARM_L1PTABLE_BYTES;

        if ExtractAbsL1PTE(ptew).Just? {
            var vbase2 := ExtractAbsL1PTE(ptew).v + PhysBase();
            forall i2 | 0 <= i2 < ARM_L2PTES
                ensures ValidAbsL2PTEWord(MemContents(s2.m, WordOffset(vbase2, i2)))
            {
                assert ValidAbsL2PTEWord(MemContents(s1.m, WordOffset(vbase2, i2)));
                assert MemContents(s1.m, WordOffset(vbase2, i2)) == MemContents(s2.m, WordOffset(vbase2, i2));
            }
        }
    }

    assert ExtractAbsPageTable(s2).Just?;
}
