include "ARMspartan.dfy"
include "kom_common.s.dfy"
include "pagedb.s.dfy"

//-----------------------------------------------------------------------------
// Stack/procedure invariants
//-----------------------------------------------------------------------------

predicate StackBytesRemaining(s:state,bytes:int)
{
    ValidState(s) && ValidStack(s) &&
    (StackLimit() + bytes < OperandContents(s, OSP) <= StackBase())
}

predicate ParentStackPreserving(s:state, r:state)
    requires SaneState(s) && SaneState(r)
{
    forall m:addr :: OperandContents(s, OSP) <= m < StackBase()
        ==> MemContents(r.m, m) == MemContents(s.m, m)
}

predicate StackPreserving(s:state, r:state)
    requires SaneState(s) && SaneState(r)
{
    OperandContents(s, OSP) == OperandContents(r, OSP)
    && ParentStackPreserving(s, r)
}

predicate DistinctRegOperands(operands:set<operand>, count:nat)
{
    |operands| == count && forall o :: o in operands ==> ValidRegOperand(o) && o != OSP
}

predicate RegPreservingExcept(s:state, r:state, trashed:set<operand>)
    requires ValidState(s) && ValidState(r);
    requires forall o :: o in trashed ==> ValidRegOperand(o);
{
    forall reg {:trigger OReg(reg)} :: OReg(reg) !in trashed && ValidRegOperand(OReg(reg))
        ==> OperandContents(s, OReg(reg)) == OperandContents(r, OReg(reg))
    && (OSP !in trashed ==> OperandContents(s, OSP) == OperandContents(r, OSP))
    && (OLR !in trashed ==> OperandContents(s, OLR) == OperandContents(r, OLR))
    && SRegsInvariant(s, r)
}

predicate NonvolatileRegPreserving(s:state, r:state)
    requires ValidState(s) && ValidState(r);
{
    OperandContents(s, OReg(R4)) == OperandContents(r, OReg(R4))
    && OperandContents(s, OReg(R5)) == OperandContents(r, OReg(R5))
    && OperandContents(s, OReg(R6)) == OperandContents(r, OReg(R6))
    && OperandContents(s, OReg(R7)) == OperandContents(r, OReg(R7))
    && OperandContents(s, OReg(R8)) == OperandContents(r, OReg(R8))
    && OperandContents(s, OReg(R9)) == OperandContents(r, OReg(R9))
    && OperandContents(s, OReg(R10)) == OperandContents(r, OReg(R10))
    && OperandContents(s, OReg(R11)) == OperandContents(r, OReg(R11))
    && OperandContents(s, OReg(R12)) == OperandContents(r, OReg(R12))
    && OperandContents(s, OSP) == OperandContents(r, OSP)
    && OperandContents(s, OLR) == OperandContents(r, OLR)
}

predicate MemPreservingExcept(s:state, r:state, base:int, limit:int)
    requires ValidState(s) && ValidState(r);
    requires limit >= base;
{
    forall m:addr :: ValidMem(m) && !(base <= m < limit)
        ==> MemContents(s.m, m) == MemContents(r.m, m)
}

predicate NonStackMemPreserving(s:state, r:state)
    requires ValidState(s) && ValidState(r);
{
    MemPreservingExcept(s, r, StackLimit(), StackBase())
}


//-----------------------------------------------------------------------------
// Common functions
//-----------------------------------------------------------------------------

function page_paddr(p: PageNr): addr
    requires validPageNr(p)
    ensures PageAligned(page_paddr(p))
    ensures SecurePhysBase() <= page_paddr(p) < SecurePhysBase() + KOM_SECURE_RESERVE()
{
    assert PageAligned(PAGESIZE());
    SecurePhysBase() + p * PAGESIZE()
}

function page_monvaddr(p:PageNr): addr
    requires validPageNr(p)
    ensures PageAligned(page_monvaddr(p))
    ensures KOM_DIRECTMAP_VBASE() + SecurePhysBase() <= page_monvaddr(p)
            < KOM_DIRECTMAP_VBASE() + SecurePhysBase() + KOM_SECURE_RESERVE()
{
    assert p < KOM_SECURE_NPAGES();
    var pa := page_paddr(p);
    assert pa < SecurePhysBase() + KOM_SECURE_RESERVE();
    pa + KOM_DIRECTMAP_VBASE()
}

function monvaddr_page(mva:addr): PageNr
    requires PageAligned(mva)
    requires address_is_secure(mva)
    ensures validPageNr(monvaddr_page(mva))
    ensures page_monvaddr(monvaddr_page(mva)) == mva
{
    (mva - KOM_DIRECTMAP_VBASE() - SecurePhysBase()) / PAGESIZE()
}

// workarounds for Spartan's lack of Dafny language features
function specPageDb(t: (PageDb, int)): PageDb { t.0 }
function specErr(t: (PageDb, int)): int { t.1 }

// FIXME: delete
lemma WordAlignedAdd(x1:int,x2:int)
    requires WordAligned(x1) && WordAligned(x2)
    ensures  WordAligned(x1+x2)
    {}

lemma WordAlignedAdd_(x1:int,x2:int,y:int)
    requires WordAligned(x1) && WordAligned(x2) && y == x1+x2
    ensures WordAligned(y)
    {}
