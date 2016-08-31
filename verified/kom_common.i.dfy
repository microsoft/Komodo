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
    RegPreservingExcept(s, r, {OReg(R0), OReg(R1), OReg(R2), OReg(R3)})
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
{
    assert PageAligned(PAGESIZE());
    SecurePhysBase() + p * PAGESIZE()
}

function page_monvaddr(pagenr:PageNr): addr
    requires validPageNr(pagenr)
    ensures PageAligned(page_monvaddr(pagenr))
{
    assert pagenr < KOM_SECURE_NPAGES();
    var pa := page_paddr(pagenr);
    assert pa < SecurePhysBase() + KOM_SECURE_RESERVE();
    page_paddr(pagenr) + KOM_DIRECTMAP_VBASE()
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
