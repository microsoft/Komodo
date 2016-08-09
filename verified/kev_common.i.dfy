include "ARMspartan.dfy"
include "kev_common.s.dfy"
include "pagedb.s.dfy"

//-----------------------------------------------------------------------------
// Stack/procedure invariants
//-----------------------------------------------------------------------------

predicate StackBytesRemaining(s:state,bytes:int)
{
    ValidState(s) && ValidStack(s) &&
    (StackLimit() + bytes < eval_op(s,op_sp()) <= StackBase())
}

predicate ParentStackPreserving(s:state, r:state)
    requires SaneState(s) && SaneState(r)
{
    var sp := eval_op(s,op_sp());
    forall i :: sp <= i < StackBase() && WordAligned(i) ==> addrval(r,i) == addrval(s,i)
}

predicate StackPreserving(s:state, r:state)
    requires SaneState(s) && SaneState(r)
{
    eval_op(s,op_sp()) == eval_op(r,op_sp())
    && ParentStackPreserving(s, r)
}

predicate DistinctRegOperands(operands:set<operand>, count:nat)
{
    |operands| == count && forall o :: o in operands ==> ValidRegOperand(o) && o != op_sp()
}

predicate RegPreservingExcept(s:state, r:state, trashed:set<operand>)
    requires ValidState(s) && ValidState(r);
    requires forall o :: o in trashed ==> ValidRegOperand(o);
{
    forall reg {:trigger OReg(reg)} :: OReg(reg) !in trashed && ValidRegOperand(OReg(reg))
        ==> eval_op(s,OReg(reg)) == eval_op(r,OReg(reg))
    && (op_sp() !in trashed ==> eval_op(s,op_sp()) == eval_op(r,op_sp()))
    && (op_lr() !in trashed ==> eval_op(s,op_lr()) == eval_op(r,op_lr()))
}

predicate NonvolatileRegPreserving(s:state, r:state)
    requires ValidState(s) && ValidState(r);
{
    RegPreservingExcept(s, r, {OReg(R0), OReg(R1), OReg(R2), OReg(R3)})
}

predicate MemPreservingExcept(s:state, r:state, base:int, limit:int)
    requires AlwaysInvariant(s,r);
    requires limit >= base;
{
    forall i :: ValidMem(s.m,i) && !(base <= i < limit) ==> addrval(s,i) == addrval(r,i)
}

predicate NonStackMemPreserving(s:state, r:state)
    requires AlwaysInvariant(s,r);
{
    MemPreservingExcept(s, r, StackLimit(), StackBase())
}


//-----------------------------------------------------------------------------
// Common functions
//-----------------------------------------------------------------------------

function page_paddr(p: PageNr) : int
    requires validPageNr(p)
    ensures isUInt32(page_paddr(p)) && PageAligned(page_paddr(p))
{
    assert PageAligned(KEVLAR_PAGE_SIZE());
    SecurePhysBase() + p * KEVLAR_PAGE_SIZE()
}

function page_monvaddr(pagenr:PageNr):int
    requires validPageNr(pagenr)
    ensures isUInt32(page_monvaddr(pagenr)) && PageAligned(page_monvaddr(pagenr))
{
    assert pagenr < KEVLAR_SECURE_NPAGES();
    var pa := page_paddr(pagenr);
    assert pa < SecurePhysBase() + KEVLAR_SECURE_RESERVE();
    page_paddr(pagenr) + KEVLAR_DIRECTMAP_VBASE()
}
