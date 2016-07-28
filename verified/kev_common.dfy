include "ARMspartan.dfy"
include "kev_constants.dfy"
include "pagedb.dfy"

//-----------------------------------------------------------------------------
// Globals
//-----------------------------------------------------------------------------

function method {:opaque} PageDb(): operand { op_sym("g_pagedb") }
function method {:opaque} SecurePhysBaseOp(): operand { op_sym("g_secure_physbase") }

// the phys base is unknown, but never changes
function {:axiom} SecurePhysBase(): int
    ensures 0 < SecurePhysBase() <= KEVLAR_PHYSMEM_LIMIT() - KEVLAR_SECURE_RESERVE();
    ensures WordAligned(SecurePhysBase());

function method KevGlobalDecls(): globaldecls
    ensures ValidGlobalDecls(KevGlobalDecls());
{
    reveal_PageDb(); reveal_SecurePhysBaseOp();
    GlobalDecls(map[SecurePhysBaseOp() := 4, //BytesPerWord()
                    PageDb() := G_PAGEDB_SIZE()])
}


//-----------------------------------------------------------------------------
// Stack
//-----------------------------------------------------------------------------

// we don't know where the stack is exactly, but we know how big it is
function {:axiom} StackLimit():int
    ensures WordAligned(StackLimit())
    ensures KEVLAR_MON_VBASE() <= StackLimit()
    ensures StackLimit() <= KEVLAR_DIRECTMAP_VBASE() - KEVLAR_STACK_SIZE()

function StackBase():int
{
    StackLimit() + KEVLAR_STACK_SIZE()
}

predicate ValidStack(s:state)
    requires ValidState(s)
{
    WordAligned(eval_op(s, op_sp()))
    && StackLimit() < eval_op(s, op_sp()) <= StackBase()
}

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


//-----------------------------------------------------------------------------
// Procedure invariants
//-----------------------------------------------------------------------------

predicate RegPreservingExcept(s:state, r:state, trashed:seq<operand>)
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
    RegPreservingExcept(s, r, [OReg(R0), OReg(R1), OReg(R2), OReg(R3)])
}

predicate MemPreservingExcept(s:state, r:state, base:int, limit:int)
    requires AlwaysInvariant(s,r);
    requires limit >= base;
{
    forall i :: ValidMem(s.m,i) && (i < base || i >= limit) ==> addrval(s,i) == addrval(r,i)
}

predicate NonStackMemPreserving(s:state, r:state)
    requires AlwaysInvariant(s,r);
{
    MemPreservingExcept(s, r, StackLimit(), StackBase())
}


//-----------------------------------------------------------------------------
// Application-level state invariants
//-----------------------------------------------------------------------------

predicate SaneMem(s:memstate)
{
    ValidMemState(s)
    // TODO: our insecure phys mapping must be valid
    //&& ValidMemRange(s, KEVLAR_DIRECTMAP_VBASE(),
    //    (KEVLAR_DIRECTMAP_VBASE() + MonitorPhysBaseValue()))
    // our secure phys mapping must be valid
    && ValidMemRange(s, KEVLAR_DIRECTMAP_VBASE() + SecurePhysBase(),
        (KEVLAR_DIRECTMAP_VBASE() + SecurePhysBase() + KEVLAR_SECURE_RESERVE()))
    // the stack must be mapped
    && ValidMemRange(s, StackLimit(), StackBase())
    // globals are as we expect
    && KevGlobalDecls() == TheGlobalDecls()
    && GlobalFullContents(s, SecurePhysBaseOp()) == [SecurePhysBase()]
    // XXX: workaround so dafny sees that these are distinct
    && SecurePhysBaseOp() != PageDb()
}

predicate SaneState(s:state)
{
    ValidState(s) && ValidStack(s) && SaneMem(s.m) && mode_of_state(s) == Monitor
}


//-----------------------------------------------------------------------------
// Common functions
//-----------------------------------------------------------------------------

function page_paddr(p: PageNr) : int
    requires validPageNr(p)
    ensures WordAligned(page_paddr(p))
{
    assert WordAligned(KEVLAR_PAGE_SIZE());
    SecurePhysBase() + p * KEVLAR_PAGE_SIZE()
}

function page_monvaddr(pagenr:PageNr):int
    requires validPageNr(pagenr)
    ensures WordAligned(page_monvaddr(pagenr))
{
    page_paddr(pagenr) + KEVLAR_DIRECTMAP_VBASE()
}
