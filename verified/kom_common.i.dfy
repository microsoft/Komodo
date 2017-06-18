include "ARMdef.dfy"
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
    s.sregs == s'.sregs && s.conf == s'.conf
}

predicate SpsrsInvariant(s:state, r:state)
    requires ValidState(s) && ValidState(r)
{
    reveal_ValidSRegState();
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

predicate StackBytesRemaining(s:state,bytes:int)
{
    ValidState(s) && SaneStack(s) &&
    (reveal_ValidRegState();
    var sp := s.regs[SP(Monitor)];
    StackLimit() + bytes < sp <= StackBase())
}

predicate ParentStackPreserving(s:state, r:state)
    requires ValidState(s) && ValidState(r) && SaneConstants()
{
    reveal_ValidRegState();
    var sp := s.regs[SP(Monitor)];
    SaneStack(s) &&
    forall a:addr | sp <= a < StackBase() :: MemContents(s.m, a) == MemContents(r.m, a)
}

predicate StackPreserving(s:state, r:state)
    requires ValidState(s) && ValidState(r) && SaneConstants()
{
    reveal_ValidRegState();
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
    reveal_ValidMemState();
    forall glob | glob !in trashed && ValidGlobal(glob) ::
        s.m.globals[glob] == r.m.globals[glob]
}

predicate BankedRegsInvariant(s:state, r:state)
    requires ValidState(s) && ValidState(r)
{
    reveal_ValidRegState();

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
