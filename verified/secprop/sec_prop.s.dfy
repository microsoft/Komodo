include "../smcapi.s.dfy"
include "../pagedb.s.dfy"

predicate valDispPage(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
{
    d[n].PageDbEntryTyped? && d[n].entry.Dispatcher?
}

predicate valAddrPage(d: PageDb, n: PageNr)
    requires wellFormedPageDb(d)
{
    d[n].PageDbEntryTyped? && d[n].entry.Addrspace?
}

predicate pgInAddrSpc(d: PageDb, n: PageNr, a: PageNr)
    requires wellFormedPageDb(d) && valAddrPage(d, a)
{
    d[n].PageDbEntryTyped? && d[n].addrspace == a
}

predicate usr_regs_equiv(s1:state, s2:state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal ValidRegState();
    reveal ValidSRegState();
    s1.regs[R0]  == s2.regs[R0] &&
    s1.regs[R1]  == s2.regs[R1] &&
    s1.regs[R2]  == s2.regs[R2] &&
    s1.regs[R3]  == s2.regs[R3] &&
    s1.regs[R4]  == s2.regs[R4] &&
    s1.regs[R5]  == s2.regs[R5] &&
    s1.regs[R6]  == s2.regs[R6] &&
    s1.regs[R7]  == s2.regs[R7] &&
    s1.regs[R8]  == s2.regs[R8] &&
    s1.regs[R9]  == s2.regs[R9] &&
    s1.regs[R10] == s2.regs[R10] &&
    s1.regs[R11] == s2.regs[R11] &&
    s1.regs[R12] == s2.regs[R12] &&
    s1.regs[SP(User)] == s2.regs[SP(User)] &&
    s1.regs[LR(User)] == s2.regs[LR(User)]
}
//-----------------------------------------------------------------------------
// Low Equivalence for Confidentiality
//-----------------------------------------------------------------------------
// These relations specify the observational power of an adversary comprising a 
// malicious or compromised operating system colluding with an enclave. This 
// low-equivalence relation is used to prove that the confidentiality of 
// enclaves is protected against this attacker

// Relates concrete (state) and abstract (PageDb) pairs that appear the same 
// to the attacker
predicate conf_loweq(s1: state, d1: PageDb, s2: state, d2: PageDb, atkr: PageNr)
    requires ValidState(s1) && ValidState(s2)
    requires validPageDb(d1) && validPageDb(d2)
{
    reveal ValidMemState();
    os_regs_equiv(s1, s2) &&
    os_ctrl_eq(s1, s2) &&
    InsecureMemInvariant(s1, s2) &&
    loweq_pdb(d1, d2, atkr)
}

// Relates two PageDbs that appear the same to an observer enclave
// For the proof of confidentiality, the observer is an attacker.
// For the proof of integrity, the observer is a would-be victim.
predicate {:opaque} loweq_pdb(d1: PageDb, d2: PageDb, obs: PageNr)
    requires wellFormedPageDb(d1) && wellFormedPageDb(d2)
{
    valAddrPage(d1, obs) && valAddrPage(d2, obs) &&
    !stoppedAddrspace(d1[obs]) && !stoppedAddrspace(d2[obs]) &&
    (forall n: PageNr ::
        d1[n].PageDbEntryTyped? <==> d2[n].PageDbEntryTyped?) &&
    (forall n: PageNr :: pgInAddrSpc(d1, n, obs) <==>
        pgInAddrSpc(d2, n, obs)) &&
    (forall n : PageNr | d1[n].PageDbEntryTyped? ::
        d1[n].addrspace == d2[n].addrspace &&
        (if(pgInAddrSpc(d1, n, obs))
            then d1[n].entry == d2[n].entry
            else loweq_entry(d1[n].entry, d2[n].entry)))
}


// This relates two PageDbEntryTypeds that are in the same enclave address
// space and appear the same to an observer that controls a different enclave
// address space.
predicate loweq_entry(e1:PageDbEntryTyped, e2:PageDbEntryTyped)
{
    match e1
        case Addrspace(_,_,_,_,_)
            => e2.Addrspace? && e1.(shatrace := e2.shatrace,
                measurement := e2.measurement, refcount := e2.refcount ) == e2 
        case Dispatcher(_,_,_,_,_) => e2.Dispatcher? &&
            e2.entered == e1.entered && e2.entrypoint == e1.entrypoint
        case L1PTable(_) => e1 == e2
        case L2PTable(_) => e1 == e2
        case DataPage(_) => e2.DataPage?
        case SparePage   => e2.SparePage?
}


predicate os_ctrl_eq(s1: state, s2: state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal ValidSRegState();
    forall m | m in {Supervisor, Abort, Undefined} ::
        s1.sregs[spsr(m)] == s2.sregs[spsr(m)]

}

predicate os_regs_equiv(s1: state, s2: state)
    requires ValidState(s1) && ValidState(s2)
{
   reveal ValidRegState();
   reveal ValidSRegState();
   s1.regs[R0]  == s2.regs[R0] &&
   s1.regs[R1]  == s2.regs[R1] &&
   s1.regs[R2]  == s2.regs[R2] &&
   s1.regs[R3]  == s2.regs[R3] &&
   s1.regs[R4]  == s2.regs[R4] &&
   s1.regs[R5]  == s2.regs[R5] &&
   s1.regs[R6]  == s2.regs[R6] &&
   s1.regs[R7]  == s2.regs[R7] &&
   s1.regs[R8]  == s2.regs[R8] &&
   s1.regs[R9]  == s2.regs[R9] &&
   s1.regs[R10] == s2.regs[R10] &&
   s1.regs[R11] == s2.regs[R11] &&
   s1.regs[R12] == s2.regs[R12] &&
   s1.regs[LR(User)]       == s2.regs[LR(User)] &&
   // s1.regs[LR(FIQ)]        == s2.regs[LR(FIQ)] &&
   // s1.regs[LR(IRQ)]        == s2.regs[LR(IRQ)] &&
   s1.regs[LR(Supervisor)] == s2.regs[LR(Supervisor)] &&
   s1.regs[LR(Abort)]      == s2.regs[LR(Abort)] &&
   s1.regs[LR(Undefined)]  == s2.regs[LR(Undefined)] &&
   s1.regs[SP(User)]       == s2.regs[SP(User)] &&
   s1.regs[SP(FIQ)]        == s2.regs[SP(FIQ)] &&
   s1.regs[SP(IRQ)]        == s2.regs[SP(IRQ)] &&
   s1.regs[SP(Supervisor)] == s2.regs[SP(Supervisor)] &&
   s1.regs[SP(Abort)]      == s2.regs[SP(Abort)] &&
   s1.regs[SP(Undefined)]  == s2.regs[SP(Undefined)]
}
