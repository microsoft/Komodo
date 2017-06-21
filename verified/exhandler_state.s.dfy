include "kom_print.s.dfy"

// these are global assumptions
predicate GlobalAssumptions()
{
    SaneConstants()
        && UsermodeContinuationPreconditionDef()
        && UsermodeContinuationInvariantDef()
        && InterruptContinuationPreconditionDef()
        && InterruptContinuationInvariantDef()
}

// this is what we assume about the initial state on entry to the SMC handler
predicate InitialSMCState(s:state)
{
    reveal ValidRegState();
    reveal ValidSRegState();

    ValidState(s) && s.ok
        && SaneMem(s.m)
        && mode_of_state(s) == Monitor
        && s.conf.scr.ns == NotSecure
        && !interrupts_enabled(s)
        && s.regs[SP(Monitor)] == StackBase()
        && decode_psr(s.sregs[spsr(Monitor)]).m != Monitor
}

function exHandler(ex:exception): va_code
{
    match ex
        case ExAbt => abt_handler()
        case ExUnd => und_handler()
        case ExSVC => svc_handler()
        case ExFIQ => fiq_handler()
        case ExIRQ => irq_handler()
}
