include "exhandler_state.i.dfy"

method Main()
{
    // prove that the SMC handler is correct
    forall s1:state, p1:PageDb, s2:state
        | GlobalAssumptions() && InitialSMCState(s1)
        && validPageDb(p1) && pageDbCorresponds(s1.m, p1)
        && evalCode(smc_handler(), s1, s2)
        ensures exists p2:PageDb :: smchandler(s1, p1, s2, p2)
            && validPageDb(p2) && pageDbCorresponds(s2.m, p2)
    { lemma_SMCHandlerIsCorrect(s1, p1, s2); }

    // prove that whenever we take an exception from user mode, we can run the right
    // handler and it will establish the invariants assumed in the SMC path
    forall s0:state, s1:state, s3:state, r:state
        | GlobalAssumptions() && ValidState(s0) && s0.ok
        && UsermodeContinuationPrecondition(s0)
        && evalUserExecution(s0, s1, s3)
        && evalCode(exHandler(s3.conf.ex), s3, r)
        ensures exists p2, dp :: KomExceptionHandlerInvariant(s3, p2, r, dp)
    { lemma_UserModeExceptionHandlersAreCorrect(s0, s1, s3, r); }

    // prove that interrupts taken from non-SVC PL1 modes maintain the invariant
    forall s0:state, ex:exception, s1:state, r:state
        | GlobalAssumptions() && ValidState(s0) && s0.ok
        && UsermodeContinuationPrecondition(s0)
        && priv_of_state(s0) == PL1 && interrupts_enabled(s0)
        && mode_of_state(s0) != Supervisor
        && (ex == ExFIQ || ex == ExIRQ)
        && evalExceptionTaken(s0, ex, nondet_word(s0.conf.nondet, NONDET_PC()), s1)
        && evalCode(exHandler(ex), s1, r)
        ensures KomInterruptHandlerInvariant(s1, r)
    { lemma_PrivModeExceptionHandlersAreCorrect(s0, ex, s1, r); }

    // prove the special-case User -> SVC -> FIQ nested interrupt path
    forall s0:state, s1:state, s2:state, r:state
        | GlobalAssumptions() && ValidState(s0) && s0.ok
        && UsermodeContinuationPrecondition(s0)
        && mode_of_state(s0) == User && interrupts_enabled(s0)
        && (exists upc:word :: evalExceptionTaken(s0, ExSVC, upc, s1))
        && evalExceptionTaken(s1, ExFIQ, nondet_word(s1.conf.nondet, NONDET_PC()), s2)
        && evalCode(exHandler(ExFIQ), s2, r)
        ensures exists p0, dp :: KomExceptionHandlerInvariant(s2, p0, r, dp)
    { lemma_SVCFIQNestedExceptionIsCorrect(s0, s1, s2, r); }

    printAll();
}
