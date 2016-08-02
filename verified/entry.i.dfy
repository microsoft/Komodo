include "kev_common.s.dfy"
include "ARMdef.dfy"
include "pagedb.s.dfy"
include "smcapi.s.dfy"

//-----------------------------------------------------------------------------
// Untrusted Functional Model of Addrspace Entry
//-----------------------------------------------------------------------------
// This model is untrusted. Its security is verified by proofs in entry.s.dfy.
// By proving that the spartan implementation produces the same final state as
// these pure functions, the spartan implementation is ensured to have the
// same properties.

function enterDispatchFunctional(stateIn:state, dispPage: PageNr, arg1: int, arg2: int,
    arg3: int, pageDbIn:PageDb) : state
    requires ValidState(stateIn);
	requires validPageDb(pageDbIn);
    //TODO requires pageDb corresponds to stateIn
    // This does not have a PageDbOut because it does not change the PageDb
    // May need lemma to ensure s' corresponds to pageDbIn still
{
	reveal_validPageDb();
	var p_out := smc_enter(pageDbIn, dispPage, arg1, arg2, arg3);
	var pageDbOut := p_out.0;
	var errOut := p_out.1;
	if(errOut != KEV_ERR_SUCCESS()) then
		// Note: can possibly avoid overspecifying by only requiring the assembly to match the 
		// result of this function whenever there is no error, and just requiring that
        // stateOut corresponds to PageDbIn in either case
		stateIn
	else
		reveal_ValidRegState();
		var addrspacePage := pageDbIn[dispPage].addrspace;
		var addrspace := pageDbIn[addrspacePage].entry;

		var confOut := stateIn.conf.(m := User, ns := Secure, l1p := addrspace.l1ptnr);
		var regsOut := stateIn.regs[R0 := arg1][R1 := arg2][R2 := arg3];
	
        // This won't be necessary to prove the safety property.
		var sp_usr := stateIn.regs[SP(User)];
		var lr_usr := stateIn.regs[LR(User)];
		var lr_svc := stateIn.regs[LR(Supervisor)];
		var lr_abt := stateIn.regs[LR(Abort)];
		var lr_und := stateIn.regs[LR(Undefined)];
		var globsOut := stateIn.m.globals[OSymbol("sp_usr") := [sp_usr]]
			    [OSymbol("lr_usr") := [lr_usr]][OSymbol("lr_svc") := [lr_svc]]
			    [OSymbol("lr_abt") := [lr_abt]][OSymbol("lr_und") := [lr_und]];		
		
        var mOut := stateIn.m.(globals := globsOut);
        
        // TODO? set FIQ, IRQ bits so interrupts are taken to monitor mode
            // Only needed with more detailed interrupt model in ARMdef
		
        State(regsOut, mOut, confOut)
}

function enterReturnFunctional(stateIn:state) : state
{
    //TODO 
    stateIn
}

function svc(stateIn:state) : state
{
    var s' := stateIn;
    // TODO
    enterReturnFunctional(s')
}

function irq(stateIn:state) : state
{
    // TODO
    var s' := stateIn;
    enterReturnFunctional(s')
}

function fiq(stateIn:state) : state
{
    // TODO
    var s' := stateIn;
    enterReturnFunctional(s')
}

function abort(stateIn:state) : state
{
    // TODO
    var s' := stateIn;
    enterReturnFunctional(s')
}

// svc
    // change to monitor mode + disable interrupts (cpsid)
        // Need interrupt model for this to matter
    // return success + return value of call

// irq / fiq
    // mark pending irq/fiq
    // check spsr for mode
        // if not -> we were in another handler, go handle it.
        // (need more detailed model of exceptions for this to matter)
    // save context in dispatcher

// dispatch_return
    // restore spsr
    // restore non-volatiles

// leave secure world
    // set NS bit
    // Clear FIQ/IRQ bits so interrupts stay in normal
