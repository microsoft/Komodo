include "kev_common.s.dfy"
include "ARMdef.dfy"
include "pagedb.s.dfy"
include "smcapi.s.dfy"

function enterFunctionalDispatch(stateIn:state, dispPage: PageNr, arg1: int, arg2: int,
    arg3: int, pageDbIn:PageDb) : state
    requires ValidState(stateIn);
	requires validPageDb(pageDbIn);
{
	reveal_validPageDb();
	var p_out := smc_enter(pageDbIn, dispPage, arg1, arg2, arg3);
	var pageDbOut := p_out.0;
	var errOut := p_out.1;
	if(errOut != KEV_ERR_SUCCESS()) then
		// Note: can possibly avoid overspecifying by only requiring the assembly to match the resultof this
		// function whenever there is no error.
		stateIn
	else
		reveal_ValidRegState();
		var addrspacePage := pageDbIn[dispPage].addrspace;
		var addrspace := pageDbIn[addrspacePage].entry;

		var confOut := stateIn.conf.(m := User, ns := Secure, l1p := addrspace.l1ptnr);
		var regsOut := stateIn.regs[R0 := arg1][R1 := arg2][R2 := arg3];
		
		var sp_usr := stateIn.regs[SP(User)];
		var lr_usr := stateIn.regs[LR(User)];
		var lr_svc := stateIn.regs[LR(Supervisor)];
		var lr_abt := stateIn.regs[LR(Abort)];
		var lr_und := stateIn.regs[LR(Undefined)];
		var globsOut := stateIn.m.globals[OSymbol("sp_usr") := [sp_usr]]
			[OSymbol("lr_usr") := [lr_usr]][OSymbol("lr_svc") := [lr_svc]]
			[OSymbol("lr_abt") := [lr_abt]][OSymbol("lr_und") := [lr_und]];		
		var mOut := stateIn.m.(globals := globsOut);
		State(regsOut, mOut, confOut)
}
