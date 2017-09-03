include "../ARMdef.s.dfy"
include "../kom_common.s.dfy"

predicate {:axiom} do_declassify()

lemma {:axiom} lemma_decl_ex(s11:state, s12:state, s14:state, s21:state, s22:state, s24:state)
    requires do_declassify()
    requires ValidState(s11) && ValidState(s21)
    requires s11.conf.nondet == s21.conf.nondet
    requires evalUserExecution(s11, s12, s14) && evalUserExecution(s21, s22, s24)
    // requires s12.conf.cpsr.f == s22.conf.cpsr.f && s12.conf.cpsr.i == s22.conf.cpsr.i
    ensures s14.conf.ex == s24.conf.ex

lemma {:axiom} lemma_decl_svc_r0(s13:state, s14:state, s23:state, s24:state)
    requires do_declassify()
    requires ValidState(s13) && ValidState(s23)
    requires mode_of_state(s13) == mode_of_state(s23) == User
    requires s13.conf.nondet == s23.conf.nondet
    requires exists pc1 :: evalExceptionTaken(s13, ExSVC, pc1, s14)
    requires exists pc2 :: evalExceptionTaken(s23, ExSVC, pc2, s24)
    ensures s14.regs[R0] == s24.regs[R0]

lemma {:axiom} lemma_decl_svc_r1(s13:state, s14:state, s23:state, s24:state)
    requires do_declassify()
    requires ValidState(s13) && ValidState(s23)
    requires mode_of_state(s13) == mode_of_state(s23) == User
    requires s13.conf.nondet == s23.conf.nondet
    requires exists pc1 :: evalExceptionTaken(s13, ExSVC, pc1, s14)
    requires exists pc2 :: evalExceptionTaken(s23, ExSVC, pc2, s24)
    requires s14.regs[R0] == s24.regs[R0] 
    requires s14.regs[R0] == KOM_SVC_EXIT ||
        s14.regs[R0] == KOM_SVC_MAP_DATA ||
        s14.regs[R0] == KOM_SVC_UNMAP_DATA ||
        s14.regs[R0] == KOM_SVC_INIT_L2PTABLE
    // On exit: the return value is released to the OS
    // On map_data, unmap_data, and init_l2ptable: the target page is released 
    // to the OS because the OS can distinguish between spare pages and other 
    // kinds of pages and these calls all change the type either to or from a 
    // spare page.
    ensures s14.regs[R1] == s24.regs[R1] 

lemma {:axiom} lemma_decl_svc_r2(s13:state, s14:state, s23:state, s24:state)
    requires do_declassify()
    requires ValidState(s13) && ValidState(s23)
    requires mode_of_state(s13) == mode_of_state(s23) == User
    requires s13.conf.nondet == s23.conf.nondet
    requires exists pc1 :: evalExceptionTaken(s13, ExSVC, pc1, s14)
    requires exists pc2 :: evalExceptionTaken(s23, ExSVC, pc2, s24)
    requires s14.regs[R0] == s24.regs[R0] 
    requires s14.regs[R0] == KOM_SVC_MAP_DATA ||
        s14.regs[R0] == KOM_SVC_UNMAP_DATA ||
        s14.regs[R0] == KOM_SVC_INIT_L2PTABLE
    // On map_data, unmap_data, and init_l2ptable: 
    // For each of these calls, the value of R2 implcitily influences whether 
    // or not pages can change from SparePages or other kinds of pages.
    ensures s14.regs[R2] == s24.regs[R2] 
