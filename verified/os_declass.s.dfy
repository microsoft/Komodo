include "ARMdef.s.dfy"
include "kom_common.s.dfy"

predicate {:axiom} do_declassify()
function  {:axiom} declassified_ex(): exception
function  {:axiom} declassified_reg(r:ARMReg):  word

lemma {:axiom} lemma_decl_ex()
    requires do_declassify()
    ensures forall x, s, maskf, maski ::
        nondet_exception(x, s, maskf, maski) == declassified_ex();

lemma {:axiom} lemma_decl_r0(s:state)
    requires ValidState(s)
    requires do_declassify()
    requires declassified_ex() == ExSVC
    ensures forall x, us ::nondet_private_word(x, us, NONDET_REG(R0)) == 
            declassified_reg(R0);

lemma {:axiom} lemma_decl_r1(s:state)
    requires ValidState(s)
    requires do_declassify()
    requires declassified_ex() == ExSVC
    requires declassified_reg(R0) == KOM_SVC_EXIT;
    ensures forall x, us ::nondet_private_word(x, us, NONDET_REG(R1)) == 
            declassified_reg(R1);

lemma {:axiom} lemma_decl_regs(s:state)
    requires ValidState(s)
    requires do_declassify()
    //requires declassified_ex() == ExFIQ
    ensures declassified_ex() == ExSVC ==>
        forall x, us ::nondet_private_word(x, us, NONDET_REG(R0)) == 
            declassified_reg(R0);
    ensures declassified_ex() == ExSVC ==>
        forall x, us ::nondet_private_word(x, us, NONDET_REG(R1)) == 
            declassified_reg(R1);
    //ensures forall x, us ::nondet_private_word(x, us, NONDET_REG(R1)) ==
    //    declassified_reg(R1);
