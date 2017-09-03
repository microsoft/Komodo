include "sec_prop.s.dfy"
include "../pagedb.s.dfy"
include "../entry.s.dfy"
include "sec_prop_util.i.dfy"
include "../smcapi.i.dfy"
include "conf_ni_entry.i.dfy"

lemma lemma_enter_enc_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                              s2: state, d2: PageDb, s2':state, d2': PageDb,
                              dispPage: word, arg1: word, arg2: word, arg3: word,
                              obs: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', obs)
    requires smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    requires smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    requires loweq_pdb(d1, d2, obs)
    requires s1.conf.nondet == s2.conf.nondet
    ensures loweq_pdb(d1', d2', obs)
{
    reveal loweq_pdb();
    var e1, e2 := smc_enter_err(d1, dispPage, false), smc_enter_err(d2, dispPage, false);

    assert e1 == KOM_ERR_SUCCESS <==> e2 == KOM_ERR_SUCCESS;

    if(e1 == KOM_ERR_SUCCESS && e2 == KOM_ERR_SUCCESS) {
        var asp1, asp2 := d1[dispPage].addrspace, d2[dispPage].addrspace;
        assert asp1 == asp2;
        if(asp1 == obs) {
            lemma_enter_enc_obs_enter(s1, d1, s1', d1',
                                       s2, d2, s2', d2',
                                       dispPage, arg1, arg2, arg3, 
                                       obs, false);
        } else {
            lemma_enter_loweq_pdb_not_obs(s1, d1, s1', d1',
                                           s2, d2, s2', d2',
                                           dispPage, arg1, arg2, arg3,
                                           asp1, obs, false);
        }
    }
    if(e1 != KOM_ERR_SUCCESS && e2 != KOM_ERR_SUCCESS) {
        assert loweq_pdb(d1', d2', obs);
    }

}

lemma
lemma_enter_loweq_pdb_not_obs(s1: state, d1: PageDb, s1':state, d1': PageDb,
                               s2: state, d2: PageDb, s2':state, d2': PageDb,
                               dispPage: word, arg1: word, arg2: word, arg3: word,
                               asp: PageNr,obs: PageNr, isresume:bool)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', obs)
    requires valAddrPage(d1, asp) && valAddrPage(d2, asp)
    requires !isresume ==> smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    requires !isresume ==> smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    requires isresume ==> smc_resume(s1, d1, s1', d1', dispPage)
    requires isresume ==> smc_resume(s2, d2, s2', d2', dispPage)
    requires validPageNr(dispPage) && d1[dispPage].PageDbEntryTyped? && 
        d2[dispPage].PageDbEntryTyped?
    requires d1[dispPage].addrspace == asp && d2[dispPage].addrspace == asp
    requires asp != obs
    requires loweq_pdb(d1, d2, obs)
    requires smc_enter_err(d1, dispPage, isresume) == KOM_ERR_SUCCESS
            && (smc_enter_err(d2, dispPage, isresume) == KOM_ERR_SUCCESS);
    requires s1.conf.nondet == s2.conf.nondet
    ensures  loweq_pdb(d1', d2', obs)
{
    if(!isresume) {
        var s11:state, steps1: nat :|
            preEntryEnter(s1, s11, d1, dispPage, arg1, arg2, arg3) &&
            validEnclaveExecution(s11, d1, s1', d1', dispPage, steps1);
        
        var s21:state, steps2: nat :|
            preEntryEnter(s2, s21, d2, dispPage, arg1, arg2, arg3) &&
            validEnclaveExecution(s21, d2, s2', d2', dispPage, steps2);

        assert s11.conf.nondet == s21.conf.nondet;
        assert user_regs(s11.regs) == user_regs(s21.regs);

        assert !spsr_of_state(s11).f && !spsr_of_state(s11).i &&
            !spsr_of_state(s21).f && !spsr_of_state(s21).i by {
            assert psr_mask_fiq(encode_mode(User)) == 0 by {
                assert WordAsBits(0x10) == 0x10 && WordAsBits(0x40) == 0x40
                    by { reveal WordAsBits(); }
                lemma_BitsAndWordConversions();
                reveal BitAnd();
            }
            assert psr_mask_irq(encode_mode(User)) == 0 by {
                assert WordAsBits(0x10) == 0x10 && WordAsBits(0x80) == 0x80
                    by { reveal WordAsBits(); }
                lemma_BitsAndWordConversions();
                reveal BitAnd();
            }
        }
        lemma_validEnclaveEx_enc_not_obs(s11, d1, s1', d1', s21, d2, s2', d2',
                                         dispPage, steps1, steps2, asp, obs);
    } else {
        var s11:state, steps1: nat :|
            preEntryResume(s1, s11, d1, dispPage) &&
            validEnclaveExecution(s11, d1, s1', d1', dispPage, steps1);
        
        var s21:state, steps2: nat :|
            preEntryResume(s2, s21, d2, dispPage) &&
            validEnclaveExecution(s21, d2, s2', d2', dispPage, steps2);

        assert s11.conf.nondet == s21.conf.nondet;

        lemma_validEnclaveEx_enc_not_obs(s11, d1, s1', d1', s21, d2, s2', d2',
                                     dispPage, steps1, steps2, asp, obs);
    }
}

lemma lemma_validEnclaveEx_enc_not_obs(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                        s2: state, d2: PageDb, s2':state, d2': PageDb,
                                        dispPg: PageNr, steps1:nat, steps2:nat,
                                        asp: PageNr, obs: PageNr)
    
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') && SaneConstants()
    requires do_declassify()
    requires valAddrPage(d1, asp) && valAddrPage(d2, asp)
    requires valAddrPage(d1, obs) && valAddrPage(d2, obs)
    requires finalDispatcher(d1, dispPg) && finalDispatcher(d2, dispPg)
    requires d1[dispPg].addrspace == asp && d2[dispPg].addrspace == asp
    requires asp != obs
    requires validEnclaveExecution(s1, d1, s1', d1', dispPg, steps1)
    requires validEnclaveExecution(s2, d2, s2', d2', dispPg, steps2);
    requires loweq_pdb(d1, d2, obs)
    requires s1.conf.nondet == s2.conf.nondet
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires !spsr_of_state(s1).f && !spsr_of_state(s1).i
    requires !spsr_of_state(s2).f && !spsr_of_state(s2).i
    requires s1.conf.scr == s2.conf.scr;
    // requires InsecureMemInvariant(s1, s2)
    ensures  loweq_pdb(d1', d2', obs)
    ensures  same_ret(s1', s2')
    ensures  valAddrPage(d1', asp) && valAddrPage(d2', asp)
    ensures  valAddrPage(d1', obs) && valAddrPage(d2', obs)
    ensures finalDispatcher(d1', dispPg) && finalDispatcher(d2', dispPg)
    ensures  d1'[dispPg].addrspace == asp && d2'[dispPg].addrspace == asp
    // ensures InsecureMemInvariant(s1', s2')
    decreases steps1, steps2
{
    reveal validEnclaveExecution();

    var retToEnclave1, s15, d15 := lemma_unpack_validEnclaveExecution(
        s1, d1, s1', d1', dispPg, steps1);
    var retToEnclave2, s25, d25 := lemma_unpack_validEnclaveExecution(
        s2, d2, s2', d2', dispPg, steps2);

    lemma_validEnclaveExecutionStep_validPageDb(s1, d1, s15, d15, dispPg, retToEnclave1);
    lemma_validEnclaveExecutionStep_validPageDb(s2, d2, s25, d25, dispPg, retToEnclave2);
    lemma_validEnclaveStep_enc_not_obs(s1, d1, s15, d15, s2, d2, s25, d25,
        dispPg, retToEnclave1, retToEnclave2, asp, obs);

    assert retToEnclave1 == retToEnclave2;

    if(retToEnclave1) {
        lemma_validEnclaveExecution(s15, d15, s1', d1', dispPg, steps1 - 1);
        lemma_validEnclaveExecution(s25, d25, s2', d2', dispPg, steps2 - 1);
        lemma_validEnclaveEx_enc_not_obs(s15, d15, s1', d1', s25, d25, s2', d2',
                                         dispPg, steps1 - 1, steps2 - 1, asp, 
                                         obs);
    } else {
        reveal loweq_pdb();
    }
}

lemma lemma_validEnclaveStep_enc_not_obs(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                          s2: state, d2: PageDb, s2':state, d2': PageDb,
                                          dispPg: PageNr, ret1:bool, ret2:bool,
                                          asp: PageNr, obs: PageNr)
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') && SaneConstants()
    requires do_declassify()
    requires valAddrPage(d1, asp) && valAddrPage(d2, asp)
    requires valAddrPage(d1, obs) && valAddrPage(d2, obs)
    requires finalDispatcher(d1, dispPg)
    requires finalDispatcher(d2, dispPg)
    requires d1[dispPg].addrspace == asp && d2[dispPg].addrspace == asp
    requires asp != obs
    // requires InsecureMemInvariant(s1, s2)
    requires validEnclaveExecutionStep(s1, d1, s1', d1', dispPg, ret1);
    requires validEnclaveExecutionStep(s2, d2, s2', d2', dispPg, ret2);
    requires loweq_pdb(d1, d2, obs)
    requires s1.conf.nondet == s2.conf.nondet
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires !spsr_of_state(s1).f && !spsr_of_state(s1).i
    requires !spsr_of_state(s2).f && !spsr_of_state(s2).i
    requires s1.conf.scr == s2.conf.scr;
    ensures  loweq_pdb(d1', d2', obs)
    ensures  ret1 == ret2
    ensures  ret1 ==> s1'.conf.nondet == s2'.conf.nondet;
    ensures  !ret1 ==> same_ret(s1', s2')
    ensures  valAddrPage(d1', asp)  && valAddrPage(d2', asp)
    ensures  valAddrPage(d1', obs) && valAddrPage(d2', obs)
    ensures finalDispatcher(d1', dispPg) && finalDispatcher(d2', dispPg)
    ensures  d1'[dispPg].addrspace == asp && d2'[dispPg].addrspace == asp
    // ensures  InsecureMemInvariant(s1', s2')
{
    reveal validEnclaveExecutionStep();
    var s14, d14 :|
        validEnclaveExecutionStep'(s1, d1, s14, d14, s1', d1',
            dispPg, ret1);

    var s24, d24 :|
        validEnclaveExecutionStep'(s2, d2, s24, d24, s2', d2',
            dispPg, ret2);

    lemma_validEnclaveStepPrime_enc_not_obs(
        s1, d1, s14, d14, s1', d1',
        s2, d2, s24, d24, s2', d2',
        dispPg, ret1, ret2, asp, obs);
}

lemma {:timeLimitMultiplier 3}
lemma_validEnclaveStepPrime_enc_not_obs(
s11: state, d11: PageDb, s14:state, d14:PageDb, r1:state, rd1:PageDb,
s21: state, d21: PageDb, s24:state, d24:PageDb, r2:state, rd2:PageDb,
dispPg:PageNr, retToEnclave1:bool, retToEnclave2:bool,
asp: PageNr, obs: PageNr)
    requires ValidState(s11) && ValidState(s21) &&
             ValidState(r1)  && ValidState(r2)  &&
             validPageDb(d11) &&
             validPageDb(d21) && 
             validPageDb(d14) && 
             validPageDb(d24) && 
             validPageDb(rd1) && 
             validPageDb(rd2) && 
             SaneConstants()
    requires do_declassify()
    requires valAddrPage(d11, asp) && valAddrPage(d21, asp)
    requires valAddrPage(d11, obs) && valAddrPage(d21, obs)
    requires finalDispatcher(d11, dispPg)
    requires finalDispatcher(d21, dispPg)
    requires validEnclaveExecutionStep'(s11,d11,s14,d14,r1,rd1,dispPg,retToEnclave1)
    requires validEnclaveExecutionStep'(s21,d21,s24,d24,r2,rd2,dispPg,retToEnclave2)
    // requires InsecureMemInvariant(s11, s21)
    requires d11[dispPg].addrspace == asp && d21[dispPg].addrspace == asp
    requires asp != obs
    requires loweq_pdb(d11, d21, obs)
    requires s11.conf.nondet == s21.conf.nondet
    requires mode_of_state(s11) != User && mode_of_state(s21) != User
    // requires spsr_same(s11, s21)
    requires s11.conf.scr == s21.conf.scr;
    ensures  loweq_pdb(rd1, rd2, obs)
    // ensures  InsecureMemInvariant(r1, r2)
    ensures  retToEnclave1 == retToEnclave2
    ensures  retToEnclave1 ==> r1.conf.scr == r2.conf.scr
    ensures  retToEnclave1 ==> r1.conf.nondet == r2.conf.nondet
    ensures  !retToEnclave1 ==> same_ret(r1, r2)
    ensures  valAddrPage(rd1, asp)  && valAddrPage(rd2, asp)
    ensures  valAddrPage(rd1, obs) && valAddrPage(rd2, obs)
    ensures finalDispatcher(rd1, dispPg) && finalDispatcher(rd2, dispPg)
    ensures  rd1[dispPg].addrspace == asp && rd2[dispPg].addrspace == asp
    // ensures  retToEnclave1 ==> OperandContents(r1, OLR) == OperandContents(r2, OLR)
    // ensures  retToEnclave1 ==> user_regs(r1.regs) == user_regs(r2.regs)
{    
    assert l1pOfDispatcher(d11, dispPg) == l1pOfDispatcher(d21, dispPg) by
        { reveal loweq_pdb(); }
    var l1p := l1pOfDispatcher(d11, dispPg);

    assert dataPagesCorrespond(s11.m, d11);
    assert dataPagesCorrespond(s21.m, d21);
    
    assert userspaceExecutionAndException(s11, s14);
    assert userspaceExecutionAndException(s21, s24);
    
    reveal userspaceExecutionAndException();

    var s1', s12 :| userspaceExecutionAndException'(s11, s1', s12, s14);
    var s2', s22 :| userspaceExecutionAndException'(s21, s2', s22, s24);

    var pc1 := OperandContents(s11, OLR);
    var pc2 := OperandContents(s21, OLR);
    
    assert ExtractAbsPageTable(s12).Just? by {
        assert ExtractAbsPageTable(s11).Just?;
        assert ExtractAbsPageTable(s11) == ExtractAbsPageTable(s1');
        assert ExtractAbsPageTable(s12) == ExtractAbsPageTable(s1');
    }
    var (s13, expc1, ex1) := userspaceExecutionFn(s12, pc1);
    var (s23, expc2, ex2) := userspaceExecutionFn(s22, pc2);
  
    /*
    assert InsecureMemInvariant(s12, s22) by {
        assert InsecureMemInvariant(s11, s12);
        assert InsecureMemInvariant(s21, s22);
    }
    */

    var pt1 := ExtractAbsPageTable(s12);
    var pt2 := ExtractAbsPageTable(s22);

    assert pageTableCorresponds(s12, d11, l1p)
        && pageTableCorresponds(s22, d21, l1p) by
    { 
        assert pageTableCorresponds(s11, d11, l1p);
        assert pageTableCorresponds(s21, d21, l1p);
        reveal pageTableCorresponds();
    }

    assert pt1 == pt2 by {
        lemma_eqpdb_pt_coresp_not_atkr(d11, d21, s12, s22, l1p, asp, obs);
    }

    assert s12.conf.nondet == s22.conf.nondet;

    /*
    assert InsecureMemInvariant(s13, s23) by {
        lemma_insecure_mem_userspace(
            s12, pc1, s13, expc1, ex1,
            s22, pc2, s23, expc2, ex2);
    }

    assert InsecureMemInvariant(s14, s24);

    assert InsecureMemInvariant(r1, r2);
    */

    assert s13.conf.nondet == s23.conf.nondet by
    {
        reveal userspaceExecutionFn();
        assert s13.conf.nondet == nondet_int(s12.conf.nondet, NONDET_GENERATOR());
        assert s23.conf.nondet == nondet_int(s22.conf.nondet, NONDET_GENERATOR());
    }
    
    assert s14.conf.nondet == s24.conf.nondet;

    assert ex1 == ex2 && s14.conf.ex == s24.conf.ex by {
        lemma_decl_ex(s1', s12, s14, s2', s22, s24);
    }

    assert loweq_pdb(d14, d24, obs) by
    {
        assert validPageDbs({d11,d21,d14,d24});
        lemma_updateUserPages_conf_not_atkr(s14, d11, d14,
            s24, d21, d24, dispPg, asp, obs);
    }

    assert valAddrPage(d14, obs) && valAddrPage(d24, obs) &&
        d14[dispPg].addrspace == asp && d24[dispPg].addrspace == asp by
        { reveal updateUserPagesFromState(); }

    assert retToEnclave1 == retToEnclave2 &&
        (ex1 == ExSVC ==> s14.regs[R0] == s24.regs[R0]) &&
        (ex1 == ExSVC && (s14.regs[R0] == KOM_SVC_EXIT ||
            s14.regs[R0] == KOM_SVC_MAP_DATA ||
            s14.regs[R0] == KOM_SVC_UNMAP_DATA ||
            s14.regs[R0] == KOM_SVC_INIT_L2PTABLE) ==>
            s14.regs[R1] == s24.regs[R1]) &&
        (ex1 == ExSVC && (s14.regs[R0] == KOM_SVC_MAP_DATA ||
            s14.regs[R0] == KOM_SVC_UNMAP_DATA ||
            s14.regs[R0] == KOM_SVC_INIT_L2PTABLE) ==>
            s14.regs[R2] == s24.regs[R2]) by
    {
        assert s14.regs[R0] == s13.regs[R0];
        assert s24.regs[R0] == s23.regs[R0];
        reveal userspaceExecutionFn();
        if(ex1 == ExSVC) {
            lemma_decl_svc_r0(s13, s14, s23, s24);
            if(s14.regs[R0] == KOM_SVC_EXIT ||
               s14.regs[R0] == KOM_SVC_MAP_DATA ||
               s14.regs[R0] == KOM_SVC_UNMAP_DATA ||
               s14.regs[R0] == KOM_SVC_INIT_L2PTABLE){
                lemma_decl_svc_r1(s13, s14, s23, s24);
            }
            if(s14.regs[R0] == KOM_SVC_MAP_DATA ||
               s14.regs[R0] == KOM_SVC_UNMAP_DATA ||
               s14.regs[R0] == KOM_SVC_INIT_L2PTABLE){
                lemma_decl_svc_r2(s13, s14, s23, s24);
            }
        }
    }
   
    lemma_validEnclaveStepPrime_conf_not_atkr_retnondet(
        s11, d11, s14, d14, r1, rd1,
        s21, d21, s24, d24, r2, rd2,
        dispPg, retToEnclave1, retToEnclave2, asp, obs);

}

lemma lemma_enter_enc_obs_enter(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                 s2: state, d2: PageDb, s2':state, d2': PageDb,
                                 dispPg: word, arg1: word, arg2: word, arg3: word,
                                 obs: PageNr, isresume:bool)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', obs)
    requires !isresume ==> smc_enter(s1, d1, s1', d1', dispPg, arg1, arg2, arg3)
    requires !isresume ==> smc_enter(s2, d2, s2', d2', dispPg, arg1, arg2, arg3)
    requires isresume ==> smc_resume(s1, d1, s1', d1', dispPg)
    requires isresume ==> smc_resume(s2, d2, s2', d2', dispPg)
    requires loweq_pdb(d1, d2, obs)
    requires entering_obs(d1, d2, dispPg, obs, isresume);
    requires s1.conf.nondet == s2.conf.nondet
    ensures  loweq_pdb(d1', d2', obs)
{

    if(!isresume) {
        var s11:state, steps1: nat :|
            preEntryEnter(s1, s11, d1, dispPg, arg1, arg2, arg3) &&
            validEnclaveExecution(s11, d1, s1', d1', dispPg, steps1);
        
        var s21:state, steps2: nat :|
            preEntryEnter(s2, s21, d2, dispPg, arg1, arg2, arg3) &&
            validEnclaveExecution(s21, d2, s2', d2', dispPg, steps2);

        assert s11.conf.nondet == s21.conf.nondet;
        assert user_regs(s11.regs) == user_regs(s21.regs);

        assert OperandContents(s11, OLR) == OperandContents(s21, OLR) by 
        {
            assert OperandContents(s11, OLR) == d1[dispPg].entry.entrypoint;
            assert OperandContents(s21, OLR) == d2[dispPg].entry.entrypoint;
            reveal loweq_pdb();
        }
        
        assert spsr_same(s11, s21) by {
            assert preEntryEnter(s1, s11, d1, dispPg, arg1, arg2, arg3);
            assert preEntryEnter(s2, s21, d2, dispPg, arg1, arg2, arg3);
            var mode1 := mode_of_state(s11);
            var mode2 := mode_of_state(s21);
            assert mode1 != User && mode2 != User;
            reveal ValidSRegState();
            assert s11.sregs[spsr(mode1)] == encode_mode(User);
            assert s21.sregs[spsr(mode2)] == encode_mode(User);
        }

        assert !spsr_of_state(s11).f && !spsr_of_state(s11).i &&
            !spsr_of_state(s21).f && !spsr_of_state(s21).i by {
            assert psr_mask_fiq(encode_mode(User)) == 0 by {
                assert WordAsBits(0x10) == 0x10 && WordAsBits(0x40) == 0x40
                    by { reveal WordAsBits(); }
                lemma_BitsAndWordConversions();
                reveal BitAnd();
            }
            assert psr_mask_irq(encode_mode(User)) == 0 by {
                assert WordAsBits(0x10) == 0x10 && WordAsBits(0x80) == 0x80
                    by { reveal WordAsBits(); }
                lemma_BitsAndWordConversions();
                reveal BitAnd();
            }
        }
        lemma_validEnclaveEx_enc(s11, d1, s1', d1', s21, d2, s2', d2',
                                             dispPg, steps1, steps2, obs);
    } else {
        var s11:state, steps1: nat :|
            preEntryResume(s1, s11, d1, dispPg) &&
            validEnclaveExecution(s11, d1, s1', d1', dispPg, steps1);
        
        var s21:state, steps2: nat :|
            preEntryResume(s2, s21, d2, dispPg) &&
            validEnclaveExecution(s21, d2, s2', d2', dispPg, steps2);

        assert s11.conf.nondet == s21.conf.nondet;

        assert d1[dispPg].entry == d2[dispPg].entry by
            { reveal loweq_pdb(); }

        assert user_regs(s11.regs) == user_regs(s21.regs) by {
            var disp := d1[dispPg].entry;
            assert (forall r | r in USER_REGS() :: 
                (s11.regs[r] == disp.ctxt.regs[r] &&
                 s21.regs[r] == disp.ctxt.regs[r]));
            eqregs(user_regs(s11.regs), user_regs(s21.regs));
        }

        assert OperandContents(s11, OLR) == OperandContents(s21, OLR) by 
        {   
            assert OperandContents(s11, OLR) == d1[dispPg].entry.ctxt.pc;
            assert OperandContents(s21, OLR) == d2[dispPg].entry.ctxt.pc;
            reveal loweq_pdb();
        }
        
        assert spsr_same(s11, s21) by {
            var disp := d1[dispPg].entry;
            assert preEntryResume(s1, s11, d1, dispPg);
            assert preEntryResume(s2, s21, d2, dispPg);
            reveal ValidSRegState();
            var mode1 := mode_of_state(s11);
            var mode2 := mode_of_state(s21);
            assert mode1 != User && mode2 != User;
            assert s11.sregs[spsr(mode1)] == disp.ctxt.cpsr;
            assert s21.sregs[spsr(mode2)] == disp.ctxt.cpsr;
        }
        lemma_validEnclaveEx_enc(s11, d1, s1', d1', s21, d2, s2', d2',
                                             dispPg, steps1, steps2, obs);
    }
}

lemma lemma_validEnclaveEx_enc(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                    s2: state, d2: PageDb, s2':state, d2': PageDb,
                                    dispPg: PageNr, steps1:nat, steps2:nat,
                                    obs: PageNr)
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') && SaneConstants()
    requires obs_entry(d1, d2, dispPg, obs)
    requires validEnclaveExecution(s1, d1, s1', d1', dispPg, steps1)
    requires validEnclaveExecution(s2, d2, s2', d2', dispPg, steps2);
    requires loweq_pdb(d1, d2, obs)
    requires s1.conf.nondet == s2.conf.nondet
    requires OperandContents(s1, OLR) == OperandContents(s2, OLR)
    requires user_regs(s1.regs) == user_regs(s2.regs)
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires !spsr_of_state(s1).f && !spsr_of_state(s1).i
    requires !spsr_of_state(s2).f && !spsr_of_state(s2).i
    requires spsr_same(s1, s2)
    requires s1.conf.scr == s2.conf.scr;
    ensures  obs_entry(d1', d2', dispPg, obs)
    ensures  loweq_pdb(d1', d2', obs)
    decreases steps1, steps2
{
    reveal validEnclaveExecution();

    var retToEnclave1, s15, d15 := lemma_unpack_validEnclaveExecution(
        s1, d1, s1', d1', dispPg, steps1);
    var retToEnclave2, s25, d25 := lemma_unpack_validEnclaveExecution(
        s2, d2, s2', d2', dispPg, steps2);

    lemma_validEnclaveExecutionStep_validPageDb(s1, d1, s15, d15, dispPg, retToEnclave1);
    lemma_validEnclaveExecutionStep_validPageDb(s2, d2, s25, d25, dispPg, retToEnclave2);
    lemma_validEnclaveStep_enc(s1, d1, s15, d15, s2, d2, s25, d25,
        dispPg, obs, retToEnclave1, retToEnclave2);

    assert retToEnclave1 == retToEnclave2;

    if(retToEnclave1) {
        lemma_validEnclaveExecution(s15, d15, s1', d1', dispPg, steps1 - 1);
        lemma_validEnclaveExecution(s25, d25, s2', d2', dispPg, steps2 - 1);
        lemma_validEnclaveEx_enc(s15, d15, s1', d1', s25, d25, s2', d2',
                                         dispPg, steps1 - 1, steps2 - 1, obs);
        assert loweq_pdb(d1', d2', obs);
    } else {
        assert s2' == s25;
        assert s1' == s15;
        assert d1' == d15;
        assert d2' == d25;
        assert loweq_pdb(d1', d2', obs);
    }

}

lemma lemma_validEnclaveStep_enc(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                      s2: state, d2: PageDb, s2':state, d2': PageDb,
                                      dispPage:PageNr, obs: PageNr, ret1:bool, ret2:bool)
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') && SaneConstants()
    requires obs_entry(d1, d2, dispPage, obs)
    requires validEnclaveExecutionStep(s1, d1, s1', d1', dispPage, ret1);
    requires validEnclaveExecutionStep(s2, d2, s2', d2', dispPage, ret2);
    requires loweq_pdb(d1, d2, obs)
    requires s1.conf.nondet == s2.conf.nondet
    requires OperandContents(s1, OLR) == OperandContents(s2, OLR)
    requires user_regs(s1.regs) == user_regs(s2.regs)
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires spsr_same(s1, s2)
    requires s1.conf.scr == s2.conf.scr;
    ensures  obs_entry(d1', d2', dispPage, obs)
    ensures  loweq_pdb(d1', d2', obs)
    ensures  ret1 == ret2
    ensures  ret1 ==> s1'.conf.scr == s2'.conf.scr;
    ensures  ret1 ==> s1'.conf.nondet == s2'.conf.nondet
    ensures  ret1 ==> OperandContents(s1', OLR) == OperandContents(s2', OLR)
    ensures  ret1 ==> user_regs(s1'.regs) == user_regs(s2'.regs)
{
    reveal validEnclaveExecutionStep();
    var s14, d14 :|
        validEnclaveExecutionStep'(s1, d1, s14, d14, s1', d1',
            dispPage, ret1);

    var s24, d24 :|
        validEnclaveExecutionStep'(s2, d2, s24, d24, s2', d2',
            dispPage, ret2);
    
    lemma_updateUserPagesFromState_validPageDb(s14, d1, dispPage);
    lemma_updateUserPagesFromState_validPageDb(s24, d2, dispPage);

    assert validPageDb(d1);
    assert validPageDb(d2);
    assert validPageDb(d14);
    assert validPageDb(d24);
    assert validPageDb(d1');
    assert validPageDb(d2');
    lemma_validEnclaveStepPrime_enc(
        s1, d1, s14, d14, s1', d1',
        s2, d2, s24, d24, s2', d2',
        dispPage, ret1, ret2, obs);
}

lemma lemma_userspaceExecutionFn_loweq_integ(
s12: state, pc1:word, expc1:word, ex1:exception, s13:state,
s22: state, pc2:word, expc2:word, ex2:exception, s23:state)
    requires ValidState(s12) && ValidState(s13) && ValidState(s22) && 
        ValidState(s23)
    requires mode_of_state(s12) == User && mode_of_state(s22) == User
    requires ExtractAbsPageTable(s12).Just? && ExtractAbsPageTable(s22).Just?
    requires (s13, expc1, ex1) == userspaceExecutionFn(s12, pc1)
    requires (s23, expc2, ex2) == userspaceExecutionFn(s22, pc2)
    requires ExtractAbsPageTable(s12) == ExtractAbsPageTable(s22)
    requires user_visible_state(s12, pc1, ExtractAbsPageTable(s12).v) ==
        user_visible_state(s22, pc2, ExtractAbsPageTable(s22).v)
    requires s12.conf.nondet == s22.conf.nondet
    requires s12.conf.scr == s22.conf.scr
    requires s12.conf.cpsr.f == s22.conf.cpsr.f;
    requires s12.conf.cpsr.i == s22.conf.cpsr.i;
    ensures  ex1 == ex2
    ensures  user_regs(s13.regs) == user_regs(s23.regs)
    ensures  expc1 == expc2
    ensures  s13.conf.scr == s23.conf.scr
    ensures s13.conf.nondet == s23.conf.nondet
    ensures mode_of_exception(s13.conf, ex1) == mode_of_exception(s23.conf, ex2)
    ensures cpsr in s13.sregs && cpsr in s23.sregs &&
        s13.sregs[cpsr] == s23.sregs[cpsr]
{
    reveal userspaceExecutionFn();
    assert user_regs(s13.regs) == user_regs(s23.regs) by {
        var user_state1 := user_visible_state(s12, pc1, 
            ExtractAbsPageTable(s12).v);
        var user_state2 := user_visible_state(s22, pc2, 
            ExtractAbsPageTable(s22).v);
        var hr1 := havocUserRegs(s12.conf.nondet, user_state1, s12.regs);
        var hr2 := havocUserRegs(s22.conf.nondet, user_state2, s22.regs);
        assert s13.regs == hr1 by
            { reveal userspaceExecutionFn(); }
        assert s23.regs == hr2 by
            { reveal userspaceExecutionFn(); }
        assert user_state1 == user_state2;
        assert s12.conf.nondet == s22.conf.nondet;
        forall (r | r in USER_REGS() )
            ensures hr1[r] ==
                nondet_private_word(s12.conf.nondet, user_state1, NONDET_REG(r))
            ensures hr2[r] ==
                nondet_private_word(s22.conf.nondet, user_state2, NONDET_REG(r))
            ensures hr1[r] == hr2[r]
            ensures user_regs(hr1)[r] == user_regs(hr2)[r]
        {
        }
        lemma_user_regs_domain(hr1, user_regs(hr1));
        lemma_user_regs_domain(hr2, user_regs(hr2));
        assert forall r :: r in user_regs(hr1) <==> r in user_regs(hr2);
        assert forall r | r in user_regs(hr1) :: user_regs(hr1)[r] == user_regs(hr2)[r];
    
        eqregs(user_regs(hr1), user_regs(hr2));
        assert user_regs(hr1) == user_regs(hr2);
    }

}

lemma
lemma_validEnclaveStepPrime_enc(
s11: state, d11: PageDb, s14:state, d14:PageDb, r1:state, rd1:PageDb,
s21: state, d21: PageDb, s24:state, d24:PageDb, r2:state, rd2:PageDb,
dispPg:PageNr, retToEnclave1:bool, retToEnclave2:bool, obs: PageNr
)
    requires ValidState(s11) && ValidState(s21) &&
             ValidState(r1)  && ValidState(r2)  &&
             validPageDb(d11) &&
             validPageDb(d21) && 
             validPageDb(d14) && 
             validPageDb(d24) && 
             validPageDb(rd1) && 
             validPageDb(rd2) && 
             SaneConstants()
    requires obs_entry(d11, d21, dispPg, obs)
    requires validEnclaveExecutionStep'(s11,d11,s14,d14,r1,rd1,dispPg,retToEnclave1)
    requires validEnclaveExecutionStep'(s21,d21,s24,d24,r2,rd2,dispPg,retToEnclave2)
    requires OperandContents(s11, OLR) == OperandContents(s21, OLR)
    requires user_regs(s11.regs) == user_regs(s21.regs)
    requires loweq_pdb(d11, d21, obs)
    requires s11.conf.nondet == s21.conf.nondet
    requires mode_of_state(s11) != User && mode_of_state(s21) != User
    requires spsr_same(s11, s21)
    requires s11.conf.scr == s21.conf.scr;
    ensures  obs_entry(rd1, rd2, dispPg, obs)
    ensures  loweq_pdb(rd1, rd2, obs)
    ensures  retToEnclave1 == retToEnclave2
    ensures  retToEnclave1 ==> r1.conf.scr == r2.conf.scr
    ensures  retToEnclave1 ==> r1.conf.nondet == r2.conf.nondet
    ensures  retToEnclave1 ==> OperandContents(r1, OLR) == OperandContents(r2, OLR)
    ensures  retToEnclave1 ==> user_regs(r1.regs) == user_regs(r2.regs)
{                        
    assert l1pOfDispatcher(d11, dispPg) == l1pOfDispatcher(d21, dispPg) by
        { reveal loweq_pdb(); }
    var l1p := l1pOfDispatcher(d11, dispPg);

    assert dataPagesCorrespond(s11.m, d11);
    assert dataPagesCorrespond(s21.m, d21);
    
    assert userspaceExecutionAndException(s11, s14);
    assert userspaceExecutionAndException(s21, s24);

    reveal userspaceExecutionAndException();

    var s1', s12 :| userspaceExecutionAndException'(s11, s1', s12, s14);
    var s2', s22 :| userspaceExecutionAndException'(s21, s2', s22, s24);

    var pc1 := OperandContents(s11, OLR);
    var pc2 := OperandContents(s21, OLR);
    
    var (s13, expc1, ex1) := userspaceExecutionFn(s12, pc1);
    var (s23, expc2, ex2) := userspaceExecutionFn(s22, pc2);

    // assert s12.m == s11.m;
    // assert s22.m == s21.m;
    assert cpsr_same(s12, s22) by {
        lemma_eval_cpsrs(s11, s1', s12, s21, s2', s22);
    }

    assert pageTableCorresponds(s12, d11, l1p) &&
        pageTableCorresponds(s22, d21, l1p) by
    { 
        assert pageTableCorresponds(s11, d11, l1p);
        assert pageTableCorresponds(s21, d21, l1p);
        reveal pageTableCorresponds();
    }

    var pt1 := ExtractAbsPageTable(s12);
    var pt2 := ExtractAbsPageTable(s22);
    assert pt1 == pt2 by {
        lemma_eqpdb_pt_coresp(d11, d21, s12, s22, l1p, obs);
    }
    lemma_userStatesEquiv_atkr(
        s11, s1', s12, s14, pc1, pt1, d11,
        s21, s2', s22, s24, pc2, pt2, d21,
        dispPg, obs, l1p);

    lemma_userspaceExecutionFn_loweq_integ(
        s12, pc1, expc1, ex1, s13,
        s22, pc2, expc2, ex2, s23
    );

    var user_state1 := user_visible_state(s12, pc1, pt1.v);
    var user_state2 := user_visible_state(s22, pc2, pt2.v);

    assert s14.conf.ex == ex1 && s24.conf.ex == ex2;

    assert s14.conf.nondet == s24.conf.nondet;

    lemma_userspaceExec_atkr(
        s11, s1', s12, s13, s14, d11, d14,
        s21, s2', s22, s23, s24, d21, d24,
        dispPg, obs, l1p);

    assert user_regs(s14.regs) == user_regs(s13.regs)
        && user_regs(s24.regs) == user_regs(s23.regs) by
    {
        lemma_exceptionTakenRegs(s13, ex1, expc1, s14);
        lemma_exceptionTakenRegs(s23, ex2, expc2, s24);
    }

    assert OperandContents(s14, OLR) == OperandContents(s24, OLR) by
    {
        lemma_exceptionTakenRegs(s13, ex1, expc1, s14);
        lemma_exceptionTakenRegs(s23, ex2, expc2, s24);
        assert expc1 == expc2;
    }

    assert retToEnclave1 == retToEnclave2 by {
        assert retToEnclave1 == isReturningSvc(s14);
        assert retToEnclave2 == isReturningSvc(s24);
        reveal ValidRegState();
        assert s14.conf.ex == s24.conf.ex;
        assert R0 in USER_REGS();
        assert R0 in user_regs(s14.regs) && R0 in user_regs(s24.regs);
        assert user_regs(s14.regs) == user_regs(s24.regs);
        assert s14.regs[R0] == s24.regs[R0];

    }

    assert s14.conf.scr == s24.conf.scr;

    var retToEnclave := retToEnclave1;

    assert validDispatcherPage(d14, dispPg) && validDispatcherPage(d24, dispPg);

    if(retToEnclave) {
        var retRegs1 := svcHandled(s14, d14, dispPg).0;
        var retRegs2 := svcHandled(s24, d24, dispPg).0;

        lemma_svcHandled_validPageDb(s14, d14, dispPg, retRegs1, rd1);
        lemma_svcHandled_validPageDb(s24, d24, dispPg, retRegs2, rd2);

        lemma_svcHandled_loweq_pdb(s14, d14, rd1,
            s24, d24, rd2, dispPg, obs);

        assert r1.conf.nondet == r2.conf.nondet by {
            assert s14.conf.nondet == s24.conf.nondet; 
        }
        assert loweq_pdb(rd1, rd2, obs);
        assert r1.conf.nondet == r2.conf.nondet;
        assert retRegs1 == retRegs2;
        assert user_regs(r1.regs) == user_regs(r2.regs) by
        { 
            lemma_preEntryUserRegs(
                s14, r1, retRegs1, rd1,
                s24, r2, retRegs2, rd2, dispPg
            );
        }
        assert OperandContents(r1, OLR) == OperandContents(r2, OLR);
    } else {
        assert validDispatcherPage(d14, dispPg) && validDispatcherPage(d24, dispPg);
        lemma_exceptionTaken_atkr(
            s13, s14, ex1, expc1, 
            s23, s24, ex2, expc2);
        lemma_exceptionHandled_atkr(s14, d14, rd1, s24, d24, rd2,
             r1.regs[R0], r1.regs[R1], r2.regs[R0], r2.regs[R1],
             dispPg, obs);

        assert loweq_pdb(rd1, rd2, obs);
    }
}

//-----------------------------------------------------------------------------
// Resume
//-----------------------------------------------------------------------------
lemma lemma_resume_enc_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                               s2: state, d2: PageDb, s2':state, d2': PageDb,
                               dispPage: word,
                               obs: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', obs)
    requires smc_resume(s1, d1, s1', d1', dispPage)
    requires smc_resume(s2, d2, s2', d2', dispPage)
    requires loweq_pdb(d1, d2, obs)
    requires s1.conf.nondet == s2.conf.nondet
    ensures loweq_pdb(d1', d2', obs)
{
    reveal loweq_pdb();
    var e1, e2 := smc_enter_err(d1, dispPage, true), smc_enter_err(d2, dispPage, true);
    assert e1 == e2;

    if(e1 == KOM_ERR_SUCCESS) {
        var asp1, asp2 := d1[dispPage].addrspace, d2[dispPage].addrspace;
        assert asp1 == asp2;
        if(asp1 == obs) {
            lemma_enter_enc_obs_enter(s1, d1, s1', d1',
                                       s2, d2, s2', d2',
                                       dispPage, 0, 0, 0, 
                                       obs, true);
        } else {
            lemma_enter_loweq_pdb_not_obs(s1, d1, s1', d1',
                                           s2, d2, s2', d2',
                                           dispPage, 0, 0, 0,
                                           asp1, obs, true);
        }
    } 
}
