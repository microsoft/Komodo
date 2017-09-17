include "sec_prop.s.dfy"
include "../pagedb.s.dfy"
include "../entry.s.dfy"
include "sec_prop_util.i.dfy"
include "../smcapi.i.dfy"


// This one's unstable so it's at the top!
lemma lemma_userspaceExec_atkr(
s11: state, s1':state, s12: state, s13:state, s14: state, d1:PageDb, d14: PageDb,
s21: state, s2':state, s22: state, s23:state, s24: state, d2:PageDb, d24: PageDb,
dispPg: PageNr, atkr: PageNr, l1p: PageNr)
    requires ValidState(s11) && ValidState(s12) && ValidState(s13) && ValidState(s14)
    requires ValidState(s21) && ValidState(s22) && ValidState(s23) && ValidState(s24)
    requires validPageDb(d1) && validPageDb(d14)
    requires validPageDb(d2) && validPageDb(d24)
    requires SaneConstants()
    requires s12.conf.nondet == s22.conf.nondet;
    requires userspaceExecutionAndException'(s11, s1', s12, s14)
    requires userspaceExecutionAndException'(s21, s2', s22, s24)
    requires s13 == userspaceExecutionFn(s12, OperandContents(s11, OLR)).0;
    requires s23 == userspaceExecutionFn(s22, OperandContents(s21, OLR)).0;
    requires obs_entry(d1, d2, dispPg, atkr)
    requires loweq_pdb(d1, d2, atkr)
    requires l1pOfDispatcher(d1, dispPg) == l1pOfDispatcher(d2, dispPg) == l1p
    requires OperandContents(s11, OLR) == OperandContents(s21, OLR)
    requires user_regs(s11.regs) == user_regs(s21.regs)
    requires 
        pageTableCorresponds(s12, d1, l1p) &&
        pageTableCorresponds(s22, d2, l1p) &&
        dataPagesCorrespond(s12.m, d1) &&
        dataPagesCorrespond(s22.m, d2)
    requires d14 == updateUserPagesFromState(s14, d1, dispPg);
    requires d24 == updateUserPagesFromState(s24, d2, dispPg);
    ensures loweq_pdb(d14, d24, atkr)
    ensures obs_entry(d14, d24, dispPg, atkr)
    ensures s14.rng.entropy == s24.rng.entropy
{
    var pc1 := OperandContents(s11, OLR);
    var pc2 := OperandContents(s21, OLR);
    var pt1 := ExtractAbsPageTable(s12);
    var pt2 := ExtractAbsPageTable(s22);
    
    lemma_userStatesEquiv_atkr(
        s11, s1', s12, s14, pc1, pt1, d1,
        s21, s2', s22, s24, pc2, pt2, d2,
        dispPg, atkr, l1p);

    var user_state1 := user_visible_state(s12, pc1, pt1.v);
    var user_state2 := user_visible_state(s22, pc2, pt2.v);

    forall( n : PageNr | pageSWrInAddrspace(d1, l1p, n))
        ensures contentsOfPage(s14, n) ==
            contentsOfPage(s24, n)
    {
        var base := page_monvaddr(n);
        forall( a : addr | a in addrsInPage(n, base) )
            ensures s13.m.addresses[a] == s23.m.addresses[a]
        {
            reveal userspaceExecutionFn();
            assert ExtractAbsPageTable(s12) == ExtractAbsPageTable(s22) by
            {
                lemma_eqpdb_pt_coresp(d1, d2, s12, s22, l1p, atkr);
            }
            var pt := ExtractAbsPageTable(s22);
            assert pt.Just?;
            var pages := WritablePagesInTable(fromJust(pt));
            
            if( PageBase(a) in pages ){
                assert s13.m.addresses[a] ==s23.m.addresses[a];
            } else {
                reveal loweq_pdb();
                lemma_data_page_eqdb_to_addrs(d1, d2, s12, s22, n, a, atkr);
            }
        }
        assert s14.m == s13.m;
        assert s24.m == s23.m;
    }

    
    assert valAddrPage(d14, atkr) by { reveal updateUserPagesFromState(); }
    forall( n : PageNr | pgInAddrSpc(d14, n, atkr) &&
        d14[n].PageDbEntryTyped? &&
        d24[n].PageDbEntryTyped?)
        ensures d14[n].entry == d24[n].entry
    {
        reveal updateUserPagesFromState();
        reveal loweq_pdb();
        assert pageSWrInAddrspace(d1, l1p, n) <==>
            pageSWrInAddrspace(d2, l1p, n);
        if(pageSWrInAddrspace(d1, l1p, n)) {
            assert d1[n].entry == d2[n].entry;
            assert d14[n] == d1[n].(entry := d1[n].entry.(
                contents := contentsOfPage(s14, n)));
            assert d24[n] == d2[n].(entry := d2[n].entry.(
                contents := contentsOfPage(s24, n)));
            assert d14[n].entry == d24[n].entry;
        } else {
            assert d14[n].entry == d1[n].entry;
            assert d24[n].entry == d2[n].entry;
        }
    }

    forall(n : PageNr) 
        ensures pgInAddrSpc(d14, n, atkr) <==> pgInAddrSpc(d1, n, atkr)
        ensures pgInAddrSpc(d24, n, atkr) <==> pgInAddrSpc(d2, n, atkr) 
        { reveal updateUserPagesFromState(); }

    reveal loweq_pdb();
    assert loweq_pdb(d14, d24, atkr);
    assert s14.rng.entropy == s24.rng.entropy by {
        reveal userspaceExecutionFn();
    }
}

lemma lemma_enter_conf_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                              s2: state, d2: PageDb, s2':state, d2': PageDb,
                              dispPage: word, arg1: word, arg2: word, arg3: word,
                              atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    requires smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    requires conf_loweq(s1, d1, s2, d2, atkr)
    requires loweq_pdb(d1, d2, atkr)
    requires s1.conf.nondet == s2.conf.nondet
    ensures loweq_pdb(d1', d2', atkr)
    ensures same_ret(s1', s2')
    ensures InsecureMemInvariant(s1', s2')
{
    reveal loweq_pdb();
    var e1, e2 := smc_enter_err(d1, dispPage, false), smc_enter_err(d2, dispPage, false);

    assert e1 == KOM_ERR_SUCCESS <==> e2 == KOM_ERR_SUCCESS;

    if(e1 == KOM_ERR_SUCCESS && e2 == KOM_ERR_SUCCESS) {
        var asp1, asp2 := d1[dispPage].addrspace, d2[dispPage].addrspace;
        assert asp1 == asp2;
        if(asp1 == atkr) {
            lemma_enter_conf_atkr_enter(s1, d1, s1', d1',
                                       s2, d2, s2', d2',
                                       dispPage, arg1, arg2, arg3, 
                                       atkr, false);
        } else {
            lemma_enter_loweq_pdb_not_atkr(s1, d1, s1', d1',
                                           s2, d2, s2', d2',
                                           dispPage, arg1, arg2, arg3,
                                           asp1, atkr, false);
        }
    }
    if(e1 != KOM_ERR_SUCCESS && e2 != KOM_ERR_SUCCESS) {
        assert loweq_pdb(d1', d2', atkr);
    }

}

lemma
lemma_enter_loweq_pdb_not_atkr(s1: state, d1: PageDb, s1':state, d1': PageDb,
                               s2: state, d2: PageDb, s2':state, d2': PageDb,
                               dispPage: word, arg1: word, arg2: word, arg3: word,
                               asp: PageNr,atkr: PageNr, isresume:bool)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires valAddrPage(d1, asp) && valAddrPage(d2, asp)
    requires !isresume ==> smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    requires !isresume ==> smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    requires isresume ==> smc_resume(s1, d1, s1', d1', dispPage)
    requires isresume ==> smc_resume(s2, d2, s2', d2', dispPage)
    requires validPageNr(dispPage) && d1[dispPage].PageDbEntryTyped? && 
        d2[dispPage].PageDbEntryTyped?
    requires d1[dispPage].addrspace == asp && d2[dispPage].addrspace == asp
    requires asp != atkr
    requires InsecureMemInvariant(s1, s2)
    requires loweq_pdb(d1, d2, atkr)
    requires smc_enter_err(d1, dispPage, isresume) == KOM_ERR_SUCCESS
            && (smc_enter_err(d2, dispPage, isresume) == KOM_ERR_SUCCESS);
    requires s1.conf.nondet == s2.conf.nondet
    ensures  loweq_pdb(d1', d2', atkr)
    ensures  InsecureMemInvariant(s1', s2')
    ensures  same_ret(s1', s2')
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
        lemma_validEnclaveEx_conf_not_atkr(s11, d1, s1', d1', s21, d2, s2', d2',
                                         dispPage, steps1, steps2, asp, atkr);
    } else {
        var s11:state, steps1: nat :|
            preEntryResume(s1, s11, d1, dispPage) &&
            validEnclaveExecution(s11, d1, s1', d1', dispPage, steps1);
        
        var s21:state, steps2: nat :|
            preEntryResume(s2, s21, d2, dispPage) &&
            validEnclaveExecution(s21, d2, s2', d2', dispPage, steps2);

        assert s11.conf.nondet == s21.conf.nondet;

        lemma_validEnclaveEx_conf_not_atkr(s11, d1, s1', d1', s21, d2, s2', d2',
                                     dispPage, steps1, steps2, asp, atkr);
    }
}

lemma lemma_validEnclaveEx_conf_not_atkr(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                        s2: state, d2: PageDb, s2':state, d2': PageDb,
                                        dispPg: PageNr, steps1:nat, steps2:nat,
                                        asp: PageNr, atkr: PageNr)
    
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') && SaneConstants()
    requires do_declassify()
    requires valAddrPage(d1, asp) && valAddrPage(d2, asp)
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
    requires finalDispatcher(d1, dispPg) && finalDispatcher(d2, dispPg)
    requires d1[dispPg].addrspace == asp && d2[dispPg].addrspace == asp
    requires asp != atkr
    requires validEnclaveExecution(s1, d1, s1', d1', dispPg, steps1)
    requires validEnclaveExecution(s2, d2, s2', d2', dispPg, steps2);
    requires InsecureMemInvariant(s1, s2)
    requires loweq_pdb(d1, d2, atkr)
    requires s1.conf.nondet == s2.conf.nondet
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires !spsr_of_state(s1).f && !spsr_of_state(s1).i
    requires !spsr_of_state(s2).f && !spsr_of_state(s2).i
    requires s1.conf.scr == s2.conf.scr;
    // stuff for looping over SVCs:
    ensures  valAddrPage(d1', asp) && valAddrPage(d2', asp)
    ensures  valAddrPage(d1', atkr) && valAddrPage(d2', atkr)
    ensures  finalDispatcher(d1', dispPg) && finalDispatcher(d2', dispPg)
    ensures  d1'[dispPg].addrspace == asp && d2'[dispPg].addrspace == asp
    // Stuff we actually care about:
    ensures  InsecureMemInvariant(s1', s2')
    ensures  same_ret(s1', s2')
    ensures  loweq_pdb(d1', d2', atkr)
    decreases steps1, steps2
{
    reveal validEnclaveExecution();

    var retToEnclave1, s15, d15 := lemma_unpack_validEnclaveExecution(
        s1, d1, s1', d1', dispPg, steps1);
    var retToEnclave2, s25, d25 := lemma_unpack_validEnclaveExecution(
        s2, d2, s2', d2', dispPg, steps2);

    lemma_validEnclaveExecutionStep_validPageDb(s1, d1, s15, d15, dispPg, retToEnclave1);
    lemma_validEnclaveExecutionStep_validPageDb(s2, d2, s25, d25, dispPg, retToEnclave2);
    lemma_validEnclaveStep_conf_not_atkr(s1, d1, s15, d15, s2, d2, s25, d25,
        dispPg, retToEnclave1, retToEnclave2, asp, atkr);

    assert retToEnclave1 == retToEnclave2;

    if(retToEnclave1) {
        lemma_validEnclaveExecution(s15, d15, s1', d1', dispPg, steps1 - 1);
        lemma_validEnclaveExecution(s25, d25, s2', d2', dispPg, steps2 - 1);
        lemma_validEnclaveEx_conf_not_atkr(s15, d15, s1', d1', s25, d25, s2', d2',
                                         dispPg, steps1 - 1, steps2 - 1, asp, 
                                         atkr);
    } else {
        reveal loweq_pdb();
    }
}

lemma lemma_validEnclaveStep_conf_not_atkr(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                          s2: state, d2: PageDb, s2':state, d2': PageDb,
                                          dispPg: PageNr, ret1:bool, ret2:bool,
                                          asp: PageNr, atkr: PageNr)
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') && SaneConstants()
    requires do_declassify()
    requires valAddrPage(d1, asp) && valAddrPage(d2, asp)
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
    requires finalDispatcher(d1, dispPg)
    requires finalDispatcher(d2, dispPg)
    requires d1[dispPg].addrspace == asp && d2[dispPg].addrspace == asp
    requires asp != atkr
    requires InsecureMemInvariant(s1, s2)
    requires validEnclaveExecutionStep(s1, d1, s1', d1', dispPg, ret1);
    requires validEnclaveExecutionStep(s2, d2, s2', d2', dispPg, ret2);
    requires loweq_pdb(d1, d2, atkr)
    requires s1.conf.nondet == s2.conf.nondet
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires !spsr_of_state(s1).f && !spsr_of_state(s1).i
    requires !spsr_of_state(s2).f && !spsr_of_state(s2).i
    requires s1.conf.scr == s2.conf.scr;
    ensures  loweq_pdb(d1', d2', atkr)
    ensures  ret1 == ret2
    ensures  ret1 ==> s1'.conf.nondet == s2'.conf.nondet;
    ensures  !ret1 ==> same_ret(s1', s2')
    ensures  valAddrPage(d1', asp)  && valAddrPage(d2', asp)
    ensures  valAddrPage(d1', atkr) && valAddrPage(d2', atkr)
    ensures  finalDispatcher(d1', dispPg) && finalDispatcher(d2', dispPg)
    ensures  d1'[dispPg].addrspace == asp && d2'[dispPg].addrspace == asp
    ensures  InsecureMemInvariant(s1', s2')
{
    reveal validEnclaveExecutionStep();
    var s14, d14 :|
        validEnclaveExecutionStep'(s1, d1, s14, d14, s1', d1',
            dispPg, ret1);

    var s24, d24 :|
        validEnclaveExecutionStep'(s2, d2, s24, d24, s2', d2',
            dispPg, ret2);

    lemma_validEnclaveStepPrime_conf_not_atkr(
        s1, d1, s14, d14, s1', d1',
        s2, d2, s24, d24, s2', d2',
        dispPg, ret1, ret2, asp, atkr);
}

lemma {:timeLimitMultiplier 3}
lemma_validEnclaveStepPrime_conf_not_atkr(
s11: state, d11: PageDb, s14:state, d14:PageDb, r1:state, rd1:PageDb,
s21: state, d21: PageDb, s24:state, d24:PageDb, r2:state, rd2:PageDb,
dispPg:PageNr, retToEnclave1:bool, retToEnclave2:bool,
asp: PageNr, atkr: PageNr)
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
    requires valAddrPage(d11, atkr) && valAddrPage(d21, atkr)
    requires finalDispatcher(d11, dispPg)
    requires finalDispatcher(d21, dispPg)
    requires validEnclaveExecutionStep'(s11,d11,s14,d14,r1,rd1,dispPg,retToEnclave1)
    requires validEnclaveExecutionStep'(s21,d21,s24,d24,r2,rd2,dispPg,retToEnclave2)
    requires InsecureMemInvariant(s11, s21)
    requires d11[dispPg].addrspace == asp && d21[dispPg].addrspace == asp
    requires asp != atkr
    requires loweq_pdb(d11, d21, atkr)
    requires s11.conf.nondet == s21.conf.nondet
    requires mode_of_state(s11) != User && mode_of_state(s21) != User
    // requires spsr_same(s11, s21)
    requires s11.conf.scr == s21.conf.scr;
    ensures  loweq_pdb(rd1, rd2, atkr)
    ensures  InsecureMemInvariant(r1, r2)
    ensures  retToEnclave1 == retToEnclave2
    ensures  retToEnclave1 ==> r1.conf.scr == r2.conf.scr
    ensures  retToEnclave1 ==> r1.conf.nondet == r2.conf.nondet
    ensures  !retToEnclave1 ==> same_ret(r1, r2)
    ensures  valAddrPage(rd1, asp)  && valAddrPage(rd2, asp)
    ensures  valAddrPage(rd1, atkr) && valAddrPage(rd2, atkr)
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
  
    assert InsecureMemInvariant(s12, s22) by {
        assert InsecureMemInvariant(s11, s12);
        assert InsecureMemInvariant(s21, s22);
    }

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
        lemma_eqpdb_pt_coresp_not_atkr(d11, d21, s12, s22, l1p, asp, atkr);
    }

    assert s12.conf.nondet == s22.conf.nondet;

    assert InsecureMemInvariant(s13, s23) by {
        lemma_insecure_mem_userspace(
            s12, pc1, s13, expc1, ex1,
            s22, pc2, s23, expc2, ex2);
    }

    assert InsecureMemInvariant(s14, s24);

    assert InsecureMemInvariant(r1, r2);

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

    assert loweq_pdb(d14, d24, atkr) by
    {
        assert validPageDbs({d11,d21,d14,d24});
        lemma_updateUserPages_conf_not_atkr(s14, d11, d14,
            s24, d21, d24, dispPg, asp, atkr);
    }

    assert valAddrPage(d14, atkr) && valAddrPage(d24, atkr) &&
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
        dispPg, retToEnclave1, retToEnclave2, asp, atkr);

}

lemma lemma_updateUserPages_conf_not_atkr(
    s14: state, d11: PageDb, d14: PageDb,
    s24: state, d21: PageDb, d24: PageDb,
    dispPg: PageNr, asp: PageNr, atkr: PageNr)
requires validStates({s14, s24}) && SaneConstants()
requires validPageDbs({d11,d21,d14,d24})
requires finalDispatcher(d11, dispPg)
requires finalDispatcher(d21, dispPg)
requires valAddrPage(d11, asp) && valAddrPage(d21, asp)
requires valAddrPage(d11, atkr) && valAddrPage(d21, atkr)
requires d11[dispPg].addrspace == asp && d21[dispPg].addrspace == asp
requires asp != atkr
requires d14 == updateUserPagesFromState(s14, d11, dispPg)
requires d24 == updateUserPagesFromState(s24, d21, dispPg)
requires loweq_pdb(d11, d21, atkr)
ensures  loweq_pdb(d14, d24, atkr)
{
    reveal updateUserPagesFromState();
    reveal loweq_pdb();
}

lemma
lemma_validEnclaveStepPrime_conf_not_atkr_retnondet(
s11: state, d11: PageDb, s14:state, d14:PageDb, r1:state, rd1:PageDb,
s21: state, d21: PageDb, s24:state, d24:PageDb, r2:state, rd2:PageDb,
dispPg:PageNr, retToEnclave1:bool, retToEnclave2:bool,
asp: PageNr, atkr: PageNr
)
    requires ValidState(s11) && ValidState(s21) &&
             ValidState(r1)  && ValidState(r2)  &&
             validPageDb(d11) && validPageDb(d21) &&
             validPageDb(rd1) && validPageDb(rd2) && SaneConstants()
    requires valAddrPage(d11, asp) && valAddrPage(d21, asp)
    requires valAddrPage(d11, atkr) && valAddrPage(d21, atkr)
    requires finalDispatcher(d11, dispPg)
    requires finalDispatcher(d21, dispPg)
    requires d11[dispPg].addrspace == asp && d21[dispPg].addrspace == asp
    requires asp != atkr
    requires finalDispatcher(d14, dispPg)
    requires finalDispatcher(d24, dispPg)
    requires valAddrPage(d14, atkr) && valAddrPage(d24, atkr);
    requires d14[dispPg].addrspace == asp && d24[dispPg].addrspace == asp;
    requires validEnclaveExecutionStep'(s11,d11,s14,d14,r1,rd1,dispPg,retToEnclave1)
    requires validEnclaveExecutionStep'(s21,d21,s24,d24,r2,rd2,dispPg,retToEnclave2)
    requires s14.conf.nondet == s24.conf.nondet 
    requires loweq_pdb(d14, d24, atkr)
    requires retToEnclave1 == retToEnclave2
    requires s14.conf.ex == s24.conf.ex;
    requires (s14.conf.ex == ExSVC) ==>
            s14.regs[R0] == s24.regs[R0];
    requires (s14.conf.ex == ExSVC && (s14.regs[R0] == KOM_SVC_EXIT ||
            s14.regs[R0] == KOM_SVC_MAP_DATA ||
            s14.regs[R0] == KOM_SVC_UNMAP_DATA ||
            s14.regs[R0] == KOM_SVC_INIT_L2PTABLE)) ==>
        s14.regs[R1] == s24.regs[R1]
    requires (s14.conf.ex == ExSVC && (s14.regs[R0] == KOM_SVC_MAP_DATA ||
              s14.regs[R0] == KOM_SVC_UNMAP_DATA ||
              s14.regs[R0] == KOM_SVC_INIT_L2PTABLE)) ==>
        s14.regs[R2] == s24.regs[R2]
    ensures  loweq_pdb(rd1, rd2, atkr)
    ensures  !retToEnclave1 ==> same_ret(r1, r2)
    ensures  retToEnclave1 ==> r1.conf.nondet == r2.conf.nondet
    ensures  valAddrPage(rd1, asp)  && valAddrPage(rd2, asp)
    ensures  valAddrPage(rd1, atkr) && valAddrPage(rd2, atkr)
    ensures finalDispatcher(rd1, dispPg) && finalDispatcher(rd2, dispPg)
    ensures  rd1[dispPg].addrspace == asp && rd2[dispPg].addrspace == asp
{
    if(retToEnclave1) {
        
        var (retRegs1, rd1') := svcHandled(s14, d14, dispPg);
        var (retRegs2, rd2') := svcHandled(s24, d24, dispPg);

        if(s14.conf.ex == ExSVC) { 
            lemma_svcHandled_conf_not_atkr(s14, d14, rd1',
                s24, d24, rd2', dispPg, asp, atkr);
        }

        reveal loweq_pdb();
        
        assert loweq_pdb(rd1', rd2', atkr);
        assert loweq_pdb(rd1, rd2, atkr);

        assert r1.conf.nondet == r2.conf.nondet by {
            assert s14.conf.nondet == s24.conf.nondet; 
        }
    } else {
        reveal ValidRegState();
        lemma_exceptionHandled_conf_not_atkr(
            s14, d14, rd1, r1.regs[R0], r1.regs[R1],
            s24, d24, rd2, r2.regs[R0], r2.regs[R1],
            dispPg, asp, atkr);
    }
}

lemma lemma_svcHandled_conf_not_atkr(s1: state, d1: PageDb, d1': PageDb,
                                    s2: state, d2: PageDb, d2': PageDb,
                                    dispPg: PageNr, asp: PageNr, atkr: PageNr)
    requires validPageDbs({d1, d1'}) && validDispatcherPage(d1, dispPg)
    requires validPageDbs({d2, d2'}) && validDispatcherPage(d2, dispPg)
    requires ValidState(s1) && mode_of_state(s1) != User
    requires ValidState(s2) && mode_of_state(s2) != User
    requires valAddrPage(d1, asp) && valAddrPage(d2, asp)
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
    requires finalDispatcher(d1, dispPg)
    requires finalDispatcher(d2, dispPg)
    requires d1[dispPg].addrspace == asp && d2[dispPg].addrspace == asp
    requires asp != atkr
    requires OperandContents(s1, OReg(R0)) == OperandContents(s2, OReg(R0));
    requires (s1.regs[R0] == KOM_SVC_EXIT ||
              s1.regs[R0] == KOM_SVC_MAP_DATA ||
              s1.regs[R0] == KOM_SVC_UNMAP_DATA ||
              s1.regs[R0] == KOM_SVC_INIT_L2PTABLE) ==>
        s1.regs[R1] == s2.regs[R1]
    requires (s1.regs[R0] == KOM_SVC_MAP_DATA ||
              s1.regs[R0] == KOM_SVC_UNMAP_DATA ||
              s1.regs[R0] == KOM_SVC_INIT_L2PTABLE) ==>
        s1.regs[R2] == s2.regs[R2]
    requires isReturningSvc(s1) && finalDispatcher(d1, dispPg)
    requires isReturningSvc(s2) && finalDispatcher(d2, dispPg)
    requires d1' == svcHandled(s1, d1, dispPg).1
    requires d2' == svcHandled(s2, d2, dispPg).1
    requires loweq_pdb(d1, d2, atkr)
    ensures loweq_pdb(d1', d2', atkr)
    ensures valAddrPage(d1', asp)  && valAddrPage(d2', asp)
    ensures valAddrPage(d1', atkr) && valAddrPage(d2', atkr)
    ensures finalDispatcher(d1', dispPg) && finalDispatcher(d2', dispPg)
    ensures  d1'[dispPg].addrspace == asp && d2'[dispPg].addrspace == asp
{

    reveal loweq_pdb();
    var addrspace := d1[dispPg].addrspace;
    var call := OperandContents(s1, OReg(R0));
    if( call  == KOM_SVC_ATTEST ) {
        assert d1' == d1;
        assert d2' == d2;
    } else if( call  == KOM_SVC_VERIFY_STEP0) {
        assert loweq_entry(d1'[dispPg].entry, d2'[dispPg].entry);
    } else if( call  == KOM_SVC_VERIFY_STEP1) {
        assert loweq_entry(d1'[dispPg].entry, d2'[dispPg].entry);
    } else if( call  == KOM_SVC_VERIFY_STEP2) {
        assert d1' == d1;
        assert d2' == d2;
    } else if( call == KOM_SVC_MAP_DATA) {
        var page, mapping := s1.regs[R1], s1.regs[R2];
        var (retDb1, retErr1) := svcMapData(d1, addrspace, page, mapping);
        var (retDb2, retErr2) := svcMapData(d2, addrspace, page, mapping);
        assert retErr1 == KOM_ERR_INVALID_PAGENO <==>
            retErr2 == KOM_ERR_INVALID_PAGENO;
        assert retErr1 == KOM_ERR_INVALID_MAPPING <==>
            retErr2 == KOM_ERR_INVALID_MAPPING;
        if(retErr1 == KOM_ERR_SUCCESS) {
            assert loweq_entry(d1'[page].entry, d2'[page].entry);

            var abs_mapping := wordToMapping(mapping);
            var l11 := d1[d1[addrspace].entry.l1ptnr].entry;
            var l12 := d2[d2[addrspace].entry.l1ptnr].entry;
            var l1pte1 := fromJust(l11.l1pt[abs_mapping.l1index]);
            var l1pte2 := fromJust(l12.l1pt[abs_mapping.l1index]);
            assert loweq_entry(d1'[l1pte1].entry, d2'[l1pte2].entry);
        }
    } else if( call == KOM_SVC_UNMAP_DATA) {
    } else if( call == KOM_SVC_INIT_L2PTABLE) {
        var e1 := svcHandled(s1, d1, dispPg).0.0;
        var e2 := svcHandled(s2, d2, dispPg).0.0;
        reveal validPageDb();
        assert e1 == KOM_ERR_INVALID_MAPPING <==> e2 == KOM_ERR_INVALID_MAPPING;
        assert e1 == KOM_ERR_INVALID_PAGENO <==> e2 == KOM_ERR_INVALID_PAGENO;
        assert e1 == KOM_ERR_ADDRINUSE <==> e2 == KOM_ERR_ADDRINUSE;
        var page := OperandContents(s1, OReg(R1));
        var l1index := OperandContents(s1, OReg(R2));
        if(e1 == KOM_ERR_SUCCESS) {
            // var l2pt := L2PTable(SeqRepeat(NR_L2PTES, NoMapping));
            // var d1 := updatePageEntry(d, page, l2pt);
            var l1ptnr := d1[addrspace].entry.l1ptnr;
            assert loweq_entry(d1'[page].entry, d2'[page].entry);
            assert loweq_entry(d1'[l1ptnr].entry, d2'[l1ptnr].entry);
            // var d2 := installL1PTEInPageDb(d1, l1ptnr, page, l1index);
        }
    } else {
    }
}

lemma lemma_exceptionHandled_conf_not_atkr(
    s14:state, d14:PageDb, rd1:PageDb, r01:word, r11:word,
    s24:state, d24:PageDb, rd2:PageDb, r02:word, r12:word,
    dispPg:PageNr, asp: PageNr, atkr: PageNr)
    requires validStates({s14, s24})
    requires validPageDbs({d14,d24,rd1,rd2})
    requires validDispatcherPage(d14, dispPg)
    requires validDispatcherPage(d24, dispPg)
    requires mode_of_state(s14) != User
    requires mode_of_state(s24) != User
    requires valAddrPage(d14, asp) && valAddrPage(d24, asp)
    requires valAddrPage(d14, atkr) && valAddrPage(d24, atkr)
    requires finalDispatcher(d14, dispPg)
    requires finalDispatcher(d24, dispPg)
    requires d14[dispPg].addrspace == asp && d24[dispPg].addrspace == asp
    requires asp != atkr
    requires (r01, r11, rd1) == exceptionHandled(s14, d14, dispPg)
    requires (r02, r12, rd2) == exceptionHandled(s24, d24, dispPg)
    requires s14.conf.ex == s24.conf.ex
    requires loweq_pdb(d14, d24, atkr)
    requires R1 in s14.regs && R1 in s24.regs
    requires s14.conf.ex.ExSVC? ==> 
        s14.regs[R1] == s24.regs[R1]
    ensures  loweq_pdb(rd1, rd2, atkr)
    ensures  r01 == r02 && r11 == r12
    ensures  valAddrPage(rd1, asp)  && valAddrPage(rd2, asp)
    ensures  valAddrPage(rd1, atkr) && valAddrPage(rd2, atkr)
    ensures  finalDispatcher(rd1, dispPg) && finalDispatcher(rd2, dispPg)
    ensures  rd1[dispPg].addrspace == asp && rd2[dispPg].addrspace == asp
{
    reveal loweq_pdb();
}

//-----------------------------------------------------------------------------
// Executions of attacker conflaves beginning from low-equiv states produce 
// low-equiv states.
//-----------------------------------------------------------------------------


// AF: This one seems a bit unstable, but at minimum it works with DAFNYPROC
lemma {:timeLimitMultiplier 2}
lemma_enter_conf_atkr_enter(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                 s2: state, d2: PageDb, s2':state, d2': PageDb,
                                 dispPg: word, arg1: word, arg2: word, arg3: word,
                                 atkr: PageNr, isresume:bool)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires !isresume ==> smc_enter(s1, d1, s1', d1', dispPg, arg1, arg2, arg3)
    requires !isresume ==> smc_enter(s2, d2, s2', d2', dispPg, arg1, arg2, arg3)
    requires isresume ==> smc_resume(s1, d1, s1', d1', dispPg)
    requires isresume ==> smc_resume(s2, d2, s2', d2', dispPg)
    requires conf_loweq(s1, d1, s2, d2, atkr)
    requires entering_obs(d1, d2, dispPg, atkr, isresume);
    requires s1.conf.nondet == s2.conf.nondet
    ensures  loweq_pdb(d1', d2', atkr)
    ensures  same_ret(s1', s2')
    ensures  InsecureMemInvariant(s1', s2')
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
        lemma_validEnclaveEx_conf(s11, d1, s1', d1', s21, d2, s2', d2',
                                             dispPg, steps1, steps2, atkr);
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
        lemma_validEnclaveEx_conf(s11, d1, s1', d1', s21, d2, s2', d2',
                                             dispPg, steps1, steps2, atkr);
    }
}

lemma lemma_validEnclaveEx_conf(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                    s2: state, d2: PageDb, s2':state, d2': PageDb,
                                    dispPg: PageNr, steps1:nat, steps2:nat,
                                    atkr: PageNr)
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') && SaneConstants()
    requires obs_entry(d1, d2, dispPg, atkr)
    requires validEnclaveExecution(s1, d1, s1', d1', dispPg, steps1)
    requires validEnclaveExecution(s2, d2, s2', d2', dispPg, steps2);
    requires loweq_pdb(d1, d2, atkr)
    requires InsecureMemInvariant(s1, s2)
    requires s1.conf.nondet == s2.conf.nondet
    requires OperandContents(s1, OLR) == OperandContents(s2, OLR)
    requires user_regs(s1.regs) == user_regs(s2.regs)
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires !spsr_of_state(s1).f && !spsr_of_state(s1).i
    requires !spsr_of_state(s2).f && !spsr_of_state(s2).i
    requires spsr_same(s1, s2)
    requires s1.conf.scr == s2.conf.scr;
    ensures  obs_entry(d1', d2', dispPg, atkr)
    ensures  loweq_pdb(d1', d2', atkr)
    ensures InsecureMemInvariant(s1', s2')
    ensures same_ret(s1', s2')
    decreases steps1, steps2
{
    reveal validEnclaveExecution();

    var retToEnclave1, s15, d15 := lemma_unpack_validEnclaveExecution(
        s1, d1, s1', d1', dispPg, steps1);
    var retToEnclave2, s25, d25 := lemma_unpack_validEnclaveExecution(
        s2, d2, s2', d2', dispPg, steps2);

    lemma_validEnclaveExecutionStep_validPageDb(s1, d1, s15, d15, dispPg, retToEnclave1);
    lemma_validEnclaveExecutionStep_validPageDb(s2, d2, s25, d25, dispPg, retToEnclave2);
    lemma_validEnclaveStep_conf(s1, d1, s15, d15, s2, d2, s25, d25,
        dispPg, atkr, retToEnclave1, retToEnclave2);

    assert retToEnclave1 == retToEnclave2;

    if(retToEnclave1) {
        lemma_validEnclaveExecution(s15, d15, s1', d1', dispPg, steps1 - 1);
        lemma_validEnclaveExecution(s25, d25, s2', d2', dispPg, steps2 - 1);
        lemma_validEnclaveEx_conf(s15, d15, s1', d1', s25, d25, s2', d2',
                                         dispPg, steps1 - 1, steps2 - 1, atkr);
        assert loweq_pdb(d1', d2', atkr);
    } else {
        assert s2' == s25;
        assert s1' == s15;
        assert d1' == d15;
        assert d2' == d25;
        assert loweq_pdb(d1', d2', atkr);
    }

}

lemma lemma_validEnclaveStep_conf(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                      s2: state, d2: PageDb, s2':state, d2': PageDb,
                                      dispPage:PageNr, atkr: PageNr, ret1:bool, ret2:bool)
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') && SaneConstants()
    requires obs_entry(d1, d2, dispPage, atkr)
    requires validEnclaveExecutionStep(s1, d1, s1', d1', dispPage, ret1);
    requires validEnclaveExecutionStep(s2, d2, s2', d2', dispPage, ret2);
    requires loweq_pdb(d1, d2, atkr)
    requires InsecureMemInvariant(s1, s2)
    requires s1.conf.nondet == s2.conf.nondet
    requires OperandContents(s1, OLR) == OperandContents(s2, OLR)
    requires user_regs(s1.regs) == user_regs(s2.regs)
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires spsr_same(s1, s2)
    requires s1.conf.scr == s2.conf.scr;
    ensures  InsecureMemInvariant(s1', s2')
    ensures  obs_entry(d1', d2', dispPage, atkr)
    ensures  loweq_pdb(d1', d2', atkr)
    ensures  ret1 == ret2
    ensures  ret1 ==> s1'.conf.scr == s2'.conf.scr;
    ensures  ret1 ==> s1'.conf.nondet == s2'.conf.nondet
    ensures  ret1 ==> OperandContents(s1', OLR) == OperandContents(s2', OLR)
    ensures  ret1 ==> user_regs(s1'.regs) == user_regs(s2'.regs)
    ensures  !ret1 ==> same_ret(s1', s2')
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
    lemma_validEnclaveStepPrime_conf(
        s1, d1, s14, d14, s1', d1',
        s2, d2, s24, d24, s2', d2',
        dispPage, ret1, ret2, atkr);
}


lemma lemma_preEntryUserRegs(
    s1:state, s1':state, ret1:SvcReturnRegs, rd1:PageDb,
    s2:state, s2':state, ret2:SvcReturnRegs, rd2:PageDb,
    disp:PageNr
)
    requires ValidState(s1) && ValidState(s1')
    requires ValidState(s2) && ValidState(s2')
    requires user_regs(s1.regs) == user_regs(s2.regs)
    requires ret1 == ret2 
    requires preEntryReturn(s1, s1', ret1, rd1, disp)
    requires preEntryReturn(s2, s2', ret2, rd2, disp)
    ensures  user_regs(s1'.regs) == user_regs(s2'.regs)
{
    assert s1'.regs[R0] == s2'.regs[R0];
    assert s1'.regs[R1] == s2'.regs[R1];
    assert s1'.regs[R2] == s2'.regs[R2];
    assert s1'.regs[R3] == s2'.regs[R3];
    assert s1'.regs[R4] == s2'.regs[R4];
    assert s1'.regs[R5] == s2'.regs[R5];
    assert s1'.regs[R6] == s2'.regs[R6];
    assert s1'.regs[R7] == s2'.regs[R7];
    assert s1'.regs[R8] == s2'.regs[R8];
    forall( r | r in {R9, R10, R11, R12, LR(User), SP(User)} )
        ensures s1.regs[r] == s2.regs[r]
    {
        assert r in USER_REGS();
        assert user_regs(s1.regs) == user_regs(s2.regs);
        assert user_regs(s1.regs)[r] == user_regs(s2.regs)[r];
    }
    assert s1'.regs[R9] == s2'.regs[R9];
    assert s1'.regs[R10] == s2'.regs[R10];
    assert s1'.regs[R11] == s2'.regs[R11];
    assert s1'.regs[R12] == s2'.regs[R12];
    assert s1'.regs[LR(User)] == s2'.regs[LR(User)];
    assert s1'.regs[SP(User)] == s2'.regs[SP(User)];
}

lemma lemma_eval_cpsrs(
s11: state, s1':state, s12: state, 
s21: state, s2':state, s22: state)
    requires ValidState(s11) && ValidState(s12) && ValidState(s1')
    requires ValidState(s21) && ValidState(s22) && ValidState(s2')
    requires equivStates(s11, s1') && evalEnterUserspace(s1', s12)
    requires equivStates(s21, s2') && evalEnterUserspace(s2', s22)
    requires mode_of_state(s11) != User && mode_of_state(s21) != User
    requires spsr_same(s11, s21)
    ensures  cpsr_same(s12, s22)
{
    assert equivStates(s11, s1') && evalEnterUserspace(s1', s12);
    assert equivStates(s21, s2') && evalEnterUserspace(s2', s22);
    var (m1, m2) := (mode_of_state(s1'), mode_of_state(s2'));
    var (spsr1, spsr2) := (OSReg(spsr(m1)), OSReg(spsr(m2)));
    assert OperandContents(s1', spsr1) == OperandContents(s2', spsr2);
    var (spsr1v, spsr2v) :=
        (OperandContents(s1', spsr1), OperandContents(s2', spsr2));
    assert evalUpdate(takestep(s1'), OSReg(cpsr), spsr1v, s12);
    assert evalUpdate(takestep(s2'), OSReg(cpsr), spsr2v, s22);
}

lemma lemma_svcHandled_loweq_pdb(
    s1: state, d1: PageDb, d1': PageDb,
    s2: state, d2: PageDb, d2': PageDb, dispPg: PageNr, atkr: PageNr)
    requires 
        validPageDb(d1) &&
        validPageDb(d2) &&
        validPageDb(d1') &&
        validPageDb(d2') &&
        validDispatcherPage(d1, dispPg) &&
        validDispatcherPage(d2, dispPg)
    requires ValidState(s1) && mode_of_state(s1) != User
    requires ValidState(s2) && mode_of_state(s2) != User
    requires isReturningSvc(s1) && isReturningSvc(s2)
    requires finalDispatcher(d1, dispPg) && finalDispatcher(d2, dispPg)
    requires d1' == svcHandled(s1, d1, dispPg).1 
    requires d2' == svcHandled(s2, d2, dispPg).1
    requires user_regs(s1.regs) == user_regs(s2.regs)
    requires s1.rng.entropy == s2.rng.entropy
    requires obs_entry(d1, d2, dispPg, atkr)
    requires loweq_pdb(d1, d2, atkr)
    ensures  obs_entry(d1', d2', dispPg, atkr)
    ensures  loweq_pdb(d1', d2', atkr)
    ensures  svcHandled(s1, d1, dispPg).0 == svcHandled(s2, d2, dispPg).0
{

    var call := OperandContents(s1, OReg(R0));
    var user_words1 := [s1.regs[R1], s1.regs[R2], s1.regs[R3], s1.regs[R4],
        s1.regs[R5], s1.regs[R6], s1.regs[R7], s1.regs[R8]];
    var user_words2 := [s2.regs[R1], s2.regs[R2], s2.regs[R3], s2.regs[R4],
        s2.regs[R5], s2.regs[R6], s2.regs[R7], s2.regs[R8]];

    assert user_words1 == user_words2 by {
        assert R1 in USER_REGS();
        assert R2 in USER_REGS();
        assert R3 in USER_REGS();
        assert R4 in USER_REGS();
        assert R5 in USER_REGS();
        assert R6 in USER_REGS();
        assert R7 in USER_REGS();
        assert R8 in USER_REGS();
        assert R1 in user_regs(s1.regs);
        assert R1 in user_regs(s2.regs);
        assert R2 in user_regs(s1.regs);
        assert R2 in user_regs(s2.regs);
        assert R3 in user_regs(s1.regs);
        assert R3 in user_regs(s2.regs);
        assert R4 in user_regs(s1.regs);
        assert R4 in user_regs(s2.regs);
        assert R5 in user_regs(s1.regs);
        assert R5 in user_regs(s2.regs);
        assert R6 in user_regs(s1.regs);
        assert R6 in user_regs(s2.regs);
        assert R7 in user_regs(s1.regs);
        assert R7 in user_regs(s2.regs);
        assert R8 in user_regs(s1.regs);
        assert R8 in user_regs(s2.regs);
        // There's no good ascii version of upside-down face emoji,
        // but if there was, it would go here.
    }
    var retRegs1 := svcHandled(s1, d1, dispPg).0;
    var retRegs2 := svcHandled(s2, d2, dispPg).0;
    lemma_svcHandled_validPageDb(s1, d1, dispPg, retRegs1, d1');
    lemma_svcHandled_validPageDb(s2, d2, dispPg, retRegs2, d2');

    assert OperandContents(s1, OReg(R0)) ==
        OperandContents(s2, OReg(R0)) by {
           assert R0 in USER_REGS(); 
           assert R0 in user_regs(s1.regs);
           assert R0 in user_regs(s2.regs);
        }
    if( call  == KOM_SVC_ATTEST ) {
        assert d1' == d1;
        assert d2' == d2;
        reveal loweq_pdb();
    } else if( call == KOM_SVC_VERIFY_STEP0 || call  == KOM_SVC_VERIFY_STEP1 ) {
        assert d1[dispPg].entry == d2[dispPg].entry &&
            d1'[dispPg].entry == d2'[dispPg].entry &&
            d1'[dispPg].addrspace == d2'[dispPg].addrspace by {
            reveal loweq_pdb();
        }
        forall (n: PageNr | n != dispPg )
            ensures d1'[n] == d1[n]
            ensures d2'[n] == d2[n] 
            ensures pgInAddrSpc(d1, n, atkr) ==> 
                pgInAddrSpc(d1', n, atkr)
            ensures pgInAddrSpc(d2, n, atkr) ==> 
                pgInAddrSpc(d2', n, atkr)
            {
                assert loweq_pdb(d1, d2, atkr);
                if(d1[n].PageDbEntryTyped? && d1[n].addrspace == atkr){
                    assert d1'[n].PageDbEntryTyped? &&
                        d1'[n].addrspace == atkr;
                }
                reveal loweq_pdb();
            }

        reveal loweq_pdb();
        assert loweq_pdb(d1', d2', atkr);
        assert user_words1 == user_words2;
    } else if( call == KOM_SVC_VERIFY_STEP2) {
        var dummy:word := 0;
        var hmac1 := svcHmacVerify(s1, d1, dispPg);
        var hmac2 := svcHmacVerify(s2, d2, dispPg);
        assert hmac1 == hmac2 by { reveal loweq_pdb(); }
        var ok := if user_words1 == hmac1 then 1 else 0;
        assert retRegs1 == (KOM_ERR_SUCCESS, ok, dummy, dummy, dummy, dummy, 
            dummy, dummy, dummy);
        assert retRegs2 == (KOM_ERR_SUCCESS, ok, dummy, dummy, dummy, dummy, 
            dummy, dummy, dummy);
        assert retRegs1 == retRegs2;
        assert d1' == d1;
        assert d2' == d2;
        reveal loweq_pdb();
    } else if (call == KOM_SVC_MAP_DATA) {
        reveal loweq_pdb();
    } else if (call == KOM_SVC_UNMAP_DATA) {
        reveal loweq_pdb();
    } else if (call == KOM_SVC_INIT_L2PTABLE) {
        reveal loweq_pdb();
    } else if (call == KOM_SVC_GET_RANDOM) {
        reveal loweq_pdb();
    } else {
        assert d1' == d1;
        assert d2' == d2;
        reveal loweq_pdb();
    }
}

lemma lemma_userspaceExecutionFn_loweq(
s12: state, pc1:word, expc1:word, ex1:exception, s13:state,
s22: state, pc2:word, expc2:word, ex2:exception, s23:state)
    requires ValidState(s12) && ValidState(s13) && ValidState(s22) && 
        ValidState(s23)
    requires mode_of_state(s12) == User && mode_of_state(s22) == User
    requires ExtractAbsPageTable(s12).Just? && ExtractAbsPageTable(s22).Just?
    requires (s13, expc1, ex1) == userspaceExecutionFn(s12, pc1)
    requires (s23, expc2, ex2) == userspaceExecutionFn(s22, pc2)
    requires InsecureMemInvariant(s12, s22)
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
    ensures  InsecureMemInvariant(s13, s23)
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
lemma_validEnclaveStepPrime_conf(
s11: state, d11: PageDb, s14:state, d14:PageDb, r1:state, rd1:PageDb,
s21: state, d21: PageDb, s24:state, d24:PageDb, r2:state, rd2:PageDb,
dispPg:PageNr, retToEnclave1:bool, retToEnclave2:bool, atkr: PageNr
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
    requires obs_entry(d11, d21, dispPg, atkr)
    requires validEnclaveExecutionStep'(s11,d11,s14,d14,r1,rd1,dispPg,retToEnclave1)
    requires validEnclaveExecutionStep'(s21,d21,s24,d24,r2,rd2,dispPg,retToEnclave2)
    requires OperandContents(s11, OLR) == OperandContents(s21, OLR)
    requires user_regs(s11.regs) == user_regs(s21.regs)
    requires InsecureMemInvariant(s11, s21)
    requires loweq_pdb(d11, d21, atkr)
    requires s11.conf.nondet == s21.conf.nondet
    requires mode_of_state(s11) != User && mode_of_state(s21) != User
    requires spsr_same(s11, s21)
    requires s11.conf.scr == s21.conf.scr;
    ensures  obs_entry(rd1, rd2, dispPg, atkr)
    ensures  loweq_pdb(rd1, rd2, atkr)
    ensures  InsecureMemInvariant(r1, r2)
    ensures  retToEnclave1 == retToEnclave2
    ensures  !retToEnclave1 ==> same_ret(r1, r2)
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
        lemma_eqpdb_pt_coresp(d11, d21, s12, s22, l1p, atkr);
    }
    lemma_userStatesEquiv_atkr(
        s11, s1', s12, s14, pc1, pt1, d11,
        s21, s2', s22, s24, pc2, pt2, d21,
        dispPg, atkr, l1p);

    lemma_userspaceExecutionFn_loweq(
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
        dispPg, atkr, l1p);

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
            s24, d24, rd2, dispPg, atkr);

        assert r1.conf.nondet == r2.conf.nondet by {
            assert s14.conf.nondet == s24.conf.nondet; 
        }
        assert loweq_pdb(rd1, rd2, atkr);
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
             dispPg, atkr);

        assert loweq_pdb(rd1, rd2, atkr);
    }
}

lemma lemma_exceptionTaken_atkr(
    s13: state, s14: state, ex1:exception, pc1:word,
    s23: state, s24: state, ex2:exception, pc2:word
)
    requires ValidState(s13) && ValidState(s23) &&
        ValidState(s14) && ValidState(s24);
    requires user_regs(s13.regs) == user_regs(s23.regs)
    requires ex1 == ex2 && pc1 == pc2
    requires cpsr in s13.sregs && cpsr in s23.sregs &&
        s13.sregs[cpsr] == s23.sregs[cpsr]
    requires mode_of_exception(s13.conf, ex1) ==
        mode_of_exception(s23.conf, ex2)
    requires ValidPsrWord(psr_of_exception(s13, ex1))
    requires ValidPsrWord(psr_of_exception(s23, ex2))
    requires s14 == exceptionTakenFn(s13, ex1, pc1)
    requires s24 == exceptionTakenFn(s23, ex2, pc2)
    ensures user_regs(s14.regs) == user_regs(s24.regs)
    ensures mode_of_state(s14) != User && mode_of_state(s24) != User
    ensures mode_of_state(s14) == mode_of_state(s24)
    ensures lr_spsr_same(s14, s24);
{
    assert user_regs(s14.regs) == user_regs(s24.regs) by {
        var newmode := mode_of_exception(s13.conf, ex1);
        assert s14.regs == s13.regs[LR(newmode) := pc1];
        assert s24.regs == s23.regs[LR(newmode) := pc1];
        assert forall r :: r in user_regs(s14.regs) <==> r in user_regs(s24.regs);
        assert forall r :: r in user_regs(s14.regs) <==> r in user_regs(s13.regs);
        forall( r | r in user_regs(s14.regs)) 
            ensures user_regs(s24.regs) == user_regs(s14.regs)
        {
            assert user_regs(s13.regs) == user_regs(s23.regs);
            if(r != LR(newmode)) {
                assert s14.regs[r] == s13.regs[r];
                assert s24.regs[r] == s23.regs[r];
                assert s13.regs[r] == s23.regs[r];
            } else {
            }
        }
        eqregs(user_regs(s24.regs), user_regs(s14.regs));
    }
    lemma_evalExceptionTaken_Mode(s13, ex1, pc1, s14);
}

// This is just for the reveal
predicate lr_spsr_same(s1:state, s2:state)
    requires ValidState(s1) && ValidState(s2)
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
{
    reveal ValidRegState();
    reveal ValidSRegState();
    s1.regs[LR(mode_of_state(s1))] == s2.regs[LR(mode_of_state(s2))] &&
    s1.sregs[spsr(mode_of_state(s1))] == s2.sregs[spsr(mode_of_state(s2))]
}

lemma lemma_exceptionHandled_atkr(
s1: state, d1: PageDb, d1': PageDb, s2: state, d2: PageDb, d2': PageDb,
r01: word, r11: word, r02: word, r12: word,
dispPg: PageNr, atkr: PageNr)
    requires ValidState(s1) && ValidState(s2) &&
             validPageDb(d1') && validPageDb(d2') &&
             validPageDb(d1) && validPageDb(d2) && SaneConstants()
    requires s1.conf.nondet == s2.conf.nondet;
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires mode_of_state(s1) == mode_of_state(s2)
    requires lr_spsr_same(s1, s2)
    requires validDispatcherPage(d1, dispPg) && validDispatcherPage(d2, dispPg) 
    requires (r01, r11, d1') == exceptionHandled(s1, d1, dispPg)
    requires (r02, r12, d2') == exceptionHandled(s2, d2, dispPg)
    requires obs_entry(d1, d2, dispPg, atkr)
    requires loweq_pdb(d1, d2, atkr)
    requires user_regs(s1.regs) == user_regs(s2.regs)
    requires s1.conf.ex == s2.conf.ex
    ensures  loweq_pdb(d1', d2', atkr)
    ensures  obs_entry(d1', d2', dispPg, atkr)
    ensures  r01 == r02 && r11 == r12
{
    reveal loweq_pdb();
    var ex := s1.conf.ex;
    forall (n : PageNr |  n != dispPg)
        ensures d1'[n] == d1[n];
        ensures d2'[n] == d2[n];
        ensures pgInAddrSpc(d1, n, atkr) <==>
            pgInAddrSpc(d1', n, atkr)
        ensures pgInAddrSpc(d2, n, atkr) <==>
            pgInAddrSpc(d2', n, atkr)
    {
    }

    assert forall n : PageNr :: pgInAddrSpc(d1, n, atkr) <==>
        pgInAddrSpc(d2, n, atkr);

    forall( n : PageNr | n != dispPg &&
        pgInAddrSpc(d1, n, atkr) )
    ensures d1'[n] == d2'[n]
    {
    }

    if( ex.ExSVC? ) {
        assert d1'[dispPg].entry == d2'[dispPg].entry;
        assert r01 == r02;
        assert R1 in USER_REGS();
        assert user_regs(s1.regs)[R1] == user_regs(s2.regs)[R1];
        assert s1.regs[R1] == s2.regs[R1];
        assert r11 == r12;
    } else if( ex.ExAbt? || ex.ExUnd? ) {
        assert d1'[dispPg].entry == d2'[dispPg].entry;
        assert r01 == r02;
        assert r11 == r12;
    } else {
        var pc1 := TruncateWord(OperandContents(s1, OLR) - 4);
        var pc2 := TruncateWord(OperandContents(s2, OLR) - 4);
        assert pc1 == pc2;
        reveal ValidSRegState();
        var psr1 := s1.sregs[spsr(mode_of_state(s1))];
        var psr2 := s2.sregs[spsr(mode_of_state(s2))];
        assert psr1 == psr2;
        var ctxt1' := DispatcherContext(user_regs(s1.regs), pc1, psr1);
        var ctxt2' := DispatcherContext(user_regs(s2.regs), pc2, psr2);
        assert user_regs(s1.regs) == user_regs(s2.regs);
        assert ctxt1' == ctxt2';
        assert d1'[dispPg].entry == d2'[dispPg].entry;
    }
}

lemma
    {:fuel userspaceExecutionAndException', 0}
    {:fuel ExtractAbsPageTable, 0}
    {:fuel l1pOfDispatcher, 0}
lemma_userMemEquiv_atkr(
s11: state, s1':state, s12: state, s14: state,
pc1: word, pt1: Maybe<AbsPTable>, d1: PageDb,
s21: state, s2':state, s22: state, s24: state,
pc2: word, pt2: Maybe<AbsPTable>, d2: PageDb,
dispPg: PageNr, atkr: PageNr, l1p: PageNr)
    requires ValidState(s11) && ValidState(s12) && ValidState(s14)
    requires ValidState(s21) && ValidState(s22) && ValidState(s24)
    requires validPageDb(d1) && validPageDb(d2)
    requires SaneConstants()
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
    requires loweq_pdb(d1, d2, atkr)
    requires s12.conf.nondet == s22.conf.nondet
    requires userspaceExecutionAndException'(s11, s1', s12, s14)
    requires userspaceExecutionAndException'(s21, s2', s22, s24)
    requires pc1 == OperandContents(s11, OLR) && pc2 == OperandContents(s21, OLR);
    requires pt1 == ExtractAbsPageTable(s12) && pt2 == ExtractAbsPageTable(s22);
    requires nonStoppedL1(d1, l1p) && nonStoppedL1(d2, l1p)
    requires obs_entry(d1, d2, dispPg, atkr)
    requires l1pOfDispatcher(d1, dispPg) == l1pOfDispatcher(d2, dispPg) == l1p
    requires !stoppedAddrspace(d1[atkr]) && !stoppedAddrspace(d2[atkr])
    requires user_regs(s11.regs) == user_regs(s21.regs);
    requires pc1 == pc2;
    requires 
        pageTableCorresponds(s12, d1, l1p) &&
        pageTableCorresponds(s22, d2, l1p) &&
        dataPagesCorrespond(s12.m, d1) &&
        dataPagesCorrespond(s22.m, d2)
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
        && d1[atkr].entry.l1ptnr == d2[atkr].entry.l1ptnr == l1p
    requires pgInAddrSpc(d1, l1p, atkr) && pgInAddrSpc(d2, l1p, atkr)
    ensures pt1.Just? && pt2.Just?
    ensures user_mem(pt1.v, s12.m) == user_mem(pt2.v, s22.m)
{
    assert pt1.Just? && pt2.Just?
        && ExtractAbsPageTable(s11).Just?
        && ExtractAbsPageTable(s21).Just? by
    {
        assert{:fuel ExtractAbsPageTable, 1}{:fuel userspaceExecutionAndException', 1}
            pt1.Just? && pt2.Just?;
        assert{:fuel userspaceExecutionAndException', 1}
            ExtractAbsPageTable(s11).Just? && ExtractAbsPageTable(s21).Just? by 
            {
                assert evalUserExecution(s1', s12, s14) &&
                    evalUserExecution(s2', s22, s24);
                assert ExtractAbsPageTable(s12).Just? &&
                    ExtractAbsPageTable(s22).Just?;
                assert {:fuel ExtractAbsPageTable, 1}
                    ExtractAbsPageTable(s1').Just? && 
                        ExtractAbsPageTable(s2').Just?;
                assert {:fuel ExtractAbsPageTable, 1}
                    ExtractAbsPageTable(s11).Just? &&
                        ExtractAbsPageTable(s21).Just?;
            }
    }

    lemma_eqpdb_pt_coresp(d1, d2, s12, s22, l1p, atkr);

    forall a:addr | ValidMem(a) && addrIsSecure(a)
            && PageBase(a) in AllPagesInTable(pt1.v)
        ensures a in s12.m.addresses
        ensures a in s22.m.addresses
        ensures s12.m.addresses[a] == s22.m.addresses[a]
    {
        lemma_data_eqpdb_to_addrs(d1, d2, s12, s22, a, atkr, l1p);
    }
}

lemma lemma_userStatesEquiv_atkr(
s11: state, s1':state, s12: state, s14: state,
pc1: word, pt1: Maybe<AbsPTable>, d1: PageDb,
s21: state, s2':state, s22: state, s24: state,
pc2: word, pt2: Maybe<AbsPTable>, d2: PageDb,
dispPg: PageNr, atkr: PageNr, l1p: PageNr)
    requires ValidState(s11) && ValidState(s12) && ValidState(s14)
    requires ValidState(s21) && ValidState(s22) && ValidState(s24)
    requires validPageDb(d1) && validPageDb(d2)
    requires SaneConstants()
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
    requires loweq_pdb(d1, d2, atkr)
    requires s12.conf.nondet == s22.conf.nondet
    requires userspaceExecutionAndException'(s11, s1', s12, s14)
    requires userspaceExecutionAndException'(s21, s2', s22, s24)
    requires pc1 == OperandContents(s11, OLR) && pc2 == OperandContents(s21, OLR);
    requires pt1 == ExtractAbsPageTable(s12) && pt2 == ExtractAbsPageTable(s22);
    requires nonStoppedL1(d1, l1p) && nonStoppedL1(d2, l1p)
    requires obs_entry(d1, d2, dispPg, atkr)
    requires l1pOfDispatcher(d1, dispPg) == l1pOfDispatcher(d2, dispPg) == l1p
    requires !stoppedAddrspace(d1[atkr]) && !stoppedAddrspace(d2[atkr])
    requires user_regs(s11.regs) == user_regs(s21.regs);
    requires pc1 == pc2;
    requires 
        pageTableCorresponds(s12, d1, l1p) &&
        pageTableCorresponds(s22, d2, l1p) &&
        dataPagesCorrespond(s12.m, d1) &&
        dataPagesCorrespond(s22.m, d2)
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
        && d1[atkr].entry.l1ptnr == d2[atkr].entry.l1ptnr == l1p
    requires pgInAddrSpc(d1, l1p, atkr) && pgInAddrSpc(d2, l1p, atkr)
    ensures pt1.Just? && pt2.Just?
    ensures  user_visible_state(s12, pc1, pt1.v) == user_visible_state(s22, pc2, pt2.v)
{
    lemma_userMemEquiv_atkr(
        s11, s1', s12, s14, pc1, pt1, d1,
        s21, s2', s22, s24, pc2, pt2, d2,
        dispPg, atkr, l1p);
}


// TODO: move this to ptables.i.dfy, next to lemma_WritablePages
lemma lemma_AllPages(d:PageDb, l1p:PageNr, pagebase:addr, pt:PageNr)
    requires PhysBase() == KOM_DIRECTMAP_VBASE
    requires validPageDb(d)
    requires nonStoppedL1(d, l1p)
    requires PageAligned(pagebase) && address_is_secure(pagebase)
    requires pt == monvaddr_page(pagebase)
    requires pagebase in AllPagesInTable(mkAbsPTable(d, l1p))
    ensures d[pt].PageDbEntryTyped?;
    ensures d[pt].entry.DataPage?;
    ensures d[pt].addrspace == d[l1p].addrspace;
{
    assert validL1PTable(d, d[l1p].addrspace, d[l1p].entry.l1pt) by { reveal validPageDb(); }
    var abspt := mkAbsPTable(d, l1p);
    var l1pt := d[l1p].entry.l1pt;
    var i, j :| 0 <= i < ARM_L1PTES && 0 <= j < ARM_L2PTES
        && abspt[i].Just? && abspt[i].v[j].Just?
        && pagebase == abspt[i].v[j].v.phys + PhysBase();
    var p := monvaddr_page(pagebase);
    reveal mkAbsPTable();
    assert p == (abspt[i].v[j].v.phys - SecurePhysBase()) / PAGESIZE;
    var n := i / 4;
    assert l1pt[n].Just?;
    var l2p := l1pt[n].v;
    assert d[l2p].PageDbEntryTyped? && d[l2p].entry.L2PTable?
        && wellFormedPageDbEntry(d[l2p])
        && validL2PTable(d, d[l2p].addrspace, d[l2p].entry.l2pt)
        by { reveal validPageDb(); }
    var l2pt := d[l2p].entry.l2pt;
    var pte := l2pt[(i%4)*ARM_L2PTES + j];
    assert validL2PTE(d, d[l2p].addrspace, pte);
    assert mkAbsPTE(pte) == abspt[i].v[j];
    assert pte.SecureMapping?;
}

lemma lemma_data_eqpdb_to_addrs( d1:PageDb, d2:PageDb, s1: state, s2: state,
a:addr, atkr:PageNr, l1p: PageNr)
    requires validPageDb(d1) && validPageDb(d2)
    requires ValidState(s1) && ValidState(s2) && SaneConstants()
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
    requires loweq_pdb(d1, d2, atkr)
    requires dataPagesCorrespond(s1.m, d1) && dataPagesCorrespond(s2.m, d2)
    requires ExtractAbsPageTable(s1).Just?
    requires ExtractAbsPageTable(s2).Just?
    requires ValidMem(a)
    requires addrIsSecure(a)
    requires PageBase(a) in AllPagesInTable(ExtractAbsPageTable(s1).v)
    requires PageBase(a) in AllPagesInTable(ExtractAbsPageTable(s2).v)
    requires nonStoppedL1(d1, l1p) && nonStoppedL1(d2, l1p)
    requires pgInAddrSpc(d1, l1p, atkr) && pgInAddrSpc(d2, l1p, atkr)
    requires pageTableCorresponds(s1, d1, l1p)
    requires pageTableCorresponds(s2, d2, l1p)
    ensures a in s1.m.addresses
    ensures a in s2.m.addresses
    ensures s1.m.addresses[a] == s2.m.addresses[a]
{
    var p := lemma_secure_addrInPage(a);

    assert PageBase(a) in AllPagesInTable(mkAbsPTable(d1, l1p))
        && PageBase(a) in AllPagesInTable(mkAbsPTable(d2, l1p)) by
        { reveal pageTableCorresponds(); }

    lemma_AllPages(d1, l1p, PageBase(a), monvaddr_page(PageBase(a)));
    lemma_AllPages(d2, l1p, PageBase(a), monvaddr_page(PageBase(a)));

    assert a in addrsInPage(p, page_monvaddr(p)) by
    {
        var a0 := page_monvaddr(p);
        var a1 := a0 + PAGESIZE;
        var i := (a - a0) / WORDSIZE;
        assert addrRangeSeq(a0, a1)[i] == a0 + WordsToBytes(i);
    }
    lemma_data_page_eqdb_to_addrs(d1, d2, s1, s2, p, a, atkr);
}

lemma lemma_data_page_eqdb_to_addrs( d1:PageDb, d2:PageDb, s1: state, s2: state,
n:PageNr, a:addr, atkr:PageNr)
    requires validPageDb(d1) && validPageDb(d2)
    requires ValidState(s1) && ValidState(s2) && SaneConstants()
    requires d1[n].PageDbEntryTyped? && d1[n].entry.DataPage?
    requires d2[n].PageDbEntryTyped? && d2[n].entry.DataPage?
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
    requires d1[n].addrspace == atkr && d2[n].addrspace == atkr
    requires loweq_pdb(d1, d2, atkr)
    requires a in addrsInPage(n, page_monvaddr(n))
    requires dataPagesCorrespond(s1.m, d1) && dataPagesCorrespond(s2.m, d2)
    ensures s1.m.addresses[a] == s2.m.addresses[a]
{
    reveal loweq_pdb();
    reveal pageDbDataCorresponds();

    // trigger i in pageDbDataCorresponds:
    var i := (a - page_monvaddr(n)) / WORDSIZE;
    assert d1[n].entry.contents[i] == d2[n].entry.contents[i];
}

lemma lemma_eqpdb_pt_coresp(d1: PageDb, d2: PageDb, s1: state, s2: state,
l1p:PageNr, atkr: PageNr)
    requires validPageDb(d1) && validPageDb(d2)
    requires ValidState(s1) && ValidState(s2)
    requires ValidState(s1) && ValidState(s2) && SaneConstants()
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
    requires !stoppedAddrspace(d1[atkr]) && !stoppedAddrspace(d2[atkr])
    requires loweq_pdb(d1, d2, atkr)
    requires nonStoppedL1(d1, l1p) && nonStoppedL1(d2, l1p)
    requires pageTableCorresponds(s1, d1, l1p)
    requires pageTableCorresponds(s2, d2, l1p)
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
        && d1[atkr].entry.l1ptnr == d2[atkr].entry.l1ptnr == l1p
    requires pgInAddrSpc(d1, l1p, atkr) && pgInAddrSpc(d2, l1p, atkr)
    ensures  ExtractAbsPageTable(s1) == ExtractAbsPageTable(s2)
{
    reveal pageTableCorresponds();
    assert mkAbsPTable(d1, l1p) == mkAbsPTable(d2, l1p) by {
        reveal loweq_pdb();
        reveal validPageDb();
        reveal mkAbsPTable();
    }
}

lemma lemma_eqpdb_pt_coresp_not_atkr(d1: PageDb, d2: PageDb, s1: state, s2: state,
    l1p:PageNr, asp: PageNr, atkr: PageNr)
    requires validPageDb(d1) && validPageDb(d2)
    requires ValidState(s1) && ValidState(s2)
    requires ValidState(s1) && ValidState(s2) && SaneConstants()
    requires valAddrPage(d1, asp ) && valAddrPage(d2, asp)
    requires valAddrPage(d1, atkr) && valAddrPage(d2, atkr)
    requires atkr != asp
    requires loweq_pdb(d1, d2, atkr)
    requires nonStoppedL1(d1, l1p) && nonStoppedL1(d2, l1p)
    requires pageTableCorresponds(s1, d1, l1p)
    requires pageTableCorresponds(s2, d2, l1p)
    requires d1[asp].entry.l1ptnr == d2[asp].entry.l1ptnr == l1p
    ensures  ExtractAbsPageTable(s1) == ExtractAbsPageTable(s2)
{
    reveal pageTableCorresponds();
    assert mkAbsPTable(d1, l1p) == mkAbsPTable(d2, l1p) by {
        reveal loweq_pdb();
        reveal validPageDb();
        reveal mkAbsPTable();
    }
}

//-----------------------------------------------------------------------------
// Resume
//-----------------------------------------------------------------------------
lemma lemma_resume_conf_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                               s2: state, d2: PageDb, s2':state, d2': PageDb,
                               dispPage: word,
                               atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires smc_resume(s1, d1, s1', d1', dispPage)
    requires smc_resume(s2, d2, s2', d2', dispPage)
    requires conf_loweq(s1, d1, s2, d2, atkr)
    requires loweq_pdb(d1, d2, atkr)
    requires s1.conf.nondet == s2.conf.nondet
    ensures  loweq_pdb(d1', d2', atkr)
    ensures  same_ret(s1', s2')
    ensures  InsecureMemInvariant(s1', s2')
{
    reveal loweq_pdb();
    var e1, e2 := smc_enter_err(d1, dispPage, true), smc_enter_err(d2, dispPage, true);
    assert e1 == e2;

    if(e1 == KOM_ERR_SUCCESS) {
        var asp1, asp2 := d1[dispPage].addrspace, d2[dispPage].addrspace;
        assert asp1 == asp2;
        if(asp1 == atkr) {
            lemma_enter_conf_atkr_enter(s1, d1, s1', d1',
                                       s2, d2, s2', d2',
                                       dispPage, 0, 0, 0, 
                                       atkr, true);
        } else {
            lemma_enter_loweq_pdb_not_atkr(s1, d1, s1', d1',
                                           s2, d2, s2', d2',
                                           dispPage, 0, 0, 0,
                                           asp1, atkr, true);
        }
    } 
}
