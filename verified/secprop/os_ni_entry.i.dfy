include "sec_prop.s.dfy"
include "../pagedb.s.dfy"
include "../entry.s.dfy"
include "sec_prop_util.i.dfy"
include "../smcapi.i.dfy"

predicate same_ret(s1:state, s2:state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal ValidRegState();
    s1.regs[R0] == s2.regs[R0] &&
    s1.regs[R1] == s2.regs[R1]
}

lemma lemma_enter_os_ni(
    s1: state, d1: PageDb, s1':state, d1': PageDb,
    s2: state, d2: PageDb, s2':state, d2': PageDb,
    dispPage: word, arg1: word, arg2: word, arg3: word)
    requires os_ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2')
    requires s1.conf.nondet == s2.conf.nondet
    requires os_eq(s1, d1, s2, d2)
    requires smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    requires smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    ensures  os_eqpdb(d1', d2')
    ensures  same_ret(s1', s2')
    ensures  InsecureMemInvariant(s1', s2')
{
    var e1', e2' := smc_enter_err(d1, dispPage, false), 
        smc_enter_err(d2, dispPage, false);
    assert e1' == e2' by {
        reveal os_eqpdb();
    }
    if(e1' != KOM_ERR_SUCCESS) {
        assert os_eqpdb(d1', d2');
        assert same_ret(s1', s2');
        assert InsecureMemInvariant(s1', s2');
    } else {
        var s11:state, steps1: nat :|
            preEntryEnter(s1, s11, d1, dispPage, arg1, arg2, arg3) &&
            validEnclaveExecution(s11, d1, s1', d1', dispPage, steps1);
        
        var s21:state, steps2: nat :|
            preEntryEnter(s2, s21, d2, dispPage, arg1, arg2, arg3) &&
            validEnclaveExecution(s21, d2, s2', d2', dispPage, steps2);
        
        assert s11.conf.nondet == s21.conf.nondet;

        assert !spsr_of_state(s11).f && !spsr_of_state(s11).i
            && !spsr_of_state(s21).f && !spsr_of_state(s21).i by {
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
        
        lemma_validEnclaveEx_os(s11, d1, s1', d1', s21, d2, s2', d2',
                                             dispPage, steps1, steps2);
    }
}

lemma lemma_resume_os_ni(
    s1: state, d1: PageDb, s1':state, d1': PageDb,
    s2: state, d2: PageDb, s2':state, d2': PageDb,
    dispPage: word)
    requires os_ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2')
    requires s1.conf.nondet == s2.conf.nondet
    requires smc_resume(s1, d1, s1', d1', dispPage)
    requires smc_resume(s2, d2, s2', d2', dispPage)
    requires os_eq(s1, d1, s2, d2)
    ensures  os_eqpdb(d1', d2')
    ensures  same_ret(s1', s2')
    ensures  InsecureMemInvariant(s1', s2')
{
    var e1', e2' := smc_enter_err(d1, dispPage, true), 
        smc_enter_err(d2, dispPage, true);
    assert e1' == e2' by {
        reveal os_eqpdb();
    }
    if(e1' != KOM_ERR_SUCCESS) {
        assert os_eqpdb(d1', d2');
        assert same_ret(s1', s2');
        assert InsecureMemInvariant(s1', s2');
    } else {
        var s11:state, steps1: nat :|
            preEntryResume(s1, s11, d1, dispPage) &&
            validEnclaveExecution(s11, d1, s1', d1', dispPage, steps1);
        
        var s21:state, steps2: nat :|
            preEntryResume(s2, s21, d2, dispPage) &&
            validEnclaveExecution(s21, d2, s2', d2', dispPage, steps2);
        
        assert s11.conf.nondet == s21.conf.nondet;
       
        lemma_validEnclaveEx_os(s11, d1, s1', d1', s21, d2, s2', d2',
            dispPage, steps1, steps2);
    }
}

lemma lemma_validEnclaveEx_os(
    s1: state, d1: PageDb, s1': state, d1': PageDb,
    s2: state, d2: PageDb, s2': state, d2': PageDb,
    dispPg:PageNr, steps1:nat, steps2:nat)
    requires SaneConstants() && do_declassify()
    requires ValidState(s1) && ValidState(s2) &&
        ValidState(s1') && ValidState(s2')
    requires validPageDb(d1) && validPageDb(d2) &&
        validPageDb(d1') && validPageDb(d2')
    requires finalDispatcher(d1, dispPg)
    requires finalDispatcher(d2, dispPg)
    requires validEnclaveExecution(s1, d1, s1', d1', dispPg, steps1);
    requires validEnclaveExecution(s2, d2, s2', d2', dispPg, steps2);
    requires os_eqpdb(d1, d2)
    requires InsecureMemInvariant(s1, s2)
    requires s1.conf.nondet == s2.conf.nondet
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires !spsr_of_state(s1).f && !spsr_of_state(s1).i
    requires !spsr_of_state(s2).f && !spsr_of_state(s2).i
    ensures  os_eqpdb(d1', d2')
    ensures  same_ret(s1', s2')
    ensures  InsecureMemInvariant(s1', s2')
    decreases steps1, steps2
{
    reveal validEnclaveExecution();

    var retToEnclave1, s15, d15 := lemma_unpack_validEnclaveExecution(
        s1, d1, s1', d1', dispPg, steps1);
    var retToEnclave2, s25, d25 := lemma_unpack_validEnclaveExecution(
        s2, d2, s2', d2', dispPg, steps2);

    lemma_validEnclaveExecutionStep_validPageDb(s1, d1, s15, d15, dispPg, retToEnclave1);
    lemma_validEnclaveExecutionStep_validPageDb(s2, d2, s25, d25, dispPg, retToEnclave2);
    lemma_validEnclaveStep_os(s1, d1, s15, d15, s2, d2, s25, d25,
        dispPg, retToEnclave1, retToEnclave2);

    assert retToEnclave1 == retToEnclave2;

    if(retToEnclave1) {
        lemma_validEnclaveExecution(s15, d15, s1', d1', dispPg, steps1 - 1);
        lemma_validEnclaveExecution(s25, d25, s2', d2', dispPg, steps2 - 1);
        lemma_validEnclaveEx_os(s15, d15, s1', d1', s25, d25, s2', d2',
                                         dispPg, steps1 - 1, steps2 - 1);
        assert os_eqpdb(d1', d2');
    } else {
        assert s2' == s25;
        assert s1' == s15;
        assert d1' == d15;
        assert d2' == d25;
        assert os_eqpdb(d1', d2');
    }
}

lemma lemma_validEnclaveStep_os(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                     s2: state, d2: PageDb, s2':state, d2': PageDb,
                                     dispPage:PageNr, ret1:bool, ret2:bool)
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') 
    requires SaneConstants() && do_declassify()
    requires s1.conf.nondet == s2.conf.nondet
    requires finalDispatcher(d1, dispPage)
    requires finalDispatcher(d2, dispPage)
    requires validEnclaveExecutionStep(s1, d1, s1', d1', dispPage, ret1);
    requires validEnclaveExecutionStep(s2, d2, s2', d2', dispPage, ret2);
    requires os_eqpdb(d1, d2)
    requires InsecureMemInvariant(s1, s2)
    ensures  os_eqpdb(d1', d2')
    ensures  InsecureMemInvariant(s1', s2')
    ensures  ret1 == ret2
    ensures  ret1 ==> s1'.conf.nondet == s2'.conf.nondet;
    ensures  ret1 ==> do_declassify()
    ensures  !ret1 ==> same_ret(s1', s2')
{
    reveal validEnclaveExecutionStep();
    var s14, d14 :|
        validEnclaveExecutionStep'(s1, d1, s14, d14, s1', d1',
            dispPage, ret1);

    var s24, d24 :|
        validEnclaveExecutionStep'(s2, d2, s24, d24, s2', d2',
            dispPage, ret2);

    lemma_validEnclaveStepPrime_os(
        s1, d1, s14, d14, s1', d1',
        s2, d2, s24, d24, s2', d2',
        dispPage, ret1, ret2);
}

lemma lemma_svcHandled_os_eqpdb(s1: state, d1: PageDb, d1': PageDb,
                                 s2: state, d2: PageDb, d2': PageDb, dispPg: PageNr)
    requires validPageDbs({d1, d1'}) && validDispatcherPage(d1, dispPg)
    requires validPageDbs({d2, d2'}) && validDispatcherPage(d2, dispPg)
    requires ValidState(s1) && mode_of_state(s1) != User
    requires ValidState(s2) && mode_of_state(s2) != User
    requires OperandContents(s1, OReg(R0)) == OperandContents(s2, OReg(R0));
    requires OperandContents(s1, OReg(R1)) == OperandContents(s2, OReg(R1));
    requires OperandContents(s1, OReg(R2)) == OperandContents(s2, OReg(R2));
    requires isReturningSvc(s1) && finalDispatcher(d1, dispPg)
    requires isReturningSvc(s2) && finalDispatcher(d2, dispPg)
    requires d1' == svcHandled(s1, d1, dispPg).1
    requires d2' == svcHandled(s2, d2, dispPg).1
    requires os_eqpdb(d1, d2)
    ensures os_eqpdb(d1', d2')
{

    reveal os_eqpdb();
    var addrspace := d1[dispPg].addrspace;
    var call := OperandContents(s1, OReg(R0));
    if( call  == KOM_SVC_ATTEST ) {
        assert d1' == d1;
        assert d2' == d2;
    } else if( call  == KOM_SVC_VERIFY_STEP0) {
        assert os_eqentry(d1'[dispPg].entry, d2'[dispPg].entry);
    } else if( call  == KOM_SVC_VERIFY_STEP1) {
        assert os_eqentry(d1'[dispPg].entry, d2'[dispPg].entry);
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
            assert enc_eqentry(d1'[page].entry, d2'[page].entry);

            var abs_mapping := wordToMapping(mapping);
            var l11 := d1[d1[addrspace].entry.l1ptnr].entry;
            var l12 := d2[d2[addrspace].entry.l1ptnr].entry;
            var l1pte1 := fromJust(l11.l1pt[abs_mapping.l1index]);
            var l1pte2 := fromJust(l12.l1pt[abs_mapping.l1index]);
            assert enc_eqentry(d1'[l1pte1].entry, d2'[l1pte2].entry);
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
            assert os_eqentry(d1'[page].entry, d2'[page].entry);
            assert os_eqentry(d1'[l1ptnr].entry, d2'[l1ptnr].entry);
            // var d2 := installL1PTEInPageDb(d1, l1ptnr, page, l1index);
        }
    } else {
    }
}

lemma //{:timeLimitMultiplier 2}
lemma_validEnclaveStepPrime_os_retnondet(
s11: state, d11: PageDb, s14:state, d14:PageDb, r1:state, rd1:PageDb,
s21: state, d21: PageDb, s24:state, d24:PageDb, r2:state, rd2:PageDb,
dispPg:PageNr, retToEnclave1:bool, retToEnclave2:bool
)
    requires ValidState(s11) && ValidState(s21) &&
             ValidState(r1)  && ValidState(r2)  &&
             validPageDb(d11) && validPageDb(d21) &&
             validPageDb(rd1) && validPageDb(rd2) && SaneConstants()
    requires do_declassify()
    // requires s11.conf.nondet == s21.conf.nondet
    requires finalDispatcher(d11, dispPg)
    requires finalDispatcher(d21, dispPg)
    requires validEnclaveExecutionStep'(s11,d11,s14,d14,r1,rd1,dispPg,retToEnclave1)
    requires validEnclaveExecutionStep'(s21,d21,s24,d24,r2,rd2,dispPg,retToEnclave2)
    /// requires InsecureMemInvariant(s11, s21)
    // requires os_eqpdb(d11, d21)
    //requires userspaceExecutionAndException'(s11, s1', s12, s14);
    //requires userspaceExecutionAndException'(s21, s2', s22, s24);
    requires s14.conf.nondet == s24.conf.nondet 
    requires os_eqpdb(d14, d24)
    requires retToEnclave1 == retToEnclave2
    requires s14.conf.ex == s24.conf.ex;
    requires (!retToEnclave1 && s14.conf.ex == ExSVC) ==>
            s14.regs[R0] == s24.regs[R0];
    requires (!retToEnclave1 && s14.conf.ex == ExSVC &&
        s14.regs[R0] == KOM_SVC_EXIT) ==> 
        s14.regs[R1] == s24.regs[R1]
    ensures  os_eqpdb(rd1, rd2)
    ensures  !retToEnclave1 ==> same_ret(r1, r2)
    ensures  retToEnclave1 ==> r1.conf.nondet == r2.conf.nondet
{
    if(retToEnclave1) {
        
        var (retRegs1, rd1') := svcHandled(s14, d14, dispPg);
        var (retRegs2, rd2') := svcHandled(s24, d24, dispPg);

        // these regs also need to be declassified so that 
        // we know the svc arguments are the same in both executions.
        assume (s14.regs[R0] == s24.regs[R0] &&
                s14.regs[R1] == s24.regs[R1] &&
                s14.regs[R2] == s24.regs[R2]);
        lemma_svcHandled_os_eqpdb(s14, d14, rd1',
                                 s24, d24, rd2', dispPg);

        reveal os_eqpdb();
        
        assert os_eqpdb(rd1', rd2');
        assert os_eqpdb(rd1, rd2);

        assert r1.conf.nondet == r2.conf.nondet by {
            assert s14.conf.nondet == s24.conf.nondet; 
        }
    } else {
        reveal ValidRegState();
        lemma_exceptionHandled_os(
            s14, d14, rd1, r1.regs[R0], r1.regs[R1],
            s24, d24, rd2, r2.regs[R0], r2.regs[R1],
            dispPg);
    }
}

lemma {:timeLimitMultiplier 3}
lemma_validEnclaveStepPrime_os(
s11: state, d11: PageDb, s14:state, d14:PageDb, r1:state, rd1:PageDb,
s21: state, d21: PageDb, s24:state, d24:PageDb, r2:state, rd2:PageDb,
dispPg:PageNr, retToEnclave1:bool, retToEnclave2:bool
)
    requires ValidState(s11) && ValidState(s21) &&
             ValidState(r1)  && ValidState(r2)  &&
             validPageDb(d11) && validPageDb(d21) &&
             validPageDb(rd1) && validPageDb(rd2) && SaneConstants()
    requires do_declassify()
    requires s11.conf.nondet == s21.conf.nondet
    requires finalDispatcher(d11, dispPg)
    requires finalDispatcher(d21, dispPg)
    requires validEnclaveExecutionStep'(s11,d11,s14,d14,r1,rd1,dispPg,retToEnclave1)
    requires validEnclaveExecutionStep'(s21,d21,s24,d24,r2,rd2,dispPg,retToEnclave2)
    requires InsecureMemInvariant(s11, s21)
    requires os_eqpdb(d11, d21)
    ensures  InsecureMemInvariant(r1, r2)
    ensures  os_eqpdb(rd1, rd2)
    ensures  retToEnclave1 == retToEnclave2
    ensures  !retToEnclave1 ==> same_ret(r1, r2)
    ensures  retToEnclave1 ==> r1.conf.nondet == r2.conf.nondet
{
    assert l1pOfDispatcher(d11, dispPg) == l1pOfDispatcher(d21, dispPg) by
        { reveal os_eqpdb(); }
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
   
    //-------------------------------------------------------------------------
    // This could be a lemma, but commenting it out and assuming
    // only shaved off about 5s
    //-------------------------------------------------------------------------
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
        lemma_eqpdb_pt_coresp(d11, d21, s12, s22, l1p);
    }

    assert s12.conf.nondet == s22.conf.nondet;

    assert InsecureMemInvariant(s13, s23) by {
        lemma_insecure_mem_userspace(
            s12, pc1, s13, expc1, ex1,
            s22, pc2, s23, expc2, ex2);
    }

    assert InsecureMemInvariant(s14, s24);

    assert InsecureMemInvariant(r1, r2);
    //-------------------------------------------------------------------------

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

    assert os_eqpdb(d14, d24) by
    {
        assert validPageDbs({d11,d21,d14,d24});
        lemma_updateUserPages_os(s14, d11, d14,
            s24, d21, d24, dispPg);
    }

    assert retToEnclave1 == retToEnclave2 &&
        (!retToEnclave1 && ex1 == ExSVC ==>
            (s14.regs[R0] == s24.regs[R0] == KOM_SVC_EXIT ==>
            s14.regs[R1] == s24.regs[R1])) by
    {
        assert s14.regs[R0] == s13.regs[R0];
        assert s24.regs[R0] == s23.regs[R0];
        reveal userspaceExecutionFn();
        if(ex1 == ExSVC) {
            lemma_decl_svc_r0(s13, s14, s23, s24);
            if(s14.regs[R0] == KOM_SVC_EXIT) {
                lemma_decl_svc_exit_r1(s13, s14, s23, s24);
            }
        }
    }
    
    lemma_validEnclaveStepPrime_os_retnondet(
        s11, d11, s14, d14, r1, rd1,
        s21, d21, s24, d24, r2, rd2,
        dispPg, retToEnclave1, retToEnclave2);

    /*
    if(retToEnclave1) {
        assert os_eqpdb(rd1, rd2);
        assert same_ret(r1, r2);
        assert r1.conf.nondet == r2.conf.nondet by {
            assert s14.conf.nondet == s24.conf.nondet; 
        }
    } else {
        reveal ValidRegState();
        lemma_exceptionHandled_os(
            s14, d14, rd1, r1.regs[R0], r1.regs[R1],
            s24, d24, rd2, r2.regs[R0], r2.regs[R1],
            dispPg);
    }
    */

}

lemma lemma_exceptionHandled_os(
    s14:state, d14:PageDb, rd1:PageDb, r01:word, r11:word,
    s24:state, d24:PageDb, rd2:PageDb, r02:word, r12:word,
    dispPg:PageNr)
    requires validStates({s14, s24})
    requires validPageDbs({d14,d24,rd1,rd2})
    requires validDispatcherPage(d14, dispPg)
    requires validDispatcherPage(d24, dispPg)
    requires mode_of_state(s14) != User
    requires mode_of_state(s24) != User
    requires (r01, r11, rd1) == exceptionHandled(s14, d14, dispPg)
    requires (r02, r12, rd2) == exceptionHandled(s24, d24, dispPg)
    requires s14.conf.ex == s24.conf.ex
    requires os_eqpdb(d14, d24)
    requires R1 in s14.regs && R1 in s24.regs
    requires s14.conf.ex.ExSVC? ==> 
        s14.regs[R1] == s24.regs[R1]
    ensures  os_eqpdb(rd1, rd2)
    ensures  r01 == r02 && r11 == r12
{
    reveal os_eqpdb();
}
    

lemma lemma_updateUserPages_os(
    s14: state, d11: PageDb, d14: PageDb,
    s24: state, d21: PageDb, d24: PageDb,
    dispPg: PageNr)
requires validStates({s14, s24}) && SaneConstants()
requires validPageDbs({d11,d21,d14,d24})
requires finalDispatcher(d11, dispPg)
requires finalDispatcher(d21, dispPg)
requires d14 == updateUserPagesFromState(s14, d11, dispPg)
requires d24 == updateUserPagesFromState(s24, d21, dispPg)
requires os_eqpdb(d11, d21)
ensures  os_eqpdb(d14, d24)
{
    reveal updateUserPagesFromState();
    reveal os_eqpdb();
}

function insecureUserspaceMem(s:state, pc:word, a:addr): word
    requires ValidState(s)
    requires ValidMem(a) && a in TheValidAddresses()
    requires !addrIsSecure(a)
    requires ExtractAbsPageTable(s).Just?
{
    var pt := ExtractAbsPageTable(s).v;
    var user_state := user_visible_state(s, pc, pt);
    var pages := WritablePagesInTable(pt);
    if( PageBase(a) in pages ) then nondet_word(s.conf.nondet, a)
    else MemContents(s.m, a)
}

lemma lemma_userspace_insecure_addr(s:state, pc: word, s3: state, a:addr)
    requires validStates({s, s3})
    requires mode_of_state(s) == User
    requires ValidMem(a) && a in TheValidAddresses()
    requires !addrIsSecure(a)
    requires ExtractAbsPageTable(s).Just?
    requires userspaceExecutionFn(s, pc).0 == s3
    ensures  MemContents(s3.m, a) == insecureUserspaceMem(s, pc, a)
{
    var pt := ExtractAbsPageTable(s).v;
    var user_state := user_visible_state(s, pc, pt);
    var pages := WritablePagesInTable(pt);
    var newpsr := nondet_psr(s.conf.nondet, user_state, s.conf.cpsr);
    var hv := havocPages(pages, s, user_state);
    assert s3.m.addresses == hv by
        { reveal userspaceExecutionFn(); }
}

lemma lemma_insecure_mem_userspace(
    s12: state, pc1: word, s13: state, expc1: word, ex1: exception,
    s22: state, pc2: word, s23: state, expc2: word, ex2: exception)
    requires validStates({s12, s13, s22, s23})
    requires SaneConstants()
    requires InsecureMemInvariant(s12, s22)
    requires s12.conf.nondet == s22.conf.nondet
    requires mode_of_state(s12) == mode_of_state(s22) == User;
    requires 
        var pt1 := ExtractAbsPageTable(s12);
        var pt2 := ExtractAbsPageTable(s22);
        pt1.Just? && pt2.Just? && pt1 == pt2
    requires userspaceExecutionFn(s12, pc1) == (s13, expc1, ex1)
    requires userspaceExecutionFn(s22, pc2) == (s23, expc2, ex2)
    ensures InsecureMemInvariant(s13, s23)
{
    reveal ValidMemState();
    var pt := ExtractAbsPageTable(s12).v;
    var pages := WritablePagesInTable(pt);

    forall( a | ValidMem(a) && address_is_insecure(a) )
        ensures s13.m.addresses[a] == s23.m.addresses[a]
    {
        var m1 := insecureUserspaceMem(s12, pc1, a);
        var m2 := insecureUserspaceMem(s22, pc2, a);
        lemma_userspace_insecure_addr(s12, pc1, s13, a);
        lemma_userspace_insecure_addr(s22, pc2, s23, a);
        assert s13.m.addresses[a] == m1;
        assert s23.m.addresses[a] == m2;
        if(PageBase(a) in pages) {
            assert m1 == nondet_word(s12.conf.nondet, a);
            assert m2 == nondet_word(s22.conf.nondet, a);
            assert s12.conf.nondet == s22.conf.nondet;
        } else {
        }
    }
}

// Range used by InsecureMemInvariant
predicate address_is_insecure(m:addr) 
{
    KOM_DIRECTMAP_VBASE <= m < KOM_DIRECTMAP_VBASE + MonitorPhysBase()
}

lemma lemma_eqpdb_pt_coresp(d1: PageDb, d2: PageDb, s1: state, s2: state, l1p:PageNr)
    requires validPageDb(d1) && validPageDb(d2)
    requires ValidState(s1) && ValidState(s2)
    requires ValidState(s1) && ValidState(s2) && SaneConstants()
    requires os_eqpdb(d1, d2)
    requires nonStoppedL1(d1, l1p) && nonStoppedL1(d2, l1p)
    requires pageTableCorresponds(s1, d1, l1p)
    requires pageTableCorresponds(s2, d2, l1p)
    ensures  ExtractAbsPageTable(s1) == ExtractAbsPageTable(s2)
{
    reveal pageTableCorresponds();
    assert mkAbsPTable(d1, l1p) == mkAbsPTable(d2, l1p) by {
        reveal os_eqpdb();
        reveal validPageDb();
        reveal mkAbsPTable();
    }
}
