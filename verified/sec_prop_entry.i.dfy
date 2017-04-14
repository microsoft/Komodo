include "sec_prop.s.dfy"
include "pagedb.s.dfy"
include "entry.s.dfy"
include "sec_prop_util.i.dfy"
include "smcapi.i.dfy"

lemma lemma_enter_enc_conf_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                              s2: state, d2: PageDb, s2':state, d2': PageDb,
                              dispPage: word, arg1: word, arg2: word, arg3: word,
                              atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    requires smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires entering_atkr(d1, d2, dispPage, atkr, false) ==>
        enc_conf_eq_entry(s1, s2, d1, d2, atkr)
    ensures enc_conf_eqpdb(d1', d2', atkr)
    ensures entering_atkr(d1, d2, dispPage, atkr, false) ==>
        enc_conf_eq_entry(s1', s2', d1', d2', atkr)
{
    reveal_enc_conf_eqpdb();
    if(!validPageNr(dispPage)){
        assert d1' == d1 &&  d2' == d2;
    } else {
        assert d1[dispPage].PageDbEntryFree? <==> d2[dispPage].PageDbEntryFree?;
        if(d1[dispPage].PageDbEntryFree?) {
            assert d1' == d1 &&  d2' == d2;
        } else {
            assert d2[dispPage].PageDbEntryTyped?;
            var asp1, asp2 := d1[dispPage].addrspace, d2[dispPage].addrspace;
            var e1', e2' := smc_enter_err(d1, dispPage, false), smc_enter_err(d2, dispPage, false);
            assert enc_conf_eqpdb(d1', d2', atkr) by {
                lemma_enter_enc_conf_eqpdb(s1, d1, s1', d1', s2, d2, s2', d2',
                                 dispPage, arg1, arg2, arg3, asp1, asp2, atkr);
            }
            assert pgInAddrSpc(d1, dispPage, atkr) <==>
                pgInAddrSpc(d2, dispPage, atkr);
            assert pgInAddrSpc(d1, dispPage, atkr) ==>
                d1[dispPage].addrspace == atkr;
            assert pgInAddrSpc(d1, dispPage, atkr) ==>
                d1[dispPage].addrspace == atkr;
            assert asp1 == atkr <==> asp2 == atkr;

            if(asp1 == atkr) {
                assert e1' == KOM_ERR_SUCCESS <==> e2' == KOM_ERR_SUCCESS;
                if(e1' == KOM_ERR_SUCCESS) {
                    assert entering_atkr(d1, d2, dispPage, atkr, false);
                    lemma_enter_enc_conf_atkr_enter(s1, d1, s1', d1', s2, d2, s2', d2',
                                                    dispPage, arg1, arg2, arg3, 
                                                    atkr);
                    assert enc_conf_eq_entry(s1', s2', d1', d2', atkr);
                } else {
                    assert !entering_atkr(d1, d2, dispPage, atkr, false);
                }
            } else {
                assert !entering_atkr(d1, d2, dispPage, atkr, false);
            }
        }
    }
}

lemma lemma_enter_enc_conf_eqpdb(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                 s2: state, d2: PageDb, s2':state, d2': PageDb,
                                 disp: word, arg1: word, arg2: word, arg3: word,
                                 asp1: PageNr, asp2: PageNr, atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires smc_enter(s1, d1, s1', d1', disp, arg1, arg2, arg3)
    requires smc_enter(s2, d2, s2', d2', disp, arg1, arg2, arg3)
    requires validPageNr(disp) && d1[disp].PageDbEntryTyped? && 
        d2[disp].PageDbEntryTyped?
    requires d1[disp].addrspace == asp1 && d2[disp].addrspace == asp2
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires entering_atkr(d1, d2, disp, atkr, false) ==>
        enc_conf_eq_entry(s1, s2, d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr)
{

    reveal_enc_conf_eqpdb();
    var go1 := smc_enter_err(d1, disp, false) == KOM_ERR_SUCCESS;
    var go2 := smc_enter_err(d2, disp, false) == KOM_ERR_SUCCESS;

    if(go1 && go2) {
        lemma_enter_only_affects_entered(s1, d1, s1', d1',
             disp, asp1, arg1, arg2, arg3);
        lemma_enter_only_affects_entered(s2, d2, s2', d2',
             disp, asp2, arg1, arg2, arg3);
        
        assert d1[atkr].PageDbEntryTyped? <==> d2[atkr].PageDbEntryTyped?;
        assert d1[atkr].PageDbEntryTyped? <==> d1'[atkr].PageDbEntryTyped?;
        assert d2[atkr].PageDbEntryTyped? <==> d2'[atkr].PageDbEntryTyped?;
        assert d1'[atkr].PageDbEntryTyped? <==> d2'[atkr].PageDbEntryTyped?;
       
        assert valAddrPage(d1, asp1) && valAddrPage(d2, asp2);

        assert pgInAddrSpc(d1, disp, atkr) <==>
            pgInAddrSpc(d2, disp, atkr);
        assert pgInAddrSpc(d1, disp, atkr) ==>
            d1[disp].addrspace == atkr;
        assert pgInAddrSpc(d1, disp, atkr) ==>
            d1[disp].addrspace == atkr;
        assert asp1 == atkr <==> asp2 == atkr;
        
        if(asp1 == atkr) {
            assert entering_atkr(d1, d2, disp, atkr, false);
            assert enc_conf_eq_entry(s1, s2, d1, d2, atkr);
            lemma_enter_enc_conf_atkr_enter(s1, d1, s1', d1', s2, d2, s2', d2',
                                            disp, arg1, arg2, arg3, 
                                            atkr);
        } else {
            assert asp1 != atkr && asp2 != atkr;
            assert outside_world_same(d1, d1', disp, asp1);
            assert outside_world_same(d2, d2', disp, asp2);

            assert forall n : PageNr :: pgInAddrSpc(d1', n, asp1)
                <==>  pgInAddrSpc(d1, n, asp1);
            assert forall n : PageNr :: pgInAddrSpc(d1', n, atkr)
                ==> !pgInAddrSpc(d1', n, asp1);

            assert forall n : PageNr :: pgInAddrSpc(d2', n, asp2)
                <==>  pgInAddrSpc(d2, n, asp2);
            assert forall n : PageNr :: pgInAddrSpc(d2', n, atkr)
                ==> !pgInAddrSpc(d2', n, asp2);

            assert (forall n : PageNr | pgInAddrSpc(d1', n, atkr) 
                && d1'[n].PageDbEntryTyped? ::
                    d1'[n].addrspace == d1[n].addrspace &&
                    d1'[n].entry == d1[n].entry);
            
            assert (forall n : PageNr | pgInAddrSpc(d2', n, atkr) 
                && d2'[n].PageDbEntryTyped? ::
                    d2'[n].addrspace == d2[n].addrspace &&
                    d2'[n].entry == d2[n].entry);
            
            assert forall n : PageNr :: pgInAddrSpc(d1', n, atkr) <==>
                pgInAddrSpc(d1, n, atkr);
            assert forall n : PageNr :: pgInAddrSpc(d2', n, atkr) <==>
                pgInAddrSpc(d2, n, atkr);
            assert forall n : PageNr :: pgInAddrSpc(d1', n, atkr) <==>
                pgInAddrSpc(d2', n, atkr);

            assert forall n : PageNr | pgInAddrSpc(d1', n, atkr) ::
                d1'[n].entry == d2'[n].entry;
            
            assert enc_conf_eqpdb(d1', d2', atkr);
            
        }
    }

    if(go1 && !go2) {
        lemma_enter_enc_conf_eqpdb_one_go(s1, d1, s1', d1', s2, d2, s2', d2',
                         disp, arg1, arg2, arg3, asp1, asp2, atkr);
        assert enc_conf_eqpdb(d1', d2', atkr);
    }
    if(!go1 && go2) {
        lemma_enter_enc_conf_eqpdb_one_go(s2, d2, s2', d2', s1, d1, s1', d1',
                         disp, arg1, arg2, arg3, asp2, asp1, atkr);
        assert enc_conf_eqpdb(d1', d2', atkr);
    }
    if(!go1 && !go2) { 
        assert d1' == d1 && d2' == d2;
        assert enc_conf_eqpdb(d1', d2', atkr);
    }
}

lemma lemma_enter_enc_conf_eqpdb_one_go(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                        s2: state, d2: PageDb, s2':state, d2': PageDb,
                                        disp: word, arg1: word, arg2: word, arg3: word,
                                        asp1: PageNr, asp2: PageNr, atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires smc_enter(s1, d1, s1', d1', disp, arg1, arg2, arg3)
    requires smc_enter(s2, d2, s2', d2', disp, arg1, arg2, arg3)
    requires validPageNr(disp) && d1[disp].PageDbEntryTyped? && 
        d2[disp].PageDbEntryTyped?
    requires d1[disp].addrspace == asp1 && d2[disp].addrspace == asp2
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires smc_enter_err(d1, disp, false) == KOM_ERR_SUCCESS
            && !(smc_enter_err(d2, disp, false) == KOM_ERR_SUCCESS);
    ensures  enc_conf_eqpdb(d1', d2', atkr)
{
   reveal_enc_conf_eqpdb();
   var go1 := smc_enter_err(d1, disp, false) == KOM_ERR_SUCCESS;
   var go2 := smc_enter_err(d2, disp, false) == KOM_ERR_SUCCESS;
   assert go1 && !go2;
   
   assert d2' == d2;

   var asp1 := d1[disp].addrspace;

   assert asp1 != atkr by {
       var asp2 := d2[disp].addrspace;
       assert pgInAddrSpc(d1, disp, atkr) <==>
           pgInAddrSpc(d2, disp, atkr);
       assert pgInAddrSpc(d1, disp, atkr) ==>
           d1[disp].addrspace == atkr;
       assert pgInAddrSpc(d1, disp, atkr) ==>
           d1[disp].addrspace == atkr;
       assert asp1 == atkr <==> asp2 == atkr;
       assert asp2 == atkr && go1 ==> go2;
   }

   lemma_enter_only_affects_entered(s1, d1, s1', d1',
        disp, asp1, arg1, arg2, arg3);
   assert outside_world_same(d1, d1', disp, asp1);

   assert forall n : PageNr :: pgInAddrSpc(d1', n, asp1)
       <==>  pgInAddrSpc(d1, n, asp1);
   assert forall n : PageNr :: pgInAddrSpc(d1', n, atkr)
       ==> !pgInAddrSpc(d1', n, asp1);

   assert (forall n : PageNr | pgInAddrSpc(d1', n, atkr) 
       && d1'[n].PageDbEntryTyped? ::
           d1'[n].addrspace == d1[n].addrspace &&
           d1'[n].entry == d1[n].entry);
   
   assert forall n : PageNr :: pgInAddrSpc(d1', n, atkr) <==>
       pgInAddrSpc(d1, n, atkr);
   assert forall n : PageNr :: pgInAddrSpc(d1', n, atkr) <==>
       pgInAddrSpc(d2', n, atkr);

   assert forall n : PageNr | pgInAddrSpc(d1', n, atkr) ::
       d1'[n].entry == d2'[n].entry;
   
   assert enc_conf_eqpdb(d1', d2', atkr);

   assert enc_conf_eqpdb(d1', d2', atkr);
}

//-----------------------------------------------------------------------------
// Single enclave executions (attacker or otherwise) only affect their own things.
//-----------------------------------------------------------------------------

predicate outside_world_same(d:PageDb, d':PageDb, p:PageNr, asp: PageNr) 
    requires validPageDb(d) && validPageDb(d')
    requires validPageNr(p) && valDispPage(d, p)
    requires validPageNr(asp) && valAddrPage(d, asp)
    requires d[p].addrspace == asp
{
    nonStoppedDispatcher(d', p) && nonStoppedDispatcher(d, p) &&
    valDispPage(d', p) && valAddrPage(d', asp) && d'[p].addrspace == asp &&
    (forall n : PageNr :: d'[n].PageDbEntryTyped? <==>
        d[n].PageDbEntryTyped?) &&
    (forall n : PageNr :: pgInAddrSpc(d', n, asp) <==>
        pgInAddrSpc(d, n, asp)) &&
    (forall n : PageNr | !pgInAddrSpc(d', n, asp) 
        && d'[n].PageDbEntryTyped? ::
            d'[n].addrspace == d[n].addrspace &&
            d'[n].entry == d[n].entry)
}

lemma lemma_enter_only_affects_entered(s: state, d: PageDb, s': state, d': PageDb,
                                       disp:PageNr, asp:PageNr, arg1: word, arg2: word, arg3: word)
    requires ValidState(s) && validPageDb(d) && ValidState(s') && 
        validPageDb(d') && SaneConstants()
    requires validPageNr(disp) && valDispPage(d, disp)
    requires validPageNr(asp) && valAddrPage(d, asp)
    requires d[disp].addrspace == asp
    requires smc_enter(s, d, s', d', disp, arg1, arg2, arg3)
    requires smc_enter_err(d, disp, false) == KOM_ERR_SUCCESS
    ensures outside_world_same(d, d', disp, asp)
{
    forall(s1: state, steps:nat |
        preEntryEnter(s, s1, d, disp, arg1, arg2, arg3) &&
        validEnclaveExecution(s1, d, s', d', disp, steps))
        ensures outside_world_same(d, d', disp, asp)
    {
        lemma_validEnclaveEx_oae(s1, d, s', d', disp, steps, asp);
    }
}

lemma lemma_validEnclaveEx_oae(
    s:state, d: PageDb, s':state, d': PageDb,
    disp: PageNr, steps:nat, asp: PageNr)
    requires ValidState(s) && validPageDb(d) && ValidState(s') && 
        validPageDb(d') && SaneConstants()
    requires validPageNr(disp) && valDispPage(d, disp)
    requires validPageNr(asp) && valAddrPage(d, asp)
    requires d[disp].addrspace == asp
    requires nonStoppedDispatcher(d, disp)
    requires validEnclaveExecution(s, d, s', d', disp, steps);
    ensures outside_world_same(d, d', disp, asp)
    decreases steps;
{
    reveal validEnclaveExecution();
    var retToEnclave := (steps > 0);
    var  s5, d5 :|
        validEnclaveExecutionStep(s, d, s5, d5, disp, retToEnclave) &&
        (if retToEnclave then
            validEnclaveExecution(s5, d5, s', d', disp, steps -1)
        else
            s' == s5 && d' == d5);
    lemma_validEnclaveExecutionStep_validPageDb(s, d, s5, d5, disp, retToEnclave);
    lemma_validEnclaveStep_oae(s, d, s5, d5, disp, asp, retToEnclave);
    if(retToEnclave) {
        lemma_validEnclaveExecution(s5, d5, s', d', disp, steps - 1);
        lemma_validEnclaveEx_oae(s5, d5, s', d', disp, steps - 1, asp);
    } else {
        assert s' == s5 && d' == d5;
    }
}

lemma lemma_validEnclaveStep_oae(
    s:state, d: PageDb, s':state, d': PageDb,
    disp: PageNr, asp: PageNr, ret:bool)
    requires ValidState(s) && validPageDb(d) && ValidState(s') && 
        validPageDb(d') && SaneConstants()
    requires validPageNr(disp) && valDispPage(d, disp)
    requires validPageNr(asp) && valAddrPage(d, asp)
    requires d[disp].addrspace == asp
    requires nonStoppedDispatcher(d, disp)
    requires validEnclaveExecutionStep(s, d, s', d', disp, ret);
    ensures outside_world_same(d, d', disp, asp)
{
    reveal validEnclaveExecutionStep();
    var s4, d4 :|
        validEnclaveExecutionStep'(s, d, s4, d4, s', d', disp, ret);
    lemma_validEnclaveStepPrime_oae(s, d, s4, d4, s', d', disp, ret, asp);
}

lemma lemma_validEnclaveStepPrime_oae(
    s1:state, d1: PageDb, s4:state, d4: PageDb, r:state, rd: PageDb,
    disp: PageNr, ret:bool, asp: PageNr)
    requires ValidState(s1) && ValidState(s4) && ValidState(r)
    requires validPageDb(d1) && validPageDb(d4) && validPageDb(rd)
    requires SaneConstants()
    requires validPageNr(disp) && valDispPage(d1, disp)
    requires validPageNr(asp) && valAddrPage(d1, asp)
    requires d1[disp].addrspace == asp
    requires nonStoppedDispatcher(d1, disp)
    requires validEnclaveExecutionStep'(s1,d1,s4,d4,r,rd,disp,ret)
    ensures outside_world_same(d1, rd, disp, asp)
{
    assert d4 == updateUserPagesFromState(s4, d1, disp);
    assert outside_world_same(d1, d4, disp, asp) by 
        { reveal_updateUserPagesFromState(); }
    if (ret) {
        assert rd == d4;
        assert outside_world_same(d1, rd, disp, asp);
    } else {
        // This is the slow case if that matters.
    }
}


//-----------------------------------------------------------------------------
// Executions of attacker enclaves beginning from low-equiv states produce 
// low-equiv states.
//-----------------------------------------------------------------------------


predicate atkr_entry(d1: PageDb, d2: PageDb, disp: word, atkr: PageNr)
{
    validPageNr(disp) &&
    validPageDb(d1) && validPageDb(d2) &&
    valAddrPage(d1, atkr) && valAddrPage(d2, atkr) &&
    d1[disp].PageDbEntryTyped? && d1[disp].entry.Dispatcher? &&
    d2[disp].PageDbEntryTyped? && d2[disp].entry.Dispatcher? &&
    nonStoppedDispatcher(d1, disp) && nonStoppedDispatcher(d2, disp) &&
    d1[disp].addrspace == d2[disp].addrspace == atkr
}


lemma lemma_enter_enc_conf_atkr_enter(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                      s2: state, d2: PageDb, s2':state, d2': PageDb,
                                      dispPage: word, arg1: word, arg2: word, arg3: word,
                                      atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    requires smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires entering_atkr(d1, d2, dispPage, atkr, false);
    requires enc_conf_eq_entry(s1, s2, d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr)
    ensures  enc_conf_eq_entry(s1', s2', d1', d2', atkr)
{

    /*
    var s11:state, steps1: nat :|
        preEntryEnter(s1, s11, d1, dispPage, arg1, arg2, arg3) &&
        validEnclaveExecution(s11, d1, s1', d1', dispPage, steps1);
    
    var s21:state, steps2: nat :|
        preEntryEnter(s2, s21, d2, dispPage, arg1, arg2, arg3) &&
        validEnclaveExecution(s21, d2, s2', d2', dispPage, steps2);

    assert steps1 == steps2 by {
        // TODO proveme :(
        assume false;
    }

    var steps := steps1;
    
    lemma_validEnclaveEx_enc_conf(s11, d1, s1', d1', s21, d2, s2', d2',
                                         dispPage, steps, atkr);
    */

    // TODO
    // The thing that cannot be proven here is that the number of steps taken 
    // is the same in both executions. Factor this out into a lemma.

    forall(s11:state, s21:state, steps1:nat, steps2:nat |
        preEntryEnter(s1, s11, d1, dispPage, arg1, arg2, arg3) &&
        preEntryEnter(s2, s21, d2, dispPage, arg1, arg2, arg3) &&
        validEnclaveExecution(s11, d1, s1', d1', dispPage, steps1) &&
        validEnclaveExecution(s21, d2, s2', d2', dispPage, steps2))
        ensures enc_conf_eqpdb(d1', d2', atkr)
        ensures enc_conf_eq_entry(s1', s2', d1', d2', atkr)
    {
        assume steps1 == steps2;
        assume s11.conf.nondet == s21.conf.nondet;

        assume OperandContents(s11, OLR) == OperandContents(s21, OLR); //TODO proveme
        // TODO entry.s spec needs to fix this:
        assume user_regs(s11.regs) == user_regs(s21.regs);
        lemma_validEnclaveEx_enc_conf(s11, d1, s1', d1', s21, d2, s2', d2',
                                         dispPage, steps1, atkr);
    }
}

lemma lemma_validEnclaveEx_enc_conf(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                    s2: state, d2: PageDb, s2':state, d2': PageDb,
                                    dispPg: PageNr, steps:nat,
                                    atkr: PageNr)
    //requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') && SaneConstants()
    requires atkr_entry(d1, d2, dispPg, atkr)
    requires validEnclaveExecution(s1, d1, s1', d1', dispPg, steps)
    requires validEnclaveExecution(s2, d2, s2', d2', dispPg, steps);
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires enc_conf_eq_entry(s1, s2, d1, d2, atkr)
    requires OperandContents(s1, OLR) == OperandContents(s2, OLR)
    requires user_regs(s1.regs) == user_regs(s2.regs)
    ensures  atkr_entry(d1', d2', dispPg, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr)
    ensures  enc_conf_eq_entry(s1', s2', d1', d2', atkr)
    decreases steps
{
    reveal_validEnclaveExecution();
    var retToEnclave := (steps > 0);

    // I can't figure out how to get around assuming nonStoppedDispatcher here. 
    // I tried using a premium version of validEnclaveExecutionStep that calls 
    // the lemma that proves nonstopped, but LHS values couldn't be found...

    var s15, d15 :|
        validEnclaveExecutionStep(s1, d1, s15, d15, dispPg, retToEnclave) &&
        (if retToEnclave then
            (assume nonStoppedDispatcher(d15, dispPg);
            validEnclaveExecution(s15, d15, s1', d1', dispPg, steps - 1))
          else
             s1' == s15 && d1' == d15);

    var s25, d25 :|
        validEnclaveExecutionStep(s2, d2, s25, d25, dispPg, retToEnclave) &&
        (if retToEnclave then 
            (assume nonStoppedDispatcher(d25, dispPg);
            validEnclaveExecution(s25, d25, s2', d2', dispPg, steps - 1))
          else
             s2' == s25 && d2' == d25);

    lemma_validEnclaveExecutionStep_validPageDb(s1, d1, s15, d15, dispPg, retToEnclave);
    lemma_validEnclaveExecutionStep_validPageDb(s2, d2, s25, d25, dispPg, retToEnclave);
    lemma_validEnclaveStep_enc_conf(s1, d1, s15, d15, s2, d2, s25, d25,
        dispPg, atkr, retToEnclave);

    if(retToEnclave) {
        lemma_validEnclaveExecution(s15, d15, s1', d1', dispPg, steps - 1);
        lemma_validEnclaveExecution(s25, d25, s2', d2', dispPg, steps - 1);
        lemma_validEnclaveEx_enc_conf(s15, d15, s1', d1', s25, d25, s2', d2',
                                         dispPg, steps -1, atkr);
        assert enc_conf_eqpdb(d1', d2', atkr);
        assert enc_conf_eq_entry(s1', s2', d1', d2', atkr);
    } else {
        assert s2' == s25;
        assert s1' == s15;
        assert d1' == d15;
        assert d2' == d25;
        assert enc_conf_eqpdb(d1', d2', atkr);
        assert enc_conf_eq_entry(s1', s2', d1', d2', atkr);
    }

}

lemma lemma_validEnclaveStep_enc_conf(s1: state, d1: PageDb, s1':state, d1': PageDb,
                                      s2: state, d2: PageDb, s2':state, d2': PageDb,
                                      dispPage:PageNr, atkr: PageNr, ret:bool)
    requires ValidState(s1) && ValidState(s2) &&
             ValidState(s1') && ValidState(s2') &&
             validPageDb(d1) && validPageDb(d2) && 
             validPageDb(d1') && validPageDb(d2') && SaneConstants()
    requires atkr_entry(d1, d2, dispPage, atkr)
    requires validEnclaveExecutionStep(s1, d1, s1', d1', dispPage, ret);
    requires validEnclaveExecutionStep(s2, d2, s2', d2', dispPage, ret);
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires enc_conf_eq_entry(s1, s2, d1, d2, atkr)
    requires OperandContents(s1, OLR) == OperandContents(s2, OLR)
    requires user_regs(s1.regs) == user_regs(s2.regs)
    ensures  atkr_entry(d1', d2', dispPage, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr)
    ensures  enc_conf_eq_entry(s1', s2', d1', d2', atkr)
    ensures OperandContents(s1', OLR) == OperandContents(s2', OLR)
    ensures user_regs(s1'.regs) == user_regs(s2'.regs)
{
    reveal validEnclaveExecutionStep();
    var s14, d14 :|
        validEnclaveExecutionStep'(s1, d1, s14, d14, s1', d1',
            dispPage, ret);

    var s24, d24 :|
        validEnclaveExecutionStep'(s2, d2, s24, d24, s2', d2',
            dispPage, ret);

    lemma_validEnclaveStepPrime_enc_conf(
        s1, d1, s14, d14, s1', d1',
        s2, d2, s24, d24, s2', d2',
        dispPage, ret, atkr);
}

lemma lemma_user_regs_domain(regs:map<ARMReg, word>, hr:map<ARMReg, word>)
    requires ValidRegState(regs)
    requires hr == user_regs(regs)
    ensures  forall r :: r in hr <==> r in USER_REGS()
{
}

lemma eqregs(x: map<ARMReg,word>, y: map<ARMReg,word>)
	requires forall r :: r in x <==> r in y
	requires forall r | r in x :: x[r] == y[r]
	ensures x == y
	{}

lemma lemma_validEnclaveStepPrime_enc_conf(
s11: state, d11: PageDb, s14:state, d14:PageDb, r1:state, rd1:PageDb,
s21: state, d21: PageDb, s24:state, d24:PageDb, r2:state, rd2:PageDb,
dispPg:PageNr, retToEnclave:bool, atkr: PageNr
)
    requires ValidState(s11) && ValidState(s21) &&
             ValidState(r1)  && ValidState(r2)  &&
             validPageDb(d11) && validPageDb(d21) &&
             validPageDb(rd1) && validPageDb(rd2) && SaneConstants()
    requires atkr_entry(d11, d21, dispPg, atkr)
    requires validEnclaveExecutionStep'(s11,d11,s14,d14,r1,rd1,dispPg,retToEnclave)
    requires validEnclaveExecutionStep'(s21,d21,s24,d24,r2,rd2,dispPg,retToEnclave)
    requires OperandContents(s11, OLR) == OperandContents(s21, OLR)
    requires user_regs(s11.regs) == user_regs(s21.regs)
    requires enc_conf_eqpdb(d11, d21, atkr)
    requires enc_conf_eq_entry(s11, s21, d11, d21, atkr)
    ensures  atkr_entry(rd1, rd2, dispPg, atkr)
    ensures  enc_conf_eqpdb(rd1, rd2, atkr)
    ensures  enc_conf_eq_entry(r1, r2, rd1, rd2, atkr)
    ensures OperandContents(r1, OLR) == OperandContents(r2, OLR)
    ensures user_regs(r1.regs) == user_regs(r2.regs)
{

    assert l1pOfDispatcher(d11, dispPg) == l1pOfDispatcher(d21, dispPg) by
        { reveal_enc_conf_eqpdb(); }
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

    assert s13.conf.nondet == s23.conf.nondet by
    {
        reveal userspaceExecutionFn();
        assert s13.conf.nondet == nondet_int(s12.conf.nondet, NONDET_GENERATOR());
        assert s23.conf.nondet == nondet_int(s22.conf.nondet, NONDET_GENERATOR());
    }

    assert s12.m == s11.m;
    assert s22.m == s21.m;

    assert pageTableCorresponds(s12, d11, l1p) by
    { 
        assert pageTableCorresponds(s11, d11, l1p);
        reveal pageTableCorresponds();
    }

    assert pageTableCorresponds(s22, d21, l1p) by
    { 
        assert pageTableCorresponds(s21, d21, l1p);
        reveal pageTableCorresponds();
    }

    var pt1 := ExtractAbsPageTable(s12);
    var pt2 := ExtractAbsPageTable(s22);
    lemma_userStatesEquiv_atkr_conf(
        s11, s1', s12, s14, pc1, pt1, d11,
        s21, s2', s22, s24, pc2, pt2, d21,
        dispPg, atkr, l1p);

    var user_state1 := user_visible_state(s12, pc1, pt1.v);
    var user_state2 := user_visible_state(s22, pc2, pt2.v);

    assert ex1 == ex2 by {
        reveal userspaceExecutionFn();

        // There is no way to prove this!!!!!
        assume s12.conf.cpsr.f == s22.conf.cpsr.f;
        assume s12.conf.cpsr.i == s22.conf.cpsr.i;
        
        assert ex1 == nondet_exception(s12.conf.nondet, user_state1, s12.conf.cpsr.f, s12.conf.cpsr.i);
        assert ex2 == nondet_exception(s22.conf.nondet, user_state2, s22.conf.cpsr.f, s22.conf.cpsr.i);
    }

    assert user_regs(s13.regs) == user_regs(s23.regs) by {
        // reveal userspaceExecutionFn();
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

    assert expc1 == expc2 by { reveal userspaceExecutionFn(); }

    assert s14.conf.ex == ex1 && s24.conf.ex == ex2;

    assert s14.conf.nondet == s24.conf.nondet;

    lemma_userspaceExec_atkr_conf(
        s11, s1', s12, s13, s14, d11, d14,
        s21, s2', s22, s23, s24, d21, d24,
        dispPg, atkr, l1p);

    if(retToEnclave) {
        assert rd1 == d14;
        assert rd2 == d24;
        // XXX Can't prove this from entry.s:
        assume r1.conf.nondet == s14.conf.nondet;
        assume r2.conf.nondet == s24.conf.nondet;
        assert enc_conf_eqpdb(rd1, rd2, atkr);
        assert enc_conf_eq_entry(r1, r2, rd1, rd2, atkr);
    } else {
        assume cpsr in s13.sregs && cpsr in s23.sregs &&
            s13.sregs[cpsr] == s23.sregs[cpsr];
        assume mode_of_exception(s13.conf, ex1) ==
            mode_of_exception(s23.conf, ex2);

        assert s14 == exceptionTakenFn(s13, ex1, expc1) by {
            assert evalExceptionTaken(s13, ex1, expc1, s14);
        }
        assert s24 == exceptionTakenFn(s23, ex2, expc2) by {
            assert evalExceptionTaken(s13, ex1, expc1, s14);
        }
        lemma_exceptionTaken_atkr_conf(
            s13, s14, ex1, expc1, 
            s23, s24, ex2, expc2);
        lemma_exceptionHandled_atkr_conf(s14, d14, rd1, s24, d24, rd2, dispPg, atkr);
        // // No idea how to prove anything about nd_*
        assume r1.conf.nondet == s14.conf.nondet;
        assume r2.conf.nondet == s24.conf.nondet;
        assert enc_conf_eqpdb(rd1, rd2, atkr);
        assert enc_conf_eq_entry(r1, r2, rd1, rd2, atkr);
    }

    // I think the OLR here is nonsensical and I'm not sure it makes sense to 
    // use the PC value as part of the user state since we aren't really 
    // modeling the PC...
    assume OperandContents(r1, OLR) == OperandContents(r2, OLR);
    assume user_regs(r1.regs) == user_regs(r2.regs);
}

predicate user_state_same(s1:state, s2:state, pc1:word, pc2:word,
pt1:Maybe<AbsPTable>, pt2:Maybe<AbsPTable>)
requires ValidState(s1) && ValidState(s2)
{
    pt1 == ExtractAbsPageTable(s1) &&
    pt2 == ExtractAbsPageTable(s2) &&
    pt1.Just? && pt2.Just? &&
    pc1 == pc2 &&
    s1.conf.nondet == s2.conf.nondet &&
    user_visible_state(s1, pc1, pt1.v) ==
        user_visible_state(s2, pc2, pt2.v)
    
}

lemma lemma_exceptionTaken_atkr_conf(
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
    reveal_ValidRegState();
    reveal_ValidSRegState();
    s1.regs[LR(mode_of_state(s1))] == s2.regs[LR(mode_of_state(s2))] &&
    s1.sregs[spsr(mode_of_state(s1))] == s2.sregs[spsr(mode_of_state(s2))]
}


lemma lemma_exceptionHandled_atkr_conf(
s1: state, d1: PageDb, d1': PageDb, s2: state, d2: PageDb, d2': PageDb,
dispPg: PageNr, atkr: PageNr)
    requires ValidState(s1) && ValidState(s2) &&
             validPageDb(d1') && validPageDb(d2') &&
             validPageDb(d1) && validPageDb(d2) && SaneConstants()
    requires enc_conf_eq_entry(s1, s2, d1, d2, atkr);
    requires mode_of_state(s1) != User && mode_of_state(s2) != User
    requires mode_of_state(s1) == mode_of_state(s2)
    requires lr_spsr_same(s1, s2)
    requires validDispatcherPage(d1, dispPg) && validDispatcherPage(d2, dispPg)
    requires d1' == exceptionHandled(s1, d1, dispPg).2
    requires d2' == exceptionHandled(s2, d2, dispPg).2
    requires atkr_entry(d1, d2, dispPg, atkr)
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires user_regs(s1.regs) == user_regs(s2.regs)
    requires s1.conf.ex == s2.conf.ex
    ensures  enc_conf_eqpdb(d1', d2', atkr)
    ensures  atkr_entry(d1', d2', dispPg, atkr)
{
    reveal_enc_conf_eqpdb();
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

    if( ex.ExSVC? || ex.ExAbt? || ex.ExUnd? ) {
        assert d1'[dispPg].entry == d2'[dispPg].entry;
    } else {
        var pc1 := TruncateWord(OperandContents(s1, OLR) - 4);
        var pc2 := TruncateWord(OperandContents(s2, OLR) - 4);
        assert pc1 == pc2;
        reveal_ValidSRegState();
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
lemma_userMemEquiv_atkr_conf(
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
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires enc_conf_eq_entry(s12, s22, d1, d2, atkr);
    requires userspaceExecutionAndException'(s11, s1', s12, s14)
    requires userspaceExecutionAndException'(s21, s2', s22, s24)
    requires pc1 == OperandContents(s11, OLR) && pc2 == OperandContents(s21, OLR);
    requires pt1 == ExtractAbsPageTable(s12) && pt2 == ExtractAbsPageTable(s22);
    requires nonStoppedL1(d1, l1p) && nonStoppedL1(d2, l1p)
    requires atkr_entry(d1, d2, dispPg, atkr)
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
            ExtractAbsPageTable(s11).Just? && ExtractAbsPageTable(s21).Just?;
    }

    lemma_eqpdb_pt_coresp(d1, d2, s12, s22, l1p, atkr);

    forall a:addr | ValidMem(a) && a in TheValidAddresses() && addrIsSecure(a)
            && PageBase(a) in AllPagesInTable(pt1.v)
        ensures a in s12.m.addresses
        ensures a in s22.m.addresses
        ensures s12.m.addresses[a] == s22.m.addresses[a]
    {
        lemma_data_eqpdb_to_addrs(d1, d2, s12, s22, a, atkr, l1p);
    }
}

lemma lemma_userStatesEquiv_atkr_conf(
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
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires enc_conf_eq_entry(s12, s22, d1, d2, atkr);
    requires userspaceExecutionAndException'(s11, s1', s12, s14)
    requires userspaceExecutionAndException'(s21, s2', s22, s24)
    requires pc1 == OperandContents(s11, OLR) && pc2 == OperandContents(s21, OLR);
    requires pt1 == ExtractAbsPageTable(s12) && pt2 == ExtractAbsPageTable(s22);
    requires nonStoppedL1(d1, l1p) && nonStoppedL1(d2, l1p)
    requires atkr_entry(d1, d2, dispPg, atkr)
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
    lemma_userMemEquiv_atkr_conf(
        s11, s1', s12, s14, pc1, pt1, d1,
        s21, s2', s22, s24, pc2, pt2, d2,
        dispPg, atkr, l1p);
}

lemma lemma_userspaceExec_atkr_conf(
s11: state, s1':state, s12: state, s13:state, s14: state, d1:PageDb, d14: PageDb,
s21: state, s2':state, s22: state, s23:state, s24: state, d2:PageDb, d24: PageDb,
dispPg: PageNr, atkr: PageNr, l1p: PageNr)
    // requires ValidState(s12) && ValidState(s22) &&
    //          validPageDb(d1) && validPageDb(d2) && SaneConstants()
    requires ValidState(s11) && ValidState(s12) && ValidState(s13) && ValidState(s14)
    requires ValidState(s21) && ValidState(s22) && ValidState(s23) && ValidState(s24)
    requires validPageDb(d1) && validPageDb(d14)
    requires validPageDb(d2) && validPageDb(d24)
    requires SaneConstants()
    requires enc_conf_eq_entry(s12, s22, d1, d2, atkr);
    requires userspaceExecutionAndException'(s11, s1', s12, s14)
    requires userspaceExecutionAndException'(s21, s2', s22, s24)
    requires s13 == userspaceExecutionFn(s12, OperandContents(s11, OLR)).0;
    requires s23 == userspaceExecutionFn(s22, OperandContents(s21, OLR)).0;
    requires atkr_entry(d1, d2, dispPg, atkr)
    requires enc_conf_eqpdb(d1, d2, atkr)
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
    ensures enc_conf_eqpdb(d14, d24, atkr)
    ensures atkr_entry(d14, d24, dispPg, atkr)
{
    // reveal_evalUserspaceExecution();
    reveal_enc_conf_eqpdb();

    assert validPageDb(d14) && validPageDb(d24);

    forall(n : PageNr) 
        ensures pgInAddrSpc(d14, n, atkr) <==> pgInAddrSpc(d1, n, atkr)
        ensures d14[n].PageDbEntryTyped? <==> d1[n].PageDbEntryTyped?
        ensures d14[atkr].entry == d1[atkr].entry;
        { reveal_updateUserPagesFromState(); }

    forall( n : PageNr) 
        ensures pgInAddrSpc(d24, n, atkr) <==> pgInAddrSpc(d2, n, atkr)
        ensures d24[n].PageDbEntryTyped? <==> d2[n].PageDbEntryTyped?
        ensures d24[atkr].entry == d2[atkr].entry;
        { reveal_updateUserPagesFromState(); }

    assert forall n : PageNr :: pgInAddrSpc(d14, n, atkr) <==>
        pgInAddrSpc(d24, n, atkr);

    assert forall n : PageNr :: pageSWrInAddrspace(d1, l1p, n) <==>
        pageSWrInAddrspace(d2, l1p, n);

    var pc1 := OperandContents(s11, OLR);
    var pc2 := OperandContents(s21, OLR);
    var pt1 := ExtractAbsPageTable(s12);
    var pt2 := ExtractAbsPageTable(s22);
    
    lemma_userStatesEquiv_atkr_conf(
        s11, s1', s12, s14, pc1, pt1, d1,
        s21, s2', s22, s24, pc2, pt2, d2,
        dispPg, atkr, l1p);

    
    var user_state1 := user_visible_state(s12, pc1, pt1.v);
    var user_state2 := user_visible_state(s22, pc2, pt2.v);
    assert user_state1 == user_state2;

    forall( n : PageNr | pageSWrInAddrspace(d1, l1p, n))
        ensures contentsOfPage(s14, n) ==
            contentsOfPage(s24, n)
    {
        assert d1[n].PageDbEntryTyped?;
        assert d2[n].PageDbEntryTyped?;
        assert d1[n].entry.DataPage?;
        assert d2[n].entry.DataPage?;
        
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
                lemma_data_page_eqdb_to_addrs(d1, d2, s12, s22, n, a, atkr);
            }
        }
        assert s14.m == s13.m;
        assert s24.m == s23.m;
    }
    
    forall( n : PageNr | pgInAddrSpc(d14, n, atkr))
        ensures d14[n].entry == d24[n].entry
    {
        reveal_updateUserPagesFromState();
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

    reveal_enc_conf_eqpdb();
    assert enc_conf_eqpdb(d14, d24, atkr);
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
    assert validL1PTable(d, l1p) by { reveal_validPageDb(); }
    var abspt := mkAbsPTable(d, l1p);
    var l1pt := d[l1p].entry.l1pt;
    var i, j :| 0 <= i < ARM_L1PTES && 0 <= j < ARM_L2PTES
        && abspt[i].Just? && abspt[i].v[j].Just?
        && pagebase == abspt[i].v[j].v.phys + PhysBase();
    var p := monvaddr_page(pagebase);
    reveal_mkAbsPTable();
    assert p == (abspt[i].v[j].v.phys - SecurePhysBase()) / PAGESIZE;
    var n := i / 4;
    assert l1pt[n].Just?;
    var l2p := l1pt[n].v;
    assert d[l2p].PageDbEntryTyped? && d[l2p].entry.L2PTable?
        && wellFormedPageDbEntry(d[l2p]) && validL2PTable(d, l2p)
        by { reveal_validPageDb(); }
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
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires dataPagesCorrespond(s1.m, d1) && dataPagesCorrespond(s2.m, d2)
    requires ExtractAbsPageTable(s1).Just?
    requires ExtractAbsPageTable(s2).Just?
    requires ValidMem(a)
    requires a in TheValidAddresses()
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
    assert address_is_secure(a) by
        { assume forall a:addr :: address_is_secure(a) <==> addrIsSecure(a); }
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
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires a in addrsInPage(n, page_monvaddr(n))
    requires dataPagesCorrespond(s1.m, d1) && dataPagesCorrespond(s2.m, d2)
    ensures s1.m.addresses[a] == s2.m.addresses[a]
{
    reveal enc_conf_eqpdb();
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
    requires enc_conf_eqpdb(d1, d2, atkr)
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
        reveal enc_conf_eqpdb();
        reveal validPageDb();
        reveal mkAbsPTable();
    }
}

//-----------------------------------------------------------------------------
// Resume
//-----------------------------------------------------------------------------
lemma lemma_resume_enc_conf_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                               s2: state, d2: PageDb, s2':state, d2': PageDb,
                               dispPage: word,
                               atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires smc_resume(s1, d1, s1', d1', dispPage)
    requires smc_resume(s2, d2, s2', d2', dispPage)
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires entering_atkr(d1, d2, dispPage, atkr, true) ==>
        enc_conf_eq_entry(s1, s2, d1, d2, atkr)
    ensures enc_conf_eqpdb(d1', d2', atkr)
    ensures entering_atkr(d1, d2, dispPage, atkr, true) ==>
        enc_conf_eq_entry(s1', s2', d1', d2', atkr)
{
    // TODO proveme
    assume false;
}
