include "sec_prop.s.dfy"
include "pagedb.s.dfy"
include "entry.s.dfy"

//-----------------------------------------------------------------------------
// Enclave-Enclave Confidentiality
//-----------------------------------------------------------------------------
predicate ni_reqs(s1: state, d1: PageDb, s1': state, d1': PageDb,
                  s2: state, d2: PageDb, s2': state, d2': PageDb,
                  atkr: PageNr)
{
    SaneState(s1) && validPageDb(d1) && SaneState(s1') && validPageDb(d1') &&
    SaneState(s2) && validPageDb(d2) && SaneState(s2') && validPageDb(d2') &&
    pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s1'.m, d1') &&
    pageDbCorresponds(s2.m, d2) && pageDbCorresponds(s2'.m, d2') &&
    valDispPage(d1, atkr) && valDispPage(d2, atkr)
}

predicate ni_reqs_(d1: PageDb, d1': PageDb, d2: PageDb, d2': PageDb, atkr: PageNr)
{
    validPageDb(d1) && validPageDb(d1') &&
    validPageDb(d2) && validPageDb(d2') &&
    valDispPage(d1, atkr) && valDispPage(d2, atkr)
}

predicate same_call_args(s1:state, s2: state)
    requires SaneState(s1) && SaneState(s2)
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
    OperandContents(s1, OReg(R0))  == OperandContents(s2, OReg(R0)) &&
    OperandContents(s1, OReg(R1))  == OperandContents(s2, OReg(R1)) &&
    OperandContents(s1, OReg(R2))  == OperandContents(s2, OReg(R2)) &&
    OperandContents(s1, OReg(R3))  == OperandContents(s2, OReg(R3)) &&
    OperandContents(s1, OReg(R4))  == OperandContents(s2, OReg(R4))
}

lemma enc_enc_conf_ni(s1: state, d1: PageDb, s1': state, d1': PageDb,
                      s2: state, d2: PageDb, s2': state, d2': PageDb,
                      atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires same_call_args(s1, s2)
    // If smchandler(s1, d1) => (s1', d1')
    requires smchandler(s1, d1, s1', d1')
    // and smchandler(s2, d2) => (s2', d2')
    requires smchandler(s2, d2, s2', d2')
    // s.t. (s1, d1) =_{atkr} (s2, d2)
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    requires (var callno := s1.regs[R0]; var dispPage := s1.regs[R1];
        (callno == KOM_SMC_ENTER || callno == KOM_SMC_RESUME) && dispPage == atkr 
            ==> enc_enc_conf_eq(s1, s2, d1, d2, atkr))
    // then (s1', d1') =_{atkr} (s2', d2')
    // (maybe the following line should really be valDisp(_,atkr) ==> d1 =_L d2)
    ensures valDispPage(d1', atkr) && valDispPage(d2', atkr) &&
        enc_enc_conf_eqpdb(d1', d2', atkr)  
    ensures (var callno := s1.regs[R0]; var dispPage := s1.regs[R1];
        (callno == KOM_SMC_ENTER || callno == KOM_SMC_RESUME) && dispPage == atkr 
            ==> enc_enc_conf_eq(s1', s2', d1', d2', atkr))
{
    reveal_ValidRegState();
    var callno, arg1, arg2, arg3, arg4
        := s1.regs[R0], s1.regs[R1], s1.regs[R2], s1.regs[R3], s1.regs[R4];
    var e1', e2' := s1'.regs[R0], s2'.regs[R0];

    if(callno == KOM_SMC_QUERY){
        assume false;
    }
    if(callno == KOM_SMC_GETPHYSPAGES){
        assume false;
    }
    if(callno == KOM_SMC_INIT_ADDRSPACE){
       initAddrspace_enc_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, atkr);
    }
    if(callno == KOM_SMC_INIT_DISPATCHER){
       initDispatcher_enc_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3, atkr);
    }
    if(callno == KOM_SMC_INIT_L2PTABLE){
       initL2PTable_enc_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3, atkr);
    }
    if(callno == KOM_SMC_MAP_SECURE){
       mapSecure_enc_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3, arg4, atkr);
    }
    if(callno == KOM_SMC_MAP_INSECURE){
       mapInsecure_enc_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3, atkr);
    }
    if(callno == KOM_SMC_REMOVE){
       remove_enc_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, atkr);
    }
    if(callno == KOM_SMC_FINALISE){
       finalise_enc_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, atkr);
    }
    if(callno == KOM_SMC_ENTER){
       enter_enc_enc_conf_ni(s1, d1, s1', d1', s2, d2, s2', d2', arg1, arg2, arg3, arg4, atkr);
    }
    if(callno == KOM_SMC_RESUME){
       resume_enc_enc_conf_ni(s1, d1, s1', d1', s2, d2, s2', d2', arg1, atkr);
    }
    if(callno == KOM_SMC_STOP){
       assume false;
       // This guy's not happy about a precond.
       stop_enc_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, atkr);
    }
}

lemma enter_enc_enc_conf_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                            s2: state, d2: PageDb, s2':state, d2': PageDb,
                            dispPage: word, arg1: word, arg2: word, arg3: word,
                            atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    requires smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    requires dispPage == atkr ==> enc_enc_conf_eq(s1, s2, d1, d2, atkr)
    ensures  valDispPage(d1', atkr) && valDispPage(d2', atkr) &&
        enc_enc_conf_eqpdb(d1', d2', atkr)
    ensures  dispPage == atkr ==> enc_enc_conf_eq(s1', s2', d1', d2', atkr)
{
    // TODO proveme
    assume false;
}

lemma resume_enc_enc_conf_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                            s2: state, d2: PageDb, s2':state, d2': PageDb,
                            dispPage: word,
                            atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires smc_resume(s1, d1, s1', d1', dispPage)
    requires smc_resume(s2, d2, s2', d2', dispPage)
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    requires dispPage == atkr ==> enc_enc_conf_eq(s1, s2, d1, d2, atkr)
    ensures  valDispPage(d1', atkr) && valDispPage(d2', atkr) &&
        enc_enc_conf_eqpdb(d1', d2', atkr)
    ensures  dispPage == atkr ==> enc_enc_conf_eq(s1', s2', d1', d2', atkr)
{
    // TODO proveme
    assume false;
}

lemma initAddrspace_enc_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                    d2: PageDb, d2': PageDb, e2':word,
                                    addrspacePage:word, l1PTPage:word,
                                    atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_initAddrspace(d1, addrspacePage, l1PTPage) == (d1', e1')
    requires smc_initAddrspace(d2, addrspacePage, l1PTPage) == (d2', e2')
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    ensures enc_enc_conf_eqpdb(d1', d2', atkr) 
    // Not sure that the following is really needed... I don't think the 
    // enclaves can observe the error ?
    // If this is needed, it should be pushed to the top-level thing
    ensures (validPageNr(addrspacePage) &&
        (d1[atkr].addrspace == addrspacePage ||
            d2[atkr].addrspace == addrspacePage))
        ==> e1' == e2'
{
    var atkr_asp := d1[atkr].addrspace;
    if( atkr_asp == addrspacePage ) {
        assert enc_enc_conf_eqpdb(d1', d2', atkr);
        assert e1' == e2';
    } else {
        assert enc_enc_conf_eqpdb(d1', d2', atkr) by {
            assert forall n : PageNr :: pgInAddrSpc(d1', n, atkr_asp) <==>
                pgInAddrSpc(d2', n, atkr_asp) by {
                    if(e1' == KOM_ERR_SUCCESS) {
                        assert !pgInAddrSpc(d1', addrspacePage, atkr_asp);
                        assert !pgInAddrSpc(d1', l1PTPage, atkr_asp);
                        assert !pgInAddrSpc(d2', addrspacePage, atkr_asp);
                        assert !pgInAddrSpc(d2', l1PTPage, atkr_asp);
                        forall( n | validPageNr(n) && n != addrspacePage &&
                            n != l1PTPage && !pgInAddrSpc(d1, n, atkr_asp))
                            ensures !pgInAddrSpc(d1', n, atkr_asp) { }
                        forall( n | validPageNr(n) && n != addrspacePage &&
                            n != l1PTPage && !pgInAddrSpc(d2, n, atkr_asp))   
                            ensures !pgInAddrSpc(d2', n, atkr_asp) { }
                        assert forall n : PageNr :: pgInAddrSpc(d1', n, atkr_asp) <==>
                            pgInAddrSpc(d2', n, atkr_asp);
                    }
                }
        }
    }
}

lemma initDispatcher_enc_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                     d2: PageDb, d2': PageDb, e2':word,
                                     page:word, addrspacePage:word, entrypoint:word,
                                     atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_initDispatcher(d1, page, addrspacePage, entrypoint) == (d1', e1')
    requires smc_initDispatcher(d2, page, addrspacePage, entrypoint) == (d2', e2')
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    ensures enc_enc_conf_eqpdb(d1', d2', atkr) 
{
    // PROVEME
    assume false;
}

lemma initL2PTable_enc_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                   d2: PageDb, d2': PageDb, e2':word,
                                   page:word, addrspacePage:word, l1index:word,
                                   atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_initL2PTable(d1, page, addrspacePage, l1index) == (d1', e1')
    requires smc_initL2PTable(d2, page, addrspacePage, l1index) == (d2', e2')
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    ensures enc_enc_conf_eqpdb(d1', d2', atkr) 
{
    // PROVEME
    assume false;
}

lemma mapSecure_enc_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                d2: PageDb, d2': PageDb, e2':word,
                                page:word, addrspacePage:word, mapping:word, physPage: word,
                                atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_mapSecure(d1, page, addrspacePage, mapping, physPage) == (d1', e1')
    requires smc_mapSecure(d2, page, addrspacePage, mapping, physPage) == (d2', e2')
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    ensures enc_enc_conf_eqpdb(d1', d2', atkr) 
{
    // PROVEME
    assume false;
}

lemma mapInsecure_enc_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                  d2: PageDb, d2': PageDb, e2':word,
                                  addrspacePage:word, physPage: word, mapping: word,
                                  atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_mapInsecure(d1, addrspacePage, physPage, mapping) == (d1', e1')
    requires smc_mapInsecure(d2, addrspacePage, physPage, mapping) == (d2', e2')
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    ensures enc_enc_conf_eqpdb(d1', d2', atkr) 
{
    // PROVEME
    assume false;
}

lemma remove_enc_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                             d2: PageDb, d2': PageDb, e2':word,
                             page:word,
                             atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_remove(d1, page) == (d1', e1')
    requires smc_remove(d2, page) == (d2', e2')
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    ensures  page != atkr ==> enc_enc_conf_eqpdb(d1', d2', atkr) 
{
    // PROVEME
    assume false;
}

lemma finalise_enc_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                             d2: PageDb, d2': PageDb, e2':word,
                             addrspacePage:word,
                             atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_finalise(d1, addrspacePage) == (d1', e1')
    requires smc_finalise(d2, addrspacePage) == (d2', e2')
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_enc_conf_eqpdb(d1', d2', atkr) 
{
    // PROVEME
    assume false;
}

lemma stop_enc_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                             d2: PageDb, d2': PageDb, e2':word,
                             addrspacePage:word,
                             atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_stop(d1, addrspacePage) == (d1', e1')
    requires smc_stop(d2, addrspacePage) == (d2', e2')
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_enc_conf_eqpdb(d1', d2', atkr) 
{
    // PROVEME
    assume false;
}


//-----------------------------------------------------------------------------
// Enclave-Enclave Integrity
//-----------------------------------------------------------------------------

lemma enter_enc_enc_integ_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                            s2: state, d2: PageDb, s2':state, d2': PageDb,
                    dispPage: word, arg1: word, arg2: word, arg3: word)
    requires SaneState(s1) && validPageDb(d1) && SaneState(s1') && validPageDb(d1')
    requires SaneState(s2) && validPageDb(d2) && SaneState(s2') && validPageDb(d2')
    requires pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s1'.m, d1') 
    requires pageDbCorresponds(s2.m, d2) && pageDbCorresponds(s2'.m, d2') 
    requires validPageNr(dispPage) && valDispPage(d1, dispPage) && valDispPage(d1', dispPage)
    // If smc_enter(s1, d1) => (s1', d1')
    requires smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    // and smc_enter(s2, d2) => (s2', d2')
    requires smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    // s.t. (s1, d1) =_{!disp} (s2, d2)
    requires enc_enc_integ_eqpdb(d1, d2, dispPage)
    requires enc_enc_integ_eq(s1, s2, d1, d2, dispPage)
    // then (s1', d1') =_{!disp} (s2', d2')
    ensures  enc_enc_integ_eqpdb(d1', d2', dispPage)
    ensures  enc_enc_integ_eq(s1', s2', d1', d2', dispPage)
{
    // TODO proveme
    assume false;
}

