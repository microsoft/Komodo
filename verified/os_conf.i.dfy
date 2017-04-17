include "sec_prop.s.dfy"
include "pagedb.s.dfy"
include "entry.s.dfy"
include "sec_prop_util.i.dfy"

//-----------------------------------------------------------------------------
// Confidentiality, Enclave Secrets are NI with OS
//-----------------------------------------------------------------------------

lemma lemma_os_conf_ni(s1: state, d1: PageDb, s1': state, d1': PageDb,
                 s2: state, d2: PageDb, s2': state, d2': PageDb,
                 atkr: PageNr)
    requires os_ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2')
    // If smchandler(s1, d1) => (s1', d1')
    requires smchandler(s1, d1, s1', d1')
    // and smchandler(s2, d2) => (s2', d2')
    requires smchandler(s2, d2, s2', d2')
    // s.t. (s1, d1) =_{os} (s2, d2)
    requires os_conf_eq(s1, d1, s2, d2)
    // then (s1', d1') =_{os} (s2', d2')
    ensures os_conf_eq(s1', d1', s2', d2')
{
    reveal_ValidRegState();
    var callno, arg1, arg2, arg3, arg4
        := s1.regs[R0], s1.regs[R1], s1.regs[R2], s1.regs[R3], s1.regs[R4];
    var e1', e2' := s1'.regs[R0], s2'.regs[R0];

    var entry := callno == KOM_SMC_ENTER || callno == KOM_SMC_RESUME;

    lemma_smchandlerInvariant_regs_ni(s1, s1', s2, s2', entry);

    if(callno == KOM_SMC_QUERY || callno == KOM_SMC_GETPHYSPAGES){
        // assert s1'.m == s1.m;
        // assert s2'.m == s2.m;
    }
    else if(callno == KOM_SMC_INIT_ADDRSPACE){
        lemma_initAddrspace_os_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2);
        lemma_integrate_reg_equiv(s1', s2');
    }
    else if(callno == KOM_SMC_INIT_DISPATCHER){
        lemma_initDispatcher_os_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3);
        lemma_integrate_reg_equiv(s1', s2');
    }
    else if(callno == KOM_SMC_INIT_L2PTABLE){
        lemma_initL2PTable_os_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3);
        lemma_integrate_reg_equiv(s1', s2');
    }
    else if(callno == KOM_SMC_MAP_SECURE){
        var c1 := maybeContentsOfPhysPage(s1, arg4);
        var c2 := maybeContentsOfPhysPage(s2, arg4);
        assert contentsOk(arg4, c1) && contentsOk(arg4, c2) by
            { reveal_enc_conf_eqpdb(); }
        lemma_maybeContents_insec_ni(s1, s2, c1, c2, arg4);
        assert c1 == c2;
        lemma_mapSecure_os_conf_ni(d1, d1', e1', c1, d2, d2', e2', c2,
            arg1, arg2, arg3, arg4);
        lemma_integrate_reg_equiv(s1', s2');
    }
    else if(callno == KOM_SMC_MAP_INSECURE){
        lemma_mapInsecure_os_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3);
        lemma_integrate_reg_equiv(s1', s2');
    }
    else if(callno == KOM_SMC_REMOVE){
        lemma_remove_os_conf_ni(d1, d1', e1', d2, d2', e2', arg1);
        lemma_integrate_reg_equiv(s1', s2');
    }
    else if(callno == KOM_SMC_FINALISE){
        lemma_finalise_os_conf_ni(d1, d1', e1', d2, d2', e2', arg1);
        lemma_integrate_reg_equiv(s1', s2');
    }
    else if(callno == KOM_SMC_ENTER){
        assume false;
    }
    else if(callno == KOM_SMC_RESUME){
        assume false;
    }
    else if(callno == KOM_SMC_STOP){
        lemma_stop_os_conf_ni(d1, d1', e1', d2, d2', e2', arg1);
        lemma_integrate_reg_equiv(s1', s2');
    }
    else {
        assert e1' == KOM_ERR_INVALID;
        assert e2' == KOM_ERR_INVALID;
        lemma_integrate_reg_equiv(s1', s2');
    }
}

predicate non_ret_os_regs_equiv(s1: state, s2: state)
    requires ValidState(s1) && ValidState(s2)
{
   reveal_ValidRegState();
   reveal_ValidSRegState();
   s1.regs[R2]  == s2.regs[R2] &&
   s1.regs[R3]  == s2.regs[R3] &&
   s1.regs[R4]  == s2.regs[R4] &&
   s1.regs[R5]  == s2.regs[R5] &&
   s1.regs[R6]  == s2.regs[R6] &&
   s1.regs[R7]  == s2.regs[R7] &&
   s1.regs[R8]  == s2.regs[R8] &&
   s1.regs[R9]  == s2.regs[R9] &&
   s1.regs[R10] == s2.regs[R10] &&
   s1.regs[R11] == s2.regs[R11] &&
   s1.regs[R12] == s2.regs[R12] &&
   s1.regs[LR(User)]       == s2.regs[LR(User)] &&
   s1.regs[LR(FIQ)]        == s2.regs[LR(FIQ)] &&
   s1.regs[LR(IRQ)]        == s2.regs[LR(IRQ)] &&
   s1.regs[LR(Supervisor)] == s2.regs[LR(Supervisor)] &&
   s1.regs[LR(Abort)]      == s2.regs[LR(Abort)] &&
   s1.regs[LR(Undefined)]  == s2.regs[LR(Undefined)] &&
   s1.regs[SP(User)]       == s2.regs[SP(User)] &&
   s1.regs[SP(FIQ)]        == s2.regs[SP(FIQ)] &&
   s1.regs[SP(IRQ)]        == s2.regs[SP(IRQ)] &&
   s1.regs[SP(Supervisor)] == s2.regs[SP(Supervisor)] &&
   s1.regs[SP(Abort)]      == s2.regs[SP(Abort)] &&
   s1.regs[SP(Undefined)]  == s2.regs[SP(Undefined)]
}

predicate ret_regs_equiv(s1:state, s2:state)
    requires ValidState(s1) && ValidState(s2)
{
    reveal_ValidRegState();
    s1.regs[R0] == s2.regs[R0] &&
    s1.regs[R1] == s2.regs[R1]
}

lemma lemma_integrate_reg_equiv(s1: state, s2: state)
    requires ValidState(s1) && ValidState(s2)
    requires non_ret_os_regs_equiv(s1, s2)
    requires ret_regs_equiv(s1, s2)
    ensures  os_regs_equiv(s1, s2)
{
}

lemma lemma_smchandlerInvariant_regs_ni(
    s1: state, s1': state, s2: state, s2': state,
    entry: bool)
    requires ValidState(s1) && ValidState(s1')
    requires ValidState(s2) && ValidState(s2')
    requires smchandlerInvariant(s1, s1', entry)
    requires smchandlerInvariant(s2, s2', entry)
    requires os_regs_equiv(s1, s2)
    requires os_ctrl_eq(s1, s2)
    requires InsecureMemInvariant(s1, s2)
    ensures  !entry ==> os_ctrl_eq(s1', s2')
    ensures  !entry ==> InsecureMemInvariant(s1', s2')
    ensures  !entry ==> non_ret_os_regs_equiv(s1', s2')
{
    if(!entry) {
        assert forall m | m != User ::
            s1.sregs[spsr(m)] == s1'.sregs[spsr(m)];
        assert forall m | m != User ::
            s2.sregs[spsr(m)] == s2'.sregs[spsr(m)];
        assert os_ctrl_eq(s1', s2');
    }
}

lemma lemma_initAddrspace_os_conf_ni(
    d1: PageDb, d1': PageDb, e1': word,
    d2: PageDb, d2': PageDb, e2': word,
    addrspacePage: word, l1PTPage: word)
    requires validPageDb(d1) && validPageDb(d2)
    requires validPageDb(d1') && validPageDb(d2')
    requires smc_initAddrspace(d1, addrspacePage, l1PTPage) == (d1', e1')
    requires smc_initAddrspace(d2, addrspacePage, l1PTPage) == (d2', e2')
    requires os_conf_eqpdb(d1, d2)
    ensures  os_conf_eqpdb(d1', d2')
    ensures  e1' == e2'
{
    reveal os_conf_eqpdb();
}

lemma lemma_initDispatcher_os_conf_ni(
    d1: PageDb, d1': PageDb, e1': word,
    d2: PageDb, d2': PageDb, e2': word,
    page:word, addrspacePage:word, entrypoint:word)
    requires validPageDb(d1) && validPageDb(d2)
    requires validPageDb(d1') && validPageDb(d2')
    requires smc_initDispatcher(d1, page, addrspacePage, entrypoint) == (d1', e1')
    requires smc_initDispatcher(d2, page, addrspacePage, entrypoint) == (d2', e2')
    requires os_conf_eqpdb(d1, d2)
    ensures  os_conf_eqpdb(d1', d2')
    ensures  e1' == e2'
{
    reveal os_conf_eqpdb();
}

lemma lemma_initL2PTable_os_conf_ni(
    d1: PageDb, d1': PageDb, e1': word,
    d2: PageDb, d2': PageDb, e2': word,
    page: word, addrspacePage: word, l1index:word)
    requires validPageDb(d1) && validPageDb(d2)
    requires validPageDb(d1') && validPageDb(d2')
    requires smc_initL2PTable(d1, page, addrspacePage, l1index) == (d1', e1')
    requires smc_initL2PTable(d2, page, addrspacePage, l1index) == (d2', e2')
    requires os_conf_eqpdb(d1, d2)
    ensures  os_conf_eqpdb(d1', d2')
    ensures  e1' == e2'
{
    reveal os_conf_eqpdb();
}

lemma lemma_mapSecure_os_conf_ni(
    d1: PageDb, d1': PageDb, e1': word, c1: Maybe<seq<word>>,
    d2: PageDb, d2': PageDb, e2': word, c2: Maybe<seq<word>>,
    page: word, addrspacePage: word,
    mapping: word, physPage: word)
    requires validPageDb(d1) && validPageDb(d2)
    requires validPageDb(d1') && validPageDb(d2')
    requires contentsOk(physPage, c1) && contentsOk(physPage, c2)
    requires c1 == c2;
    requires smc_mapSecure(d1, page, addrspacePage, mapping, physPage, c1) == (d1', e1')
    requires smc_mapSecure(d2, page, addrspacePage, mapping, physPage, c2) == (d2', e2')
    requires os_conf_eqpdb(d1, d2)
    ensures  os_conf_eqpdb(d1', d2')
    ensures  e1' == e2'
{
    reveal os_conf_eqpdb();
}

lemma lemma_mapInsecure_os_conf_ni(
    d1: PageDb, d1': PageDb, e1': word,
    d2: PageDb, d2': PageDb, e2': word,
    addrspacePage: word, mapping: word, physPage: word)
    requires validPageDb(d1) && validPageDb(d2)
    requires validPageDb(d1') && validPageDb(d2')
    requires smc_mapInsecure(d1, addrspacePage, mapping, physPage) == (d1', e1')
    requires smc_mapInsecure(d2, addrspacePage, mapping, physPage) == (d2', e2')
    requires os_conf_eqpdb(d1, d2)
    ensures  os_conf_eqpdb(d1', d2')
    ensures  e1' == e2'
{
    reveal os_conf_eqpdb();
}

lemma lemma_remove_os_conf_ni(
    d1: PageDb, d1': PageDb, e1': word,
    d2: PageDb, d2': PageDb, e2': word,
    page: word)
    requires validPageDb(d1) && validPageDb(d2)
    requires validPageDb(d1') && validPageDb(d2')
    requires smc_remove(d1, page) == (d1', e1')
    requires smc_remove(d2, page) == (d2', e2')
    requires os_conf_eqpdb(d1, d2)
    ensures  os_conf_eqpdb(d1', d2')
    ensures  e1' == e2'
{
    reveal os_conf_eqpdb();
}

lemma lemma_finalise_os_conf_ni(
    d1: PageDb, d1': PageDb, e1': word,
    d2: PageDb, d2': PageDb, e2': word,
    addrspacePage: word)
    requires validPageDb(d1) && validPageDb(d2)
    requires validPageDb(d1') && validPageDb(d2')
    requires smc_finalise(d1, addrspacePage) == (d1', e1')
    requires smc_finalise(d2, addrspacePage) == (d2', e2')
    requires os_conf_eqpdb(d1, d2)
    ensures  os_conf_eqpdb(d1', d2')
    ensures  e1' == e2'
{
    reveal os_conf_eqpdb();
}

lemma lemma_stop_os_conf_ni(
    d1: PageDb, d1': PageDb, e1': word,
    d2: PageDb, d2': PageDb, e2': word,
    addrspacePage: word)
    requires validPageDb(d1) && validPageDb(d2)
    requires validPageDb(d1') && validPageDb(d2')
    requires smc_stop(d1, addrspacePage) == (d1', e1')
    requires smc_stop(d2, addrspacePage) == (d2', e2')
    requires os_conf_eqpdb(d1, d2)
    ensures  os_conf_eqpdb(d1', d2')
    ensures  e1' == e2'
{
    reveal os_conf_eqpdb();
}
