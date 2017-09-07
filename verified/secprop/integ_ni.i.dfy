include "sec_prop.s.dfy"
include "../pagedb.s.dfy"
include "../entry.s.dfy"
include "sec_prop_util.i.dfy"
include "conf_ni.i.dfy"
include "integ_ni_entry.i.dfy"

//-----------------------------------------------------------------------------
// NI proof of integriy
//-----------------------------------------------------------------------------
// The integrity of an observer enclave, obs, is protected from a malicious
// OS colluding with an enclave.
lemma lemma_enc_ni(s1: state, d1: PageDb, s1': state, d1': PageDb,
                   s2: state, d2: PageDb, s2': state, d2': PageDb,
                   obs: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', obs)
    requires smchandler(s1, d1, s1', d1')
    requires smchandler(s2, d2, s2', d2')
    requires same_call_args(s1, s2)
    requires InsecureMemInvariant(s1, s2) // public input to mapSecure.
    requires loweq_pdb(d1, d2, obs)
    requires s1.conf.nondet == s2.conf.nondet
    ensures !(var callno := s1.regs[R0]; var asp := s1.regs[R1];
        callno == KOM_SMC_STOP && asp == obs) ==>
        loweq_pdb(d1', d2', obs)
{
    reveal ValidRegState();
    var callno, arg1, arg2, arg3, arg4
        := s1.regs[R0], s1.regs[R1], s1.regs[R2], s1.regs[R3], s1.regs[R4];
    var e1', e2' := s1'.regs[R0], s2'.regs[R0];

    if(callno == KOM_SMC_QUERY || callno == KOM_SMC_GETPHYSPAGES){
        assert d1' == d1;
        assert d2' == d2;
        reveal loweq_pdb();
    }
    else if(callno == KOM_SMC_INIT_ADDRSPACE){
        lemma_initAddrspace_loweq_pdb(d1, d1', e1', d2, d2', e2', arg1, arg2, obs);
    }
    else if(callno == KOM_SMC_INIT_DISPATCHER){
        lemma_initDispatcher_loweq_pdb(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3, obs);
    }
    else if(callno == KOM_SMC_INIT_L2PTABLE){
        lemma_initL2PTable_loweq_pdb(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3, obs);
    }
    else if(callno == KOM_SMC_MAP_SECURE){
        assert loweq_pdb(d1', d2', obs) by {
            reveal loweq_pdb();
            var c1 := maybeContentsOfPhysPage(s1, arg4);
            var c2 := maybeContentsOfPhysPage(s2, arg4);
            assert contentsOk(arg4, c1) && contentsOk(arg4, c2);
            lemma_maybeContents_insec_ni(s1, s2, c1, c2, arg4);
            assert c1 == c2;
            lemma_mapSecure_loweq_pdb(d1, d1', e1', c1, d2, d2', e2', c2,
                arg1, arg2, arg3, arg4, obs);
        }
    }
    else if(callno == KOM_SMC_ALLOC_SPARE) {
        lemma_allocSpare_loweq_pdb(d1, d1', e1', d2, d2', e2', arg1, arg2, obs);
    }
    else if(callno == KOM_SMC_MAP_INSECURE){
        lemma_mapInsecure_loweq_pdb(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3, obs);
    }
    else if(callno == KOM_SMC_REMOVE){
        lemma_remove_loweq_pdb(d1, d1', e1', d2, d2', e2', arg1, obs);
    }
    else if(callno == KOM_SMC_FINALISE){
        lemma_finalise_loweq_pdb(d1, d1', e1', d2, d2', e2', arg1, obs);
    }
    else if(callno == KOM_SMC_ENTER){
        lemma_enter_enc_ni(s1, d1, s1', d1', s2, d2, s2', d2', arg1, arg2, arg3, arg4, obs);
    }
    else if(callno == KOM_SMC_RESUME){
        lemma_resume_enc_ni(s1, d1, s1', d1', s2, d2, s2', d2', arg1, obs);
    }
    else if(callno == KOM_SMC_STOP){
        lemma_stop_loweq_pdb(d1, d1', e1', d2, d2', e2', arg1, obs);
    }
    else {
        reveal loweq_pdb();
    }
}
