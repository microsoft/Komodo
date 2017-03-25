include "sec_prop.s.dfy"
include "pagedb.s.dfy"
include "entry.s.dfy"

//-----------------------------------------------------------------------------
// Enclave-Enclave Confidentiality
//-----------------------------------------------------------------------------

lemma enter_enc_enc_conf_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                            s2: state, d2: PageDb, s2':state, d2': PageDb,
                    dispPage: word, arg1: word, arg2: word, arg3: word)
    requires SaneState(s1) && validPageDb(d1) && SaneState(s1') && validPageDb(d1')
    requires SaneState(s2) && validPageDb(d2) && SaneState(s2') && validPageDb(d2')
    requires pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s1'.m, d1') 
    requires pageDbCorresponds(s2.m, d2) && pageDbCorresponds(s2'.m, d2') 
    requires validPageNr(dispPage) && valDispPage(d1, dispPage) && 
        valDispPage(d1', dispPage)// Error case??
    // If smc_enter(s1, d1) => (s1', d1')
    requires smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    // and smc_enter(s2, d2) => (s2', d2')
    requires smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    // s.t. (s1, d1) =_{disp} (s2, d2)
    requires enc_enc_conf_eqpdb(d1, d2, dispPage)
    requires enc_enc_conf_eq(s1, s2, d1, d2, dispPage)
    // then (s1', d1') =_{disp} (s2', d2')
    ensures  enc_enc_conf_eqpdb(d1', d2', dispPage)
    ensures  enc_enc_conf_eq(s1', s2', d1', d2', dispPage)
{
    // TODO proveme
    assume false;
}

lemma initAddrspace_enc_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                    d2: PageDb, d2': PageDb, e2':word,
                                    addrspacePage:word, l1PTPage:word,
                                    atkr: word)
    requires validPageDb(d1) && validPageDb(d1') &&
        validPageDb(d2) && validPageDb(d2')
    requires validPageNr(atkr) && valDispPage(d1, atkr) && valDispPage(d2, atkr)
    requires smc_initAddrspace(d1, addrspacePage, l1PTPage) == (d1', e1')
    requires smc_initAddrspace(d2, addrspacePage, l1PTPage) == (d2', e2')
    requires enc_enc_conf_eqpdb(d1, d2, atkr)
    ensures enc_enc_conf_eqpdb(d1', d2', atkr) 
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

