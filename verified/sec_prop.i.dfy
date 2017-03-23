include "sec_prop.s.dfy"
include "pagedb.s.dfy"
include "entry.s.dfy"


lemma enter_enc_enc_conf_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                            s2: state, d2: PageDb, s2':state, d2': PageDb,
                    dispPage: word, arg1: word, arg2: word, arg3: word)
    requires SaneState(s1) && validPageDb(d1) && SaneState(s1') && validPageDb(d1')
    requires SaneState(s2) && validPageDb(d2) && SaneState(s2') && validPageDb(d2')
    requires pageDbCorresponds(s1.m, d1) && pageDbCorresponds(s1'.m, d1') 
    requires pageDbCorresponds(s1.m, d2) && pageDbCorresponds(s2'.m, d2') 
    requires validPageNr(dispPage) && valDispPage(d1, dispPage) // Error case??
    requires smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    requires smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    requires enc_enc_conf_eqpdb(d1, d2, dispPage)
    requires enc_enc_conf_eq(s1, s2, d1, d2, dispPage)
    ensures  enc_enc_conf_eqpdb(d1', d2', dispPage)
    ensures  enc_enc_conf_eq(s1', s2', d1', d2', dispPage)
{
}
