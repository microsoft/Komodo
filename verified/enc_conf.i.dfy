include "sec_prop.s.dfy"
include "pagedb.s.dfy"
include "entry.s.dfy"
include "sec_prop_util.i.dfy"
include "enc_conf_entry.i.dfy"

//-----------------------------------------------------------------------------
// Confidentiality, Enclaves are NI with other Enclaves 
//-----------------------------------------------------------------------------
lemma lemma_enc_conf_ni(s1: state, d1: PageDb, s1': state, d1': PageDb,
                        s2: state, d2: PageDb, s2': state, d2': PageDb,
                        atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    // If smchandler(s1, d1) => (s1', d1')
    requires smchandler(s1, d1, s1', d1')
    // and smchandler(s2, d2) => (s2', d2')
    requires smchandler(s2, d2, s2', d2')
    // s.t. (s1, d1) =_{atkr} (s2, d2)
    requires same_call_args(s1, s2)
    requires InsecureMemInvariant(s1, s2) // public input to mapSecure.
    requires enc_conf_eqpdb(d1, d2, atkr)
    requires (var callno := s1.regs[R0]; var dispPage := s1.regs[R1];
        (callno == KOM_SMC_ENTER  && entering_atkr(d1, d2, dispPage, atkr, false))
                ==> enc_conf_eq_entry(s1, s2, d1, d2, atkr))
    requires (var callno := s1.regs[R0]; var dispPage := s1.regs[R1];
        (callno == KOM_SMC_RESUME  && entering_atkr(d1, d2, dispPage, atkr, true))
                ==> enc_conf_eq_entry(s1, s2, d1, d2, atkr))
    // then (s1', d1') =_{atkr} (s2', d2')
    ensures !(var callno := s1.regs[R0]; var asp := s1.regs[R1];
        callno == KOM_SMC_STOP && asp == atkr) ==>
        enc_conf_eqpdb(d1', d2', atkr)
{
    reveal_ValidRegState();
    var callno, arg1, arg2, arg3, arg4
        := s1.regs[R0], s1.regs[R1], s1.regs[R2], s1.regs[R3], s1.regs[R4];
    var e1', e2' := s1'.regs[R0], s2'.regs[R0];

    if(callno == KOM_SMC_QUERY || callno == KOM_SMC_GETPHYSPAGES){
        assert d1' == d1;
        assert d2' == d2;
        reveal_enc_conf_eqpdb();
    }
    else if(callno == KOM_SMC_INIT_ADDRSPACE){
        lemma_initAddrspace_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, atkr);
    }
    else if(callno == KOM_SMC_INIT_DISPATCHER){
        lemma_initDispatcher_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3, atkr);
    }
    else if(callno == KOM_SMC_INIT_L2PTABLE){
        lemma_initL2PTable_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3, atkr);
    }
    else if(callno == KOM_SMC_MAP_SECURE){
        assert enc_conf_eqpdb(d1', d2', atkr) by {
            reveal_enc_conf_eqpdb();
            var c1 := maybeContentsOfPhysPage(s1, arg4);
            var c2 := maybeContentsOfPhysPage(s2, arg4);
            assert contentsOk(arg4, c1) && contentsOk(arg4, c2);
            lemma_maybeContents_insec_ni(s1, s2, c1, c2, arg4);
            assert c1 == c2;
            lemma_mapSecure_enc_conf_ni(d1, c1, d1', e1', d2, c2, d2', e2', arg1, arg2, arg3, arg4, atkr);
        }
    }
    else if(callno == KOM_SMC_MAP_INSECURE){
        lemma_mapInsecure_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, arg2, arg3, atkr);
    }
    else if(callno == KOM_SMC_REMOVE){
        lemma_remove_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, atkr);
    }
    else if(callno == KOM_SMC_FINALISE){
        lemma_finalise_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, atkr);
    }
    else if(callno == KOM_SMC_ENTER){
        lemma_enter_enc_conf_ni(s1, d1, s1', d1', s2, d2, s2', d2', arg1, arg2, arg3, arg4, atkr);
    }
    else if(callno == KOM_SMC_RESUME){
        lemma_resume_enc_conf_ni(s1, d1, s1', d1', s2, d2, s2', d2', arg1, atkr);
    }
    else if(callno == KOM_SMC_STOP){
        lemma_stop_enc_conf_ni(d1, d1', e1', d2, d2', e2', arg1, atkr);
    }
    else {
        reveal_enc_conf_eqpdb();
        assert e1' == KOM_ERR_INVALID;
        assert e2' == KOM_ERR_INVALID;
        assert d1' == d1;
        assert d2' == d2;
    }
}


lemma lemma_mapSecure_enc_conf_ni_both_go(d1: PageDb, c1: Maybe<seq<word>>, d1': PageDb, e1':word,
                                  d2: PageDb, c2: Maybe<seq<word>>, d2': PageDb, e2':word,
                                  page:word, addrspacePage:word, mapping:word, 
                                  physPage: word, atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires contentsOk(physPage, c1) && contentsOk(physPage, c2)
    requires c1 == c2;
    requires e1' == KOM_ERR_SUCCESS && e2' == KOM_ERR_SUCCESS
    requires smc_mapSecure(d1, page, addrspacePage, mapping, physPage, c1) == (d1', e1')
    requires smc_mapSecure(d2, page, addrspacePage, mapping, physPage, c2) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    assert d1'[atkr].PageDbEntryTyped? <==> d1[atkr].PageDbEntryTyped?;
    assert d2'[atkr].PageDbEntryTyped? <==> d2[atkr].PageDbEntryTyped?;
    assert d2'[atkr].PageDbEntryTyped? <==> d1'[atkr].PageDbEntryTyped?;
    if( d1'[atkr].PageDbEntryTyped? ){
        assert c1 == c2;
        var data := DataPage(fromJust(c1)); 
        var ap1 := allocatePage(d1, page, addrspacePage, data);
        var ap2 := allocatePage(d2, page, addrspacePage, data);
        lemma_allocatePage_enc_conf_ni(d1, ap1.0, ap1.1, d2, ap2.0, ap2.1,
            page, addrspacePage, data, atkr);
        assert ap1.1 == e1';
        assert ap2.1 == e2';
        var abs_mapping := wordToMapping(mapping);
        var l2pte := SecureMapping(page, abs_mapping.perm.w, abs_mapping.perm.x);
        assert validL2PTE(ap1.0, addrspacePage, l2pte);
        assert validL2PTE(ap2.0, addrspacePage, l2pte);
        assert d1' == updateL2Pte(ap1.0, addrspacePage, abs_mapping, l2pte); 
        assert d2' == updateL2Pte(ap2.0, addrspacePage, abs_mapping, l2pte); 
        lemma_updateL2Pte_enc_conf_ni(ap1.0, d1', ap2.0, d2', 
            addrspacePage, abs_mapping, l2pte, atkr);
    } else {
       assert enc_conf_eqpdb(d1', d2', atkr);
    }
}

lemma lemma_mapSecure_enc_conf_ni_one_go(d1: PageDb, c1: Maybe<seq<word>>, d1': PageDb, e1':word,
                                  d2: PageDb, c2: Maybe<seq<word>>, d2': PageDb, e2':word,
                                  page:word, addrspacePage:word, mapping:word, 
                                  physPage: word, atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires contentsOk(physPage, c1) && contentsOk(physPage, c2)
    requires c1 == c2;
    requires e1' == KOM_ERR_SUCCESS && !(e2' == KOM_ERR_SUCCESS)
    requires smc_mapSecure(d1, page, addrspacePage, mapping, physPage, c1) == (d1', e1')
    requires smc_mapSecure(d2, page, addrspacePage, mapping, physPage, c2) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr)
{
    reveal_enc_conf_eqpdb();
    assert d1'[atkr].PageDbEntryTyped? <==> d1[atkr].PageDbEntryTyped?;
    assert d2'[atkr].PageDbEntryTyped? <==> d2[atkr].PageDbEntryTyped?;
    assert d2'[atkr].PageDbEntryTyped? <==> d1'[atkr].PageDbEntryTyped?;
    assert d2' == d2;
    if( d1'[atkr].PageDbEntryTyped? ){
        assert enc_conf_eqpdb(d1', d2', atkr);
    } else {
        assert enc_conf_eqpdb(d1', d2', atkr);
    }
}

lemma lemma_mapSecure_enc_conf_ni(d1: PageDb, c1: Maybe<seq<word>>, d1': PageDb, e1':word,
                                  d2: PageDb, c2: Maybe<seq<word>>, d2': PageDb, e2':word,
                                  page:word, addrspacePage:word, mapping:word, 
                                  physPage: word, atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires contentsOk(physPage, c1) && contentsOk(physPage, c2)
    requires c1 == c2;
    requires smc_mapSecure(d1, page, addrspacePage, mapping, physPage, c1) == (d1', e1')
    requires smc_mapSecure(d2, page, addrspacePage, mapping, physPage, c2) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    var go1, go2 := e1' == KOM_ERR_SUCCESS, e2' == KOM_ERR_SUCCESS; 
    if( go1 && go2 ) {
        assert enc_conf_eqpdb(d1', d2', atkr) by {
            lemma_mapSecure_enc_conf_ni_both_go(d1, c1, d1', e1',
                                  d2, c2, d2', e2',
                                  page, addrspacePage, mapping, 
                                  physPage, atkr);
        }
    }
    if( go1 && !go2 ) {
            lemma_mapSecure_enc_conf_ni_one_go(d1, c1, d1', e1',
                                  d2, c2, d2', e2',
                                  page, addrspacePage, mapping, 
                                  physPage, atkr);
    }
    if( !go1 && go2 ) {
            lemma_mapSecure_enc_conf_ni_one_go(d2, c2, d2', e2',
                                  d1, c1, d1', e1',
                                  page, addrspacePage, mapping, 
                                  physPage, atkr);
    }
    if( !go1 && !go2 ) {
        assert d1' == d1;
        assert d2' == d2;
        reveal_enc_conf_eqpdb();
        assert enc_conf_eqpdb(d1', d2', atkr);
    }
}

lemma lemma_initAddrspace_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                      d2: PageDb, d2': PageDb, e2':word,
                                      addrspacePage:word, l1PTPage:word,
                                      atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_initAddrspace(d1, addrspacePage, l1PTPage) == (d1', e1')
    requires smc_initAddrspace(d2, addrspacePage, l1PTPage) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    //var atkr_asp := d1[atkr].addrspace;
    if( atkr == addrspacePage ) {
        assert enc_conf_eqpdb(d1', d2', atkr);
        assert e1' == e2';
    } else {
        forall(n : PageNr)
            ensures pgInAddrSpc(d1', n, atkr) <==>
                pgInAddrSpc(d2', n, atkr)
        {
            if(e1' == KOM_ERR_SUCCESS) {
                assert !pgInAddrSpc(d1', addrspacePage, atkr);
                assert !pgInAddrSpc(d1', l1PTPage, atkr);
                assert !pgInAddrSpc(d2', addrspacePage, atkr);
                assert !pgInAddrSpc(d2', l1PTPage, atkr);
                forall( n | validPageNr(n) && n != addrspacePage &&
                    n != l1PTPage && !pgInAddrSpc(d1, n, atkr))
                    ensures !pgInAddrSpc(d1', n, atkr) { }
                forall( n | validPageNr(n) && n != addrspacePage &&
                    n != l1PTPage && !pgInAddrSpc(d2, n, atkr))   
                    ensures !pgInAddrSpc(d2', n, atkr) { }
                assert forall n : PageNr :: pgInAddrSpc(d1', n, atkr) <==>
                    pgInAddrSpc(d2', n, atkr);
            }
        }
    }
}

lemma lemma_initDispatcher_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                       d2: PageDb, d2': PageDb, e2':word,
                                       page:word, addrspacePage:word, entrypoint:word,
                                       atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_initDispatcher(d1, page, addrspacePage, entrypoint) == (d1', e1')
    requires smc_initDispatcher(d2, page, addrspacePage, entrypoint) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    if(isAddrspace(d1, addrspacePage) && isAddrspace(d2, addrspacePage)) {
        var disp := Dispatcher(entrypoint, false, initDispCtxt());
        assert allocatePage(d1, page, addrspacePage, disp) == (d1', e1');
        assert allocatePage(d2, page, addrspacePage, disp) == (d2', e2');
        lemma_allocatePage_enc_conf_ni(d1, d1', e1', d2, d2', e2',
            page, addrspacePage, disp, atkr);
    }
    // Get dafny to think about these cases:
    if(isAddrspace(d1, addrspacePage) && !isAddrspace(d2, addrspacePage)) {
    }
    if(!isAddrspace(d1, addrspacePage) && isAddrspace(d2, addrspacePage)) {
    }
}

predicate l2initgo(e1':word) {
    !(e1' == KOM_ERR_ALREADY_FINAL ||
        e1' == KOM_ERR_ADDRINUSE || e1' == KOM_ERR_INVALID_MAPPING ||
            e1' == KOM_ERR_INVALID_ADDRSPACE)
}

lemma lemma_initL2PTable_enc_conf_ni_one_go(d1: PageDb, d1': PageDb, e1':word,
                                     d2: PageDb, d2': PageDb, e2':word,
                                     page:word, addrspacePage:word, l1index:word,
                                     atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_initL2PTable(d1, page, addrspacePage, l1index) == (d1', e1')
    requires smc_initL2PTable(d2, page, addrspacePage, l1index) == (d2', e2')
    requires l2initgo(e1') && !l2initgo(e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    assert d1'[atkr].PageDbEntryTyped? <==> d1[atkr].PageDbEntryTyped?;
    assert d2'[atkr].PageDbEntryTyped? <==> d2[atkr].PageDbEntryTyped?;
    assert d2'[atkr].PageDbEntryTyped? <==> d1'[atkr].PageDbEntryTyped?;
    assert d2' == d2;
    if( d1'[atkr].PageDbEntryTyped? ){
        assert enc_conf_eqpdb(d1', d2', atkr);
    } else {
        assert enc_conf_eqpdb(d1', d2', atkr);
    }
}

lemma lemma_initL2PTable_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                     d2: PageDb, d2': PageDb, e2':word,
                                     page:word, addrspacePage:word, l1index:word,
                                     atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_initL2PTable(d1, page, addrspacePage, l1index) == (d1', e1')
    requires smc_initL2PTable(d2, page, addrspacePage, l1index) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    var ex1_alloc := l2initgo(e1');
    var ex2_alloc := l2initgo(e2');
    if( ex1_alloc && ex2_alloc) {
        var l2pt := L2PTable(SeqRepeat(NR_L2PTES, NoMapping));
        var ap1 := allocatePage(d1, page, addrspacePage, l2pt);
        var ap2 := allocatePage(d2, page, addrspacePage, l2pt);
        lemma_allocatePage_enc_conf_ni(d1, ap1.0, e1', d2, ap2.0, e2',
            page, addrspacePage, l2pt, atkr);
        assert ap1.1 != KOM_ERR_SUCCESS ==> ap1.0 == d1;
        assert ap2.1 != KOM_ERR_SUCCESS ==> ap2.0 == d2;
        if(e1' == KOM_ERR_SUCCESS){
            var l1ptnr1 := ap1.0[addrspacePage].entry.l1ptnr;
            forall(n : PageNr | n != l1ptnr1)
                ensures d1'[n] == ap1.0[n]; 
                ensures pgInAddrSpc(d1', n, atkr) <==>
                    pgInAddrSpc(ap1.0, n, atkr) { }
        } else {
            assert d1' == ap1.0;
        }
        if(e2' == KOM_ERR_SUCCESS){
            var l1ptnr2 := ap2.0[addrspacePage].entry.l1ptnr;
            forall(n : PageNr | n != l1ptnr2)
                ensures d2'[n] == ap2.0[n]; 
                ensures pgInAddrSpc(d2', n, atkr) <==>
                    pgInAddrSpc(ap2.0, n, atkr) { }
        } else {
            assert d2' == ap2.0;
        }
    }
    if( ex1_alloc  && !ex2_alloc) { 
        lemma_initL2PTable_enc_conf_ni_one_go(
            d1, d1', e1', d2, d2', e2', page, addrspacePage, l1index, atkr);
    }
    if( !ex1_alloc && ex2_alloc ) {
        lemma_initL2PTable_enc_conf_ni_one_go(
            d2, d2', e2', d1, d1', e1', page, addrspacePage, l1index, atkr);
    }
    if( !ex1_alloc && !ex2_alloc) { 
        assert d1' == d1;
        assert d2' == d2;
    }
}


predicate contentsOk(physPage: word, contents: Maybe<seq<word>>)
{
    (physPage == 0 || physPageIsInsecureRam(physPage) ==> contents.Just?) &&
    (contents.Just? ==> |fromJust(contents)| == PAGESIZE / WORDSIZE)
}


lemma lemma_mapInsecure_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                    d2: PageDb, d2': PageDb, e2':word,
                                    addrspacePage:word, physPage: word, mapping: word,
                                    atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_mapInsecure(d1, addrspacePage, physPage, mapping) == (d1', e1')
    requires smc_mapInsecure(d2, addrspacePage, physPage, mapping) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    var go1, go2 := e1' == KOM_ERR_SUCCESS, e2' == KOM_ERR_SUCCESS; 
    if( go1 && go2 ) {
        assert enc_conf_eqpdb(d1', d2', atkr) by {
            var abs_mapping := wordToMapping(mapping);
            var l2pte := InsecureMapping(physPage, abs_mapping.perm.w);
            assert d1' == updateL2Pte(d1, addrspacePage, abs_mapping, l2pte); 
            assert d2' == updateL2Pte(d2, addrspacePage, abs_mapping, l2pte); 
            lemma_updateL2Pte_enc_conf_ni(d1, d1', d2, d2', 
                addrspacePage, abs_mapping, l2pte, atkr);
        }
    }
    if( go1 && !go2 ) { assert enc_conf_eqpdb(d1', d2', atkr); }
    if( !go1 && go2 ) { assert enc_conf_eqpdb(d1', d2', atkr); }
    if( !go1 && !go2 ) {
        assert d1' == d1;
        assert d2' == d2;
        assert enc_conf_eqpdb(d1', d2', atkr);
    }
}

lemma lemma_remove_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                               d2: PageDb, d2': PageDb, e2':word,
                               page:word,
                               atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_remove(d1, page) == (d1', e1')
    requires smc_remove(d2, page) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    if(!validPageNr(page) || d1[page].PageDbEntryFree? || 
        d2[page].PageDbEntryFree?) {
        assert d1' == d1;
        assert d2' == d2;
    } else {
        var asp1, asp2 := d1[page].addrspace, d2[page].addrspace;
        assert pgInAddrSpc(d1, page, atkr) ==> asp1 == atkr;
        assert pgInAddrSpc(d2, page, atkr) ==> asp2 == atkr;
        assert asp1 == atkr <==> asp2 == atkr;
        if(asp1 == atkr){
            if(page == atkr){
                assert d1[page].entry.Addrspace? && d2[page].entry.Addrspace?;
                assert e1' == KOM_ERR_PAGEINUSE <==> e1' == KOM_ERR_PAGEINUSE;
                if(e1' == KOM_ERR_PAGEINUSE) {
                    assert d1' == d1;
                    assert d2' == d2;
                } else {
                    assert !(d1'[atkr].PageDbEntryTyped?) && !(d2'[atkr].PageDbEntryTyped?);
                    assert d1'[atkr].PageDbEntryTyped? <==> d2'[atkr].PageDbEntryTyped?; 
                }
            } else {
                assert !(d1[page].entry.Addrspace?);
                assert !(d2[page].entry.Addrspace?);
                assert d1'[atkr].PageDbEntryTyped? <==> d2'[atkr].PageDbEntryTyped?;
                assert d1'[atkr].PageDbEntryTyped?;
                assert valAddrPage(d1', atkr) && valAddrPage(d2', atkr);
                forall(n : PageNr) ensures pgInAddrSpc(d1', n, atkr) <==>
                    pgInAddrSpc(d2', n, atkr)
                {
                    assert asp1 == asp2;
                    if( n == asp1 ){
                        assert pgInAddrSpc(d1', n, atkr);
                        assert pgInAddrSpc(d2', n, atkr);
                    }
                    if( n != page && n!= asp1 ){
                        assert pgInAddrSpc(d1', n, atkr) <==>
                            pgInAddrSpc(d1, n, atkr);
                        assert pgInAddrSpc(d2', n, atkr) <==>
                            pgInAddrSpc(d2, n, atkr);
                    }
                }
                assert forall n : PageNr | pgInAddrSpc(d1', n, atkr) ::
                    d1'[n].entry == d2'[n].entry;
            }
        } else {
            assert d1'[atkr].PageDbEntryTyped?;
            assert d2'[atkr].PageDbEntryTyped?;
            forall(n: PageNr )
                ensures pgInAddrSpc(d1', n, atkr) <==>
                    pgInAddrSpc(d1, n, atkr)
                ensures pgInAddrSpc(d2', n, atkr) <==>
                    pgInAddrSpc(d2, n, atkr) { }
        }
    }
}

lemma lemma_finalise_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                 d2: PageDb, d2': PageDb, e2':word,
                                 addrspacePage:word,
                                 atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_finalise(d1, addrspacePage) == (d1', e1')
    requires smc_finalise(d2, addrspacePage) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    if(atkr == addrspacePage) {
        assert e1' == KOM_ERR_SUCCESS <==> e2' == KOM_ERR_SUCCESS;
        if(e1' == KOM_ERR_SUCCESS){
            forall(n: PageNr)
                ensures pgInAddrSpc(d1', n, atkr) <==>
                    pgInAddrSpc(d1, n, atkr)
                ensures pgInAddrSpc(d2', n, atkr) <==>
                    pgInAddrSpc(d2, n, atkr) { }
        } else {
            assert d1' == d1;
            assert d2' == d2;
        }
    } else {
        forall(n: PageNr)
            ensures pgInAddrSpc(d1', n, atkr) <==>
                pgInAddrSpc(d1, n, atkr)
            ensures pgInAddrSpc(d2', n, atkr) <==>
                pgInAddrSpc(d2, n, atkr) { }
    }
}

lemma lemma_stop_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                             d2: PageDb, d2': PageDb, e2':word,
                             addrspacePage:word,
                             atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires smc_stop(d1, addrspacePage) == (d1', e1')
    requires smc_stop(d2, addrspacePage) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures  addrspacePage != atkr ==> enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    if(atkr == addrspacePage) {
        assert addrspacePage != atkr ==> enc_conf_eqpdb(d1', d2', atkr); 
    } else {
        forall(n : PageNr)
            ensures pgInAddrSpc(d1', n, atkr) <==> pgInAddrSpc(d2', n, atkr)
        {
            assert pgInAddrSpc(d1', n, atkr) <==> pgInAddrSpc(d1, n, atkr);
        }
    }
}

lemma lemma_allocatePage_enc_conf_ni(d1: PageDb, d1': PageDb, e1':word,
                                     d2: PageDb, d2': PageDb, e2':word,
                                     page: word, addrspacePage: PageNr, entry: PageDbEntryTyped,
                                     atkr: PageNr)
    requires ni_reqs_(d1, d1', d2, d2', atkr)
    requires validAddrspacePage(d1, addrspacePage) && 
        validAddrspacePage(d2, addrspacePage);
    requires allocatePageEntryValid(entry);
    requires allocatePage(d1, page, addrspacePage, entry) == (d1', e1')
    requires allocatePage(d2, page, addrspacePage, entry) == (d2', e2')
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    assert allocatePage_inner(d1, page, addrspacePage, entry) == (d1', e1');
    assert allocatePage_inner(d2, page, addrspacePage, entry) == (d2', e2');
    if( atkr == addrspacePage ) {
        assert valAddrPage(d1', atkr);
        assert valAddrPage(d2', atkr);
        assert valAddrPage(d1', atkr) <==> valAddrPage(d2', atkr);
       
        forall(n : PageNr)
            ensures pgInAddrSpc(d1', n, atkr) <==> pgInAddrSpc(d2', n, atkr)
         {
            if(n == atkr) {
                assert pgInAddrSpc(d1, n, atkr) <==> pgInAddrSpc(d1', n, atkr);
                assert pgInAddrSpc(d2, n, atkr) <==> pgInAddrSpc(d2', n, atkr);
            }
            if(n == page) {
                var as1 := d1[atkr].entry.state;
                assert (pageIsFree(d1, n) && as1 == InitState) ==>
                   pgInAddrSpc(d1', n, atkr);
            }
            if(n != page && n != atkr){
                assert pgInAddrSpc(d1, n, atkr) <==> pgInAddrSpc(d1', n, atkr);
                assert pgInAddrSpc(d2, n, atkr) <==> pgInAddrSpc(d2', n, atkr);
            }
         }
         forall( n : PageNr | pgInAddrSpc(d1', n, atkr)) 
             ensures d1'[n].entry == d2'[n].entry { 
             assume (e1' == KOM_ERR_PAGEINUSE) <==> (e2' == KOM_ERR_PAGEINUSE);
             if(e1' == KOM_ERR_SUCCESS){
                assert d1'[atkr].entry == d2'[atkr].entry;
                assert d1'[page].entry == d2'[page].entry;
                if(n != atkr && n != page) {
                    assert d1'[n].entry == d1[n].entry;
                }
             }
        }
    } else {
        assert valAddrPage(d1, atkr);
        assert valAddrPage(d2, atkr);
        assert valAddrPage(d1', atkr);
        assert valAddrPage(d2', atkr);

        forall(n: PageNr)
            ensures pgInAddrSpc(d1', n, atkr) <==>
                pgInAddrSpc(d2', n, atkr)
        {
            assert pgInAddrSpc(d1, n, atkr) <==> pgInAddrSpc(d1', n, atkr);
            assert pgInAddrSpc(d2, n, atkr) <==> pgInAddrSpc(d2', n, atkr);
            if(n == addrspacePage){
                assert valAddrPage(d1, n) ==> d1[n].addrspace == n;
                assert valAddrPage(d2, n) ==> d2[n].addrspace == n;
            }
            if(validPageNr(addrspacePage) && n == page){
                var a := addrspacePage; 
                if(valAddrPage(d1, a)){
                    var as1 := d1[a].entry.state;
                    assert (pageIsFree(d1, n) && as1 == InitState) ==>
                       !pgInAddrSpc(d1', n, atkr);
                }
            }
        }
    }
}

lemma lemma_updateL2Pte_enc_conf_ni(d1: PageDb, d1': PageDb,
                                    d2: PageDb, d2': PageDb,
                                    a: PageNr, mapping: Mapping, l2e: L2PTE,
                                    atkr: PageNr)
    requires ni_reqs_weak_(d1, d1', d2, d2', atkr)
    requires isAddrspace(d1, a) && isAddrspace(d2, a)
    requires validMapping(mapping, d1, a) && validMapping(mapping, d2, a)
    requires d1[a].entry.state.InitState? && d2[a].entry.state.InitState?
    requires validL2PTE(d1, a, l2e) && validL2PTE(d2, a, l2e)
    requires d1' == updateL2Pte(d1, a, mapping, l2e) 
    requires d2' == updateL2Pte(d2, a, mapping, l2e) 
    requires enc_conf_eqpdb(d1, d2, atkr)
    ensures  enc_conf_eqpdb(d1', d2', atkr) 
{
    reveal_enc_conf_eqpdb();
    assert d1[a].addrspace == a;
    assert d2[a].addrspace == a;
    var l11 := d1[d1[a].entry.l1ptnr].entry;
    var l12 := d2[d2[a].entry.l1ptnr].entry;
    var l1pte1 := fromJust(l11.l1pt[mapping.l1index]);
    var l1pte2 := fromJust(l12.l1pt[mapping.l1index]);
    assert d1[l1pte1].addrspace == a;
    assert d2[l1pte2].addrspace == a;
    forall( n: PageNr | n != l1pte1)
        ensures d1'[n] == d1[n]; 
        ensures pgInAddrSpc(d1', n, atkr) <==>
            pgInAddrSpc(d1, n, atkr) { }
    forall( n: PageNr | n != l1pte2)
        ensures d2'[n] == d2[n]; 
        ensures pgInAddrSpc(d1', n, atkr) <==>
            pgInAddrSpc(d1, n, atkr) { }
    assert d1'[l1pte1].PageDbEntryTyped?;
    assert d2'[l1pte2].PageDbEntryTyped?;
    assert d1'[l1pte1].addrspace == a;
    assert d2'[l1pte2].addrspace == a;
}

lemma lemma_maybeContents_insec_ni(s1: state, s2: state, c1: Maybe<seq<word>>, 
        c2: Maybe<seq<word>>, physPage: word)
    requires ValidState(s1) && ValidState(s2) && SaneConstants()
    requires InsecureMemInvariant(s1, s2)
    requires c1 == maybeContentsOfPhysPage(s1, physPage)
    requires c2 == maybeContentsOfPhysPage(s2, physPage)
    ensures  c1 == c2;
{
    if(physPage == 0) {
        assert c1 == c2;
    } else if( physPageIsInsecureRam(physPage) ) {
        var base := physPage * PAGESIZE + KOM_DIRECTMAP_VBASE;
        forall( a: PageNr | base <= a < base + PAGESIZE)
            ensures s1.m.addresses[a] == s2.m.addresses[a]
        {
        }
        reveal_addrRangeSeq();
        reveal_addrSeqToContents();
        assert c1 == Just(contentsOfPhysPage(s1, physPage));
        assert c2 == Just(contentsOfPhysPage(s2, physPage));
        assert contentsOfPhysPage(s1, physPage)
            == contentsOfPhysPage(s2, physPage); // seq equality
        assert c1 == c2;
    } else {
        assert c1 == c2;
    }
}

//-----------------------------------------------------------------------------
// Integrity, Enclaves are NI with other Enclaves
//-----------------------------------------------------------------------------

/*
lemma lemma_enter_enc_integ_ni(s1: state, d1: PageDb, s1':state, d1': PageDb,
                               s2: state, d2: PageDb, s2':state, d2': PageDb,
                               dispPage: word, arg1: word, arg2: word, arg3: word,
                               atkr: PageNr)
    requires ni_reqs(s1, d1, s1', d1', s2, d2, s2', d2', atkr)
    requires smc_enter(s1, d1, s1', d1', dispPage, arg1, arg2, arg3)
    requires smc_enter(s2, d2, s2', d2', dispPage, arg1, arg2, arg3)
    requires enc_integ_eqpdb(d1, d2, atkr)
    requires entering_atkr(d1, d2, dispPage, atkr, true) ==>
        enc_integ_eq(s1, s2, d1, d2, atkr)
    ensures enc_integ_eqpdb(d1', d2', atkr)
    ensures entering_atkr(d1, d2, dispPage, atkr, true) ==>
        enc_integ_eq(s1', s2', d1', d2', atkr)
{
    // TODO proveme
    assume false;
}
*/
