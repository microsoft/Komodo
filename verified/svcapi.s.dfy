include "kom_common.s.dfy"
include "pagedb.s.dfy"
include "sha/sha256.s.dfy"

predicate isReturningSvc(s:state)
    requires ValidState(s) && mode_of_state(s) != User
{
    reveal ValidRegState();
    s.conf.ex.ExSVC? && s.regs[R0] != KOM_SVC_EXIT
}

// SVCs return up to 9 registers
type SvcReturnRegs = (word, word, word, word, word, word, word, word, word)

function svcHmacAttest(s:state, d:PageDb, dispPg:PageNr): seq<word>
    requires validPageDb(d) && validDispatcherPage(d, dispPg)
    requires ValidState(s) && mode_of_state(s) != User
    requires isReturningSvc(s)
{
    var addrspace := d[dispPg].addrspace;
    assert validAddrspacePage(d, addrspace) by { reveal_validPageDb(); }
    var enclave_measurement := SHA256(WordSeqToBytes(d[addrspace].entry.measurement));
    var user_words := [s.regs[R1], s.regs[R2], s.regs[R3], s.regs[R4],
        s.regs[R5], s.regs[R6], s.regs[R7], s.regs[R8]];

    // produce an attestation
    var message := user_words + enclave_measurement + SeqRepeat(8, 0);
    HMAC_SHA256(AttestKey(), WordSeqToBytes(message))
}

function svcHmacVerify(s:state, d:PageDb, dispPg:PageNr): seq<word>
    requires validPageDb(d) && validDispatcherPage(d, dispPg)
    requires ValidState(s) && mode_of_state(s) != User
    requires isReturningSvc(s)
{
    var addrspace := d[dispPg].addrspace;
    assert validAddrspacePage(d, addrspace) by { reveal_validPageDb(); }

    // verify an attestation
    var message := d[dispPg].entry.verify_words + d[dispPg].entry.verify_measurement + SeqRepeat(8, 0);
    HMAC_SHA256(AttestKey(), WordSeqToBytes(message))
}

function svcMapData(d:PageDb, asPg:PageNr, page:word, mapping:word) : (PageDb, word)
    requires validPageDb(d) && validAddrspacePage(d, asPg)
{
    // TODO: weaken isValidMappingTarget to permit some mappings outside the InitState
    var mapErr := isValidMappingTarget(d, asPg, mapping);
    if !validPageNr(page) || pageIsFree(d, page) || d[page].addrspace != asPg
        || !d[page].entry.SparePage?
        then (d, KOM_ERR_INVALID_PAGENO)
    else if mapErr != KOM_ERR_SUCCESS
        then (d, mapErr)
    else
        // update page to zero-filled data page, and mapping in l2
        var d1 := d[page := d[page].(entry := DataPage(SeqRepeat(PAGESIZE/WORDSIZE, 0)))];
        var abs_mapping := wordToMapping(mapping);
        var l2pte := SecureMapping(page, abs_mapping.perm.w, abs_mapping.perm.x);
        var d2 := updateL2Pte(d1, asPg, abs_mapping, l2pte);
        (d2, KOM_ERR_SUCCESS)
}

function svcHandled(s:state, d:PageDb, dispPg:PageNr): (SvcReturnRegs, PageDb)
    requires validPageDb(d) && validDispatcherPage(d, dispPg)
    requires ValidState(s) && mode_of_state(s) != User
    requires isReturningSvc(s)
{
    var addrspace := d[dispPg].addrspace;
    assert validAddrspacePage(d, addrspace) by { reveal_validPageDb(); }
    var enclave_measurement := SHA256(WordSeqToBytes(d[addrspace].entry.measurement));
    var callno := s.regs[R0];
    var user_words := [s.regs[R1], s.regs[R2], s.regs[R3], s.regs[R4],
        s.regs[R5], s.regs[R6], s.regs[R7], s.regs[R8]];
    var success_regs := (KOM_ERR_SUCCESS, 0, 0, 0, 0, 0, 0, 0, 0);

    if callno == KOM_SVC_ATTEST then
        // produce an attestation
        var hmac := svcHmacAttest(s, d, dispPg);
        ((KOM_ERR_SUCCESS, hmac[0], hmac[1], hmac[2], hmac[3], hmac[4], hmac[5],
            hmac[6], hmac[7]), d)
    else if callno == KOM_SVC_VERIFY_STEP0 then
        // stash user-provided words in pagedb for a subsequent STEP1 call
        // (this is a cheesy workaround to avoid reading enclave memory)
        var ret_pagedb := d[dispPg := d[dispPg].(entry := d[dispPg].entry.(verify_words := user_words))];
        (success_regs, ret_pagedb)
    else if callno == KOM_SVC_VERIFY_STEP1 then
        // stash user-provided words in pagedb for a subsequent STEP1 call
        // (this is a cheesy workaround to avoid reading enclave memory)
        var ret_pagedb := d[dispPg := d[dispPg].(entry := d[dispPg].entry.(verify_measurement := user_words))];
        (success_regs, ret_pagedb)
    else if callno == KOM_SVC_VERIFY_STEP2 then
        // verify the attestation provided by the previous step0 call plus this
        var hmac := svcHmacVerify(s, d, dispPg);
        var ok := if user_words == hmac then 1 else 0;
        (success_regs.(1 := ok), d)
    else if callno == KOM_SVC_MAP_DATA then
        var (retDb, retErr) := svcMapData(d, addrspace, s.regs[R1], s.regs[R2]);
        (success_regs.(0 := retErr), retDb)
    // TODO: KOM_SVC_INIT_L2PTABLE, KOM_SVC_UNMAP
    else
        (success_regs.(0 := KOM_ERR_INVALID), d)
}
