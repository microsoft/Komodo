include "kom_common.s.dfy"
include "pagedb.s.dfy"
include "sha/sha256.s.dfy"
include "mapping.s.dfy"

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

predicate validSparePageForAS(d:PageDb, asPg:PageNr, page:word)
    requires wellFormedPageDb(d)
{
    validPageNr(page) && d[page].PageDbEntryTyped? && d[page].addrspace == asPg
        && d[page].entry.SparePage?
}

function allocateSparePage(d:PageDb, p:PageNr, e:PageDbEntryTyped): PageDb
    requires wellFormedPageDb(d) && !pageIsFree(d, p)
{
    d[p := d[p].(entry := e)]
}

lemma lemma_allocateSparePage(d:PageDb, p:PageNr, e:PageDbEntryTyped)
    requires validPageDb(d)
    requires d[p].PageDbEntryTyped? && d[p].entry.SparePage?
    requires wellFormedPageDbEntryTyped(e)
    requires e.DataPage? || e == L2PTable(SeqRepeat(NR_L2PTES, NoMapping))
    ensures validPageDb(allocateSparePage(d, p, e))
{
    reveal validPageDb();
    var dOut := allocateSparePage(d, p, e);

    forall (n:PageNr)
        ensures validPageDbEntry(dOut, n)
    {
        assert addrspaceRefs(dOut, n) == addrspaceRefs(d, n);
        assert validPageDbEntry(d, n) && validPageDbEntry(dOut, n);
    }
}

function svcMapData(d:PageDb, asPg:PageNr, page:word, mapping:word) : (PageDb, word)
    requires validPageDb(d) && validAddrspacePage(d, asPg)
{
    reveal validPageDb();

    if !validSparePageForAS(d, asPg, page)
        then (d, KOM_ERR_INVALID_PAGENO)
    else var mapErr := isValidMappingTarget'(d, asPg, mapping);
        if mapErr != KOM_ERR_SUCCESS then (d, mapErr)
    else
        // update page to zero-filled data page, and mapping in l2
        var datapg := DataPage(SeqRepeat(PAGESIZE/WORDSIZE, 0));
        var d1 := allocateSparePage(d, page, datapg);
        lemma_allocateSparePage(d, page, datapg);
        var abs_mapping := wordToMapping(mapping);
        var l2pte := SecureMapping(page, abs_mapping.perm.w, abs_mapping.perm.x);
        var d2 := updateL2Pte(d1, asPg, abs_mapping, l2pte);
        (d2, KOM_ERR_SUCCESS)
}

function svcInitL2PTable(d:PageDb, asPg:PageNr, page:word, l1index:word) : (PageDb, word)
    requires validPageDb(d) && validAddrspacePage(d, asPg) && d[asPg].entry.state.FinalState?
{
    reveal validPageDb();

    if !(0<= l1index < NR_L1PTES) then (d, KOM_ERR_INVALID_MAPPING)
    else if !validSparePageForAS(d, asPg, page) then (d, KOM_ERR_INVALID_PAGENO)
    else if l1indexInUse(d, asPg, l1index) then (d, KOM_ERR_ADDRINUSE)
    else
        var l2pt := L2PTable(SeqRepeat(NR_L2PTES, NoMapping));
        var d1 := allocateSparePage(d, page, l2pt);
        lemma_allocateSparePage(d, page, l2pt);
        var l1ptnr := d[asPg].entry.l1ptnr;
        var d2 := installL1PTEInPageDb(d1, l1ptnr, page, l1index);
        (d2, KOM_ERR_SUCCESS)
}

function svcHandled(s:state, d:PageDb, dispPg:PageNr): (SvcReturnRegs, PageDb)
    requires validPageDb(d) && finalDispatcher(d, dispPg)
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
    else if callno == KOM_SVC_INIT_L2PTABLE then
        var (retDb, retErr) := svcInitL2PTable(d, addrspace, s.regs[R1], s.regs[R2]);
        (success_regs.(0 := retErr), retDb)
    else
        (success_regs.(0 := KOM_ERR_INVALID), d)
}
