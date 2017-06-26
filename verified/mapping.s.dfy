include "kom_common.s.dfy"
include "pagedb.s.dfy"

predicate l1indexInUse(d: PageDb, a: PageNr, l1index: int)
    requires validPageDb(d)
    requires isAddrspace(d, a)
    requires !stoppedAddrspace(d[a])
    requires 0 <= l1index < NR_L1PTES
{
    assert validAddrspace(d, a) by { reveal_validPageDb(); }
    var l1ptnr := d[a].entry.l1ptnr;
    var l1pt := d[l1ptnr].entry;
    l1pt.l1pt[l1index].Just?
}

function updateL2Pte(d: PageDb, a: PageNr, mapping: Mapping, l2e : L2PTE)
    : PageDb 
    requires validPageDb(d)
    requires isAddrspace(d, a)
    requires validMapping(mapping,d,a)
    //requires isValidMappingTarget(d, a, mapping) == KOM_ERR_SUCCESS
    //requires d[a].entry.state.InitState?
    requires validL2PTE(d, a, l2e)
    ensures wellFormedPageDb(updateL2Pte(d, a, mapping, l2e))
{
    var addrspace := d[a].entry;
    assert validAddrspace(d, a) by { reveal_validPageDb(); }
    var l1 := d[addrspace.l1ptnr].entry;
    var l1pte := fromJust(l1.l1pt[mapping.l1index]);
    var l2pt := d[l1pte].entry.l2pt;
    d[ l1pte := d[l1pte].( entry := d[l1pte].entry.( l2pt := 
        l2pt[mapping.l2index := l2e] ))]
}

function isValidMappingTarget'(d: PageDb, a: PageNr, mapping: word)
    : int // KOM_ERROR
    requires validPageDb(d)
    requires isAddrspace(d, a)
    ensures  isValidMappingTarget'(d,a,mapping) == KOM_ERR_SUCCESS ==>
        validMapping(wordToMapping(mapping),d,a)
{
    reveal validPageDb();
    reveal wordToMapping();
    var addrspace := d[a].entry;
    var l1index := l1indexFromMapping(mapping);
    var l2index := l2indexFromMapping(mapping);
    var perm := permFromMapping(mapping);
    if addrspace.state.StoppedState? then
        KOM_ERR_STOPPED
    else if !validPageNr(l1indexFromMapping(mapping)) ||
        !validPageNr(l2indexFromMapping(mapping)) then
        KOM_ERR_INVALID_MAPPING
    else 
        if(!perm.r) then KOM_ERR_INVALID_MAPPING
        else if(!(0 <= l1index < NR_L1PTES)
            || !(0 <= l2index < NR_L2PTES) ) then
            KOM_ERR_INVALID_MAPPING
        else
            assert validAddrspace(d, a);
            var l1 := d[addrspace.l1ptnr].entry;
            var l1pte := l1.l1pt[l1index];
            if(l1pte.Nothing?) then KOM_ERR_INVALID_MAPPING
            else
                var l2pt := d[fromJust(l1pte)].entry.l2pt;
                if(!l2pt[l2index].NoMapping?) then KOM_ERR_INVALID_MAPPING
                else KOM_ERR_SUCCESS
}

function isValidMappingTarget(d: PageDb, a: PageNr, mapping: word)
    : int // KOM_ERROR
    requires validPageDb(d)
    requires isAddrspace(d, a)
    ensures  isValidMappingTarget(d,a,mapping) == KOM_ERR_SUCCESS ==>
        validMapping(wordToMapping(mapping),d,a)
{
    if !d[a].entry.state.InitState? then KOM_ERR_ALREADY_FINAL
    else isValidMappingTarget'(d, a, mapping)
}

function installL1PTE(l1pt: PageDbEntryTyped, l2page: PageNr, l1index: int): PageDbEntryTyped
    requires l1pt.L1PTable? && wellFormedPageDbEntryTyped(l1pt)
    requires 0 <= l1index < NR_L1PTES
    ensures var r := installL1PTE(l1pt, l2page, l1index);
        r.L1PTable? && wellFormedPageDbEntryTyped(r)
{
    l1pt.(l1pt := l1pt.l1pt[l1index := Just(l2page)])
}

function installL1PTEInPageDb(pagedb: PageDb, l1ptnr: PageNr, l2page: PageNr,
    l1index: int): PageDb
    requires wellFormedPageDb(pagedb)
    requires pagedb[l1ptnr].PageDbEntryTyped? && pagedb[l1ptnr].entry.L1PTable?
    requires 0 <= l1index < NR_L1PTES
    ensures wellFormedPageDb(installL1PTEInPageDb(pagedb, l1ptnr, l2page, l1index))
{
    //reveal validPageDb();
    var l1ptentry := installL1PTE(pagedb[l1ptnr].entry, l2page, l1index);
    pagedb[l1ptnr := pagedb[l1ptnr].(entry := l1ptentry)]
}
