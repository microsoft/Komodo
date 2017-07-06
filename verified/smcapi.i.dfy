include "smcapi.s.dfy"
include "entry.i.dfy"
include "Sets.i.dfy"

//=============================================================================
// Hoare Specification of Monitor Calls
//=============================================================================
function {:opaque} smc_initAddrspace_premium(pageDbIn: PageDb, addrspacePage: word,
    l1PTPage: word) : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn);
    ensures  validPageDb(smc_initAddrspace_premium(pageDbIn, addrspacePage, l1PTPage).0);
{
    initAddrspacePreservesPageDBValidity(pageDbIn, addrspacePage, l1PTPage);
    smc_initAddrspace(pageDbIn, addrspacePage, l1PTPage)
}

function {:opaque} smc_initDispatcher_premium(pageDbIn: PageDb, page:word,
    addrspacePage:word, entrypoint:word) : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn);
    ensures  validPageDb(smc_initDispatcher_premium(pageDbIn, page, addrspacePage, entrypoint).0);
{
    initDispatcherPreservesPageDBValidity(pageDbIn, page, addrspacePage, entrypoint);
    smc_initDispatcher(pageDbIn, page, addrspacePage, entrypoint)
}

function {:opaque} smc_initL2PTable_premium(pageDbIn: PageDb, page: word,
    addrspacePage: word, l1index: word) : (PageDb, word)
    requires validPageDb(pageDbIn)
    ensures validPageDb(smc_initL2PTable_premium(pageDbIn, page, addrspacePage, l1index).0)
{
    initL2PTablePreservesPageDBValidity(pageDbIn, page, addrspacePage, l1index);
    smc_initL2PTable(pageDbIn, page, addrspacePage, l1index)
}

function {:opaque} smc_remove_premium(pageDbIn: PageDb, page: word)
    : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_remove_premium(pageDbIn, page).0)
{
    removePreservesPageDBValidity(pageDbIn, page);
    smc_remove(pageDbIn, page)
}

function {:opaque} smc_mapSecure_premium(pageDbIn: PageDb, page: word,
    addrspacePage: word, mapping: word, physPage: word, contents: Maybe<seq<word>>) : (PageDb, word) // PageDbOut, KOM_ERR
    requires validPageDb(pageDbIn)
    requires physPage == 0 || physPageIsInsecureRam(physPage) ==> contents.Just?
    requires contents.Just? ==> |fromJust(contents)| == PAGESIZE / WORDSIZE
    ensures  validPageDb(smc_mapSecure_premium(pageDbIn, page, addrspacePage, 
        mapping, physPage, contents).0)
    ensures  smc_mapSecure_premium(pageDbIn, page, addrspacePage, mapping, physPage, contents) ==
        smc_mapSecure(pageDbIn, page, addrspacePage, mapping, physPage,  contents);
{
    mapSecurePreservesPageDBValidity(pageDbIn, page, addrspacePage, mapping, 
        physPage, contents);
    smc_mapSecure(pageDbIn, page, addrspacePage, mapping, physPage, contents)
}

function {:opaque} smc_mapInsecure_premium(pageDbIn: PageDb, addrspacePage: word,
    physPage: word, mapping : word) : (PageDb, word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_mapInsecure_premium(pageDbIn, addrspacePage, physPage, mapping).0)
    ensures smc_mapInsecure_premium(pageDbIn, addrspacePage, physPage, mapping) ==
        smc_mapInsecure(pageDbIn, addrspacePage, physPage, mapping) 
{
    mapInsecurePreservesPageDbValidity(pageDbIn, addrspacePage, physPage, mapping);
    smc_mapInsecure(pageDbIn, addrspacePage, physPage, mapping)
}

function {:opaque} smc_finalise_premium(pageDbIn: PageDb, addrspacePage: word)
    : (PageDb, word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_finalise_premium(pageDbIn, addrspacePage).0)
{
    finalisePreservesPageDbValidity(pageDbIn, addrspacePage);
    smc_finalise(pageDbIn, addrspacePage)
}

function {:opaque} smc_stop_premium(pageDbIn: PageDb, addrspacePage: word)
    : (PageDb, word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_stop_premium(pageDbIn, addrspacePage).0)
{
    stopPreservesPageDbValidity(pageDbIn, addrspacePage);
    smc_stop(pageDbIn, addrspacePage)
}

//=============================================================================
// Utilities
//=============================================================================

lemma lemma_sha256_length_helper(m:seq<seq<word>>)
    requires (forall i :: 0 <= i < |m| ==> |m[i]| == SHA_BLOCKSIZE)
    ensures |ConcatenateSeqs(m)| == SHA_BLOCKSIZE * |m|
{
    if (|m| != 0)
    {
        lemma_sha256_length_helper(m[1..]);
    }
}

lemma lemma_sha256_length(z:SHA256Trace)
    requires IsCompleteSHA256Trace(z)
    ensures |ConcatenateSeqs(z.M)| == SHA_BLOCKSIZE * |z.M|
{
    lemma_sha256_length_helper(z.M);
}

// TODO: merge this with BoundedAddrspaceRefs in allocate_page.sdfy
lemma BoundedAddrspaceRefs'(d:PageDb, n:PageNr)
    requires validPageDb(d)
    requires isAddrspace(d, n)
    ensures d[n].entry.refcount <= KOM_SECURE_NPAGES
{
    reveal validPageNrs();
    reveal validPageDb();
    assert addrspaceRefs(d,n) <= validPageNrs();
    assert d[n].entry.refcount == |addrspaceRefs(d,n)|;
    lemma_SubsetCardinality(addrspaceRefs(d,n), validPageNrs());
}

lemma BoundedShaLength(d:PageDb, n:PageNr)
    requires validPageDb(d)
    requires isAddrspace(d, n)
    requires IsCompleteSHA256Trace(d[n].entry.shatrace)
    requires !stoppedAddrspace(d[n])
    ensures |d[n].entry.shatrace.M| < 0x1000_0000
    ensures |d[n].entry.measurement| < 0x1000_0000
{
    assert validAddrspace(d, n) by { reveal validPageDb(); }
    BoundedAddrspaceRefs'(d, n);
    lemma_sha256_length(d[n].entry.shatrace);
    assert |d[n].entry.shatrace.M| <= KOM_SECURE_NPAGES * (1 + 64);
}

lemma GrowShaLength(d:PageDb, n:PageNr, metadata:seq<word>, contents:seq<word>)
    requires validPageDb(d)
    requires isAddrspace(d, n)
    requires IsCompleteSHA256Trace(d[n].entry.shatrace)
    requires !stoppedAddrspace(d[n])
    requires |metadata| <= SHA_BLOCKSIZE
    requires |contents| % SHA_BLOCKSIZE == 0
    requires |contents| <= PAGESIZE / WORDSIZE
    ensures
        var u := updateMeasurement(d, n, metadata, contents);
        |u[n].entry.shatrace.M| <= (d[n].entry.refcount + 1) * (1 + PAGESIZE / (WORDSIZE * SHA_BLOCKSIZE))
{
    var u := updateMeasurement(d, n, metadata, contents);
    assert |d[n].entry.shatrace.M| <= d[n].entry.refcount * (1 + PAGESIZE / (WORDSIZE * SHA_BLOCKSIZE))
        by { reveal validPageDb(); }
    assert SHA_BLOCKSIZE * |d[n].entry.shatrace.M| == |d[n].entry.measurement| by
    {
        reveal validPageDb();
        lemma_sha256_length(d[n].entry.shatrace);
    }
    lemma_sha256_length(u[n].entry.shatrace);

    var k := 1 + PAGESIZE / (WORDSIZE * SHA_BLOCKSIZE);
    assert k == 65;
    lemma_MulDistrib(d[n].entry.refcount, 1, k);
}

// TODO: consolidate with lemma_ConcatenateSeqs_Adds
lemma lemma_ConcatenateSeqs_Adds'<T>(s:seq<seq<T>>, s':seq<seq<T>>)
    ensures ConcatenateSeqs(s + s') == ConcatenateSeqs(s) + ConcatenateSeqs(s'); 
{
    if s == [] {
    } else {
        calc {
            ConcatenateSeqs(s + s');
            s[0] + ConcatenateSeqs((s + s')[1..]);
                { assert (s + s')[1..] == s[1..] + s'; }
            s[0] + ConcatenateSeqs(s[1..] + s');
                { lemma_ConcatenateSeqs_Adds'(s[1..], s'); }
            s[0] + ConcatenateSeqs(s[1..]) + ConcatenateSeqs(s');
            ConcatenateSeqs(s) + ConcatenateSeqs(s'); 
        }
    }
}

predicate MemPreservingExceptRangeOrStack(s:state, r:state, base:int, limit:int)
    requires ValidState(s) && ValidState(r);
    requires limit >= base;
{
    forall m:addr :: ValidMem(m) && !(base <= m < limit) && !(StackLimit() < m <= StackBase())
        ==> MemContents(s.m, m) == MemContents(r.m, m)
}

lemma AllButOnePageOrStackPreserving(n:PageNr,s:state,r:state)
    requires SaneState(s) && SaneState(r)
    requires MemPreservingExceptRangeOrStack(s, r, page_monvaddr(n), page_monvaddr(n) + PAGESIZE)
    ensures forall p :: validPageNr(p) && p != n
        ==> extractPage(s.m, p) == extractPage(r.m, p)
{
    forall (p, a:addr | validPageNr(p) && p != n && addrInPage(a, p))
        ensures MemContents(s.m, a) == MemContents(r.m, a)
        {}
}

//=============================================================================
// Properties of Monitor Calls
//=============================================================================

//-----------------------------------------------------------------------------
// PageDb Validity Preservation
//-----------------------------------------------------------------------------
lemma lemma_freePageRefs(d:PageDb, p:PageNr)
    requires validPageDb(d) && d[p].PageDbEntryFree?
    ensures forall a:PageNr | isAddrspace(d, a) && !d[a].entry.state.StoppedState? :: dataPageRefs(d, a, p) == {}
{
    forall a: PageNr | isAddrspace(d, a) && !d[a].entry.state.StoppedState?
        ensures dataPageRefs(d, a, p) == {}
    {
        reveal validPageDb();
        var l1ptnr := d[a].entry.l1ptnr;
        var l1pt := d[l1ptnr].entry.l1pt;
        assert forall i, j | 0 <= i < NR_L1PTES && l1pt[i].Just? && 0 <= j < NR_L2PTES
            :: validL2PTable(d, a, d[l1pt[i].v].entry.l2pt)
            && validL2PTE(d, a, d[l1pt[i].v].entry.l2pt[j]);
    }
}

lemma allocatePagePreservesPageDBValidity(pageDbIn: PageDb,
    securePage: word, addrspacePage: PageNr, entry: PageDbEntryTyped)
    requires validPageDb(pageDbIn)
    requires validAddrspacePage(pageDbIn, addrspacePage)
    requires allocatePageEntryValid(entry)
    requires !entry.L2PTable?
    ensures  validPageDb(allocatePage(pageDbIn, securePage, addrspacePage, entry).0)
{
    reveal validPageDb();
    assert validAddrspace(pageDbIn, addrspacePage);
    var result := allocatePage(pageDbIn, securePage, addrspacePage, entry);
    var pageDbOut := result.0;
    var errOut := result.1;

    if ( errOut != KOM_ERR_SUCCESS ){
        // The error case is trivial because PageDbOut == PageDbIn
    } else {
        assert validPageDbEntry(pageDbOut, addrspacePage) by {
            var oldRefs := addrspaceRefs(pageDbIn, addrspacePage);
            assert addrspaceRefs(pageDbOut, addrspacePage ) == oldRefs + {securePage};
            
            var addrspace_ := pageDbIn[addrspacePage].entry;
            var addrspace := pageDbOut[addrspacePage].entry;
            assert addrspace.refcount == |addrspaceRefs(pageDbOut, addrspacePage)|;
            assert validAddrspacePage(pageDbOut, addrspacePage);

            assert 1 + PAGESIZE / (WORDSIZE * SHA_BLOCKSIZE) == 65;
            assert addrspace_.refcount * 65 <= addrspace.refcount * 65;
        }

        forall ( n | validPageNr(n) && n != addrspacePage && n != securePage )
            ensures validPageDbEntry(pageDbOut, n)
        {
            assert validPageDbEntry(pageDbIn, n);
            assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
            if pageDbIn[n].PageDbEntryTyped? && pageDbIn[n].entry.DataPage? {
                assert dataPageRefs(pageDbIn, pageDbIn[n].addrspace, n)
                    == dataPageRefs(pageDbOut, pageDbOut[n].addrspace, n);
            }
        }

        assert validPageDbEntry(pageDbOut, securePage) by {
            if entry.DataPage? {
                lemma_freePageRefs(pageDbIn, securePage);
                assert dataPageRefs(pageDbOut, addrspacePage, securePage) == {};
            }
        }
        assert validPageDb(pageDbOut);
    }
}

lemma initAddrspacePreservesPageDBValidity(pageDbIn : PageDb,
    addrspacePage : word, l1PTPage : word)
    requires validPageDb(pageDbIn)
    ensures validPageDb(smc_initAddrspace(pageDbIn, addrspacePage, l1PTPage).0)
{
    reveal validPageDb();
    var result := smc_initAddrspace(pageDbIn, addrspacePage, l1PTPage);
    var pageDbOut := result.0;
    var errOut := result.1;

    if( errOut != KOM_ERR_SUCCESS ) {
        // The error case is trivial because PageDbOut == PageDbIn
    } else {
        // Necessary semi-manual proof of validPageDbEntry(pageDbOut, l1PTPage)
        // The interesting part of the proof deals with the contents of addrspaceRefs
        assert forall p :: p != l1PTPage ==> !(p in addrspaceRefs(pageDbOut, addrspacePage));
	      assert l1PTPage in addrspaceRefs(pageDbOut, addrspacePage);
        assert addrspaceRefs(pageDbOut, addrspacePage) == {l1PTPage};
        // only kept for readability
        assert validPageDbEntry(pageDbOut, l1PTPage);

        forall ( n:PageNr | pageDbOut[n].PageDbEntryTyped?
                          && n != addrspacePage && n != l1PTPage)
            ensures validPageDbEntry(pageDbOut, n)
        {
            assert pageDbOut[n] == pageDbIn[n];
            assert validPageDbEntry(pageDbIn, n);
            assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
            var a := pageDbIn[n].addrspace;
            assert dataPageRefs(pageDbOut, a, n) == dataPageRefs(pageDbIn, a, n);
        }
              
        assert pageDbEntriesValid(pageDbOut);
        assert validPageDb(pageDbOut);
    }
}

lemma initDispatcherPreservesPageDBValidity(pageDbIn:PageDb, page:word, addrspacePage:word,
    entrypoint:word)
    requires validPageDb(pageDbIn)
    ensures validPageDb(smc_initDispatcher(pageDbIn, page, addrspacePage, entrypoint).0)
{
    reveal validPageDb();
    var result := smc_initDispatcher(pageDbIn, page, addrspacePage, entrypoint);
    var pageDbOut := result.0;
    var errOut := result.1;

    if (errOut == KOM_ERR_SUCCESS) {
        BoundedShaLength(pageDbIn, addrspacePage);
        GrowShaLength(pageDbIn, addrspacePage, [KOM_SMC_INIT_DISPATCHER, entrypoint], []);
        var initDisp := Dispatcher(entrypoint, false, initDispCtxt(),
                                  [0, 0, 0, 0, 0, 0, 0, 0],
                                  [0, 0, 0, 0, 0, 0, 0, 0]);
        var (pagedb', err) := allocatePage(pageDbIn, page, addrspacePage, initDisp);
        allocatePagePreservesPageDBValidity(pageDbIn, page, addrspacePage, initDisp);
        forall p:PageNr | pageDbOut[p].PageDbEntryTyped?
            ensures validPageDbEntry(pageDbOut, p)
        {
            assert addrspaceRefs(pagedb', p) == addrspaceRefs(pageDbOut, p); // set equality
            if pageDbOut[p].entry.DataPage? && !hasStoppedAddrspace(pageDbOut, p) {
                var a := pageDbIn[p].addrspace;
                assert dataPageRefs(pageDbOut, a, p) == dataPageRefs(pageDbIn, a, p);
            }
        }
    }
}

lemma initL2PTablePreservesPageDBValidity(pageDbIn: PageDb, page: word,
    addrspacePage: word, l1index: word)
    requires validPageDb(pageDbIn)
    ensures validPageDb(smc_initL2PTable(pageDbIn, page, addrspacePage, l1index).0)
{
    reveal validPageDb();
    var (pageDbOut, errOut)
        := smc_initL2PTable(pageDbIn, page, addrspacePage, l1index);
    if( errOut != KOM_ERR_SUCCESS ) {
        // trivial
    } else {
        var l1ptnr := pageDbIn[addrspacePage].entry.l1ptnr;
        var l1pt := pageDbIn[l1ptnr].entry.l1pt;
        assert validL1PTable(pageDbIn, addrspacePage, l1pt);
        // no refs to the free page
        forall (i | 0 <= i < NR_L1PTES)
            ensures l1pt[i] != Just(page)
        {
            assert pageIsFree(pageDbIn, page);
            assert !stoppedAddrspace(pageDbIn[addrspacePage]);
            assert l1pt[i].Just? ==> validL1PTE(pageDbIn, fromJust(l1pt[i]));
        }
        assert forall i :: 0 <= i < NR_L1PTES
        ==> pageDbIn[l1ptnr].entry.l1pt[i] != Just(page);
        var l2pt := L2PTable(SeqRepeat(NR_L2PTES, NoMapping));
        var pageDbTmp := allocatePage(pageDbIn, page, addrspacePage, l2pt).0;
        var pageDbBogus := pageDbTmp[page := PageDbEntryTyped(addrspacePage, SparePage)];
        forall p:PageNr | pageDbBogus[p].PageDbEntryTyped?
            ensures validPageDbEntry(pageDbBogus, p)
        {
            if p == addrspacePage {
                assert validAddrspace(pageDbTmp, addrspacePage) by {
                    var oldRefs := addrspaceRefs(pageDbIn, addrspacePage);
                    assert addrspaceRefs(pageDbTmp, addrspacePage)
                        == oldRefs + {page};
                    var addrspace_ := pageDbIn[addrspacePage].entry;
                    var addrspace := pageDbTmp[addrspacePage].entry;
                    assert addrspace.refcount == |addrspaceRefs(pageDbTmp, addrspacePage)|;
                    assert validAddrspacePage(pageDbTmp, addrspacePage);

                    assert 1 + PAGESIZE / (WORDSIZE * SHA_BLOCKSIZE) == 65;
                    assert addrspace_.refcount * 65 <= addrspace.refcount * 65;
                }
                assert addrspaceRefs(pageDbTmp, addrspacePage)
                    == addrspaceRefs(pageDbBogus, addrspacePage);
                assert validAddrspace(pageDbBogus, p);
            } else {
                assert addrspaceRefs(pageDbBogus, p) == addrspaceRefs(pageDbIn, p);
            }
            if pageDbBogus[p].entry.DataPage? && !hasStoppedAddrspace(pageDbBogus, p) {
                var a := pageDbBogus[p].addrspace;
                assert dataPageRefs(pageDbBogus, a, p) == dataPageRefs(pageDbIn, a, p);
            }
        }
        lemma_installL1PTEPreservesPageDbValidity(pageDbTmp, addrspacePage,
                                                  l1ptnr, page, l1index);
    }
}

lemma removePreservesPageDBValidity(pageDbIn: PageDb, page: word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_remove(pageDbIn, page).0)
{
    reveal validPageDb();
    var result := smc_remove(pageDbIn, page);
    var pageDbOut := result.0;
    var errOut := result.1;

    if ( errOut != KOM_ERR_SUCCESS ){
       // trivial
    } else if( pageDbIn[page].PageDbEntryFree?) {
        // trivial
    } else {

        var entry := pageDbIn[page].entry;
        var addrspacePage := pageDbIn[page].addrspace;
        assert validAddrspace(pageDbIn, addrspacePage);

        assert validPageDbEntry(pageDbOut, addrspacePage) by {
            if !entry.Addrspace? {
                var addrspace := pageDbOut[addrspacePage].entry;

                var oldRefs := addrspaceRefs(pageDbIn, addrspacePage);
                assert addrspaceRefs(pageDbOut, addrspacePage) == oldRefs - {page};
                assert addrspace.refcount == |addrspaceRefs(pageDbOut, addrspacePage)|;
                //assert validAddrspace(pageDbOut, addrspace);
                assert validAddrspacePage(pageDbOut, addrspacePage);
            }
        }

        assert validPageDbEntry(pageDbOut, page);

        forall n:PageNr | pageDbOut[n].PageDbEntryTyped?
                        && n != addrspacePage && n != page
            ensures validPageDbEntry(pageDbOut, n)
        {
            var e := pageDbOut[n].entry;
            var d := pageDbOut;
            var a := pageDbOut[n].addrspace;
            assert pageDbOut[n] == pageDbIn[n];

            // This is a proof that the addrspace of n is still an addrspace
            //
            // The only interesting case is when the page that was
            // removed is the addrspace of n (i.e. a == page). This
            // case causes an error because a must have been valid in
            // pageDbIn and therefore n has a reference to it.
            assert d[a].PageDbEntryTyped? && d[a].entry.Addrspace?
            by {
                if a == page {
                    assert n in addrspaceRefs(pageDbIn, a);
                    assert pageDbIn[a].entry.refcount > 0;
                    assert false;
                }
            }

            if a == addrspacePage {
                var oldRefs := addrspaceRefs(pageDbIn, addrspacePage);
                assert addrspaceRefs(pageDbOut, addrspacePage) == oldRefs - {page};
                assert pageDbOut[a].entry.refcount == |addrspaceRefs(pageDbOut, addrspacePage)|;
            } else {
                assert pageDbOut[a].entry.refcount == pageDbIn[a].entry.refcount;
                assert addrspaceRefs(pageDbIn, a) == addrspaceRefs(pageDbOut, a);
            }

            if e.Addrspace? {
                assert addrspaceRefs(pageDbIn, n) == addrspaceRefs(pageDbOut, n);
            }

            if pageDbOut[n].entry.DataPage? && !hasStoppedAddrspace(pageDbOut, n) {
                assert dataPageRefs(pageDbOut, pageDbOut[n].addrspace, n)
                    == dataPageRefs(pageDbIn, pageDbIn[n].addrspace, n);
                assert validPageDbEntryTyped(d, n);
            }
        }

        assert pageDbEntriesValid(pageDbOut);
        assert validPageDb(pageDbOut);
    }
}

lemma mapSecurePreservesPageDBValidity(pageDbIn: PageDb, page: word,
    addrspacePage: word, map_word: word, physPage: word, contents: Maybe<seq<word>>)
    requires validPageDb(pageDbIn)
    requires physPage == 0 || physPageIsInsecureRam(physPage) ==> contents.Just?
    requires contents.Just? ==> |fromJust(contents)| == PAGESIZE / WORDSIZE
    ensures  validPageDb(smc_mapSecure(pageDbIn, page, addrspacePage,
        map_word, physPage, contents).0)
{
    reveal validPageDb();
    var mapping := wordToMapping(map_word);
    var pageDbOut := smc_mapSecure(
        pageDbIn, page, addrspacePage, map_word, physPage, contents).0;
    var err := smc_mapSecure(
        pageDbIn, page, addrspacePage, map_word, physPage, contents).1;

    if( err == KOM_ERR_SUCCESS ){
        BoundedShaLength(pageDbIn, addrspacePage);
        GrowShaLength(pageDbIn, addrspacePage, [KOM_SMC_MAP_SECURE, map_word], contents.v);

        assert validAndEmptyMapping(mapping, pageDbIn, addrspacePage)
            by { reveal wordToMapping(); }

        var pageDbA := allocatePage(pageDbIn, page,
            addrspacePage, DataPage(contents.v)).0;
        allocatePagePreservesPageDBValidity(pageDbIn, page, addrspacePage,
                                            DataPage(contents.v));
        lemma_freePageRefs(pageDbIn, page);
        assert dataPageRefs(pageDbA, addrspacePage, page) == {};
        var l2pte := SecureMapping(page, mapping.perm.w, mapping.perm.x);
        var pageDbB := updateL2Pte(pageDbA, addrspacePage, mapping, l2pte);
        lemma_updateL2PtePreservesPageDb(pageDbA, addrspacePage, mapping, l2pte);

        assert validPageDb(pageDbB);
        assert pageDbOut == updateMeasurement(pageDbB, addrspacePage,
                               [KOM_SMC_MAP_SECURE, map_word], fromJust(contents));

        assert validAddrspace(pageDbOut, addrspacePage) by {
            assert addrspaceRefs(pageDbOut, addrspacePage)
                == addrspaceRefs(pageDbB, addrspacePage);
        }

        forall ( n:PageNr | pageDbOut[n].PageDbEntryTyped? && n != addrspacePage)
            ensures validPageDbEntry(pageDbOut, n)
        {
            if( pageDbOut[n].entry.Addrspace? ){
                assert pageDbOut[n].entry.refcount == pageDbB[n].entry.refcount;
                assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbB, n);
            } else if pageDbOut[n].entry.DataPage? {
                if !hasStoppedAddrspace(pageDbOut, n) {
                    assert dataPageRefs(pageDbOut, pageDbOut[n].addrspace, n)
                        == dataPageRefs(pageDbB, pageDbB[n].addrspace, n);
                }
            }
        }
    }
}

lemma allocSparePreservesPageDBValidity(pageDbIn:PageDb, page:word, addrspacePage:word)
    requires validPageDb(pageDbIn)
    ensures validPageDb(smc_allocSpare(pageDbIn, page, addrspacePage).0)
{
    if smc_allocSpare(pageDbIn, page, addrspacePage).1 == KOM_ERR_SUCCESS {
        allocatePagePreservesPageDBValidity(pageDbIn, page, addrspacePage, SparePage);
    }
}

lemma mapInsecurePreservesPageDbValidity(pageDbIn: PageDb, addrspacePage: word,
    physPage: word, map_word: word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_mapInsecure(pageDbIn, addrspacePage, physPage, 
        map_word).0)
{
    reveal validPageDb();
    var mapping := wordToMapping(map_word);
    var pageDbOut := smc_mapInsecure(
        pageDbIn, addrspacePage, physPage, map_word).0;
    var err := smc_mapInsecure(
        pageDbIn, addrspacePage, physPage, map_word).1;

    if( err != KOM_ERR_SUCCESS ){
    } else {
        var addrspace := pageDbIn[addrspacePage].entry;
        var l1 := pageDbIn[addrspace.l1ptnr].entry;
        var l1pte := fromJust(l1.l1pt[mapping.l1index]);
        var l2pt := pageDbOut[l1pte].entry.l2pt;

        assert validAndEmptyMapping(mapping, pageDbIn, addrspacePage)
            by { reveal wordToMapping(); }

        forall n:PageNr | pageDbOut[n].PageDbEntryTyped?
            ensures validPageDbEntryTyped(pageDbOut, n);
        {
            if( pageDbOut[n].entry.Addrspace? ){
                assert pageDbOut[n].entry.refcount == pageDbIn[n].entry.refcount;
                assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
                assert validPageDbEntryTyped(pageDbOut, n);
            } else if (pageDbOut[n].entry.L2PTable?) {
                if pageDbOut[n].addrspace == addrspacePage {
                    assert addrspace.state.StoppedState?
                        || validL2PTable(pageDbIn, addrspacePage, pageDbIn[n].entry.l2pt);
                    if (n == l1pte) {
                        forall i | 0 <= i < |l2pt|
                            ensures validL2PTE(pageDbOut, addrspacePage, l2pt[i])
                        {
                            if (i == mapping.l2index) {
                                assert validL2PTE(pageDbOut, addrspacePage, l2pt[i]);
                            } else {
                                assert validL2PTE(pageDbIn, addrspacePage, l2pt[i]);
                                assert l2pt[i] == pageDbIn[n].entry.l2pt[i];
                                assert validL2PTE(pageDbOut, addrspacePage, l2pt[i]);
                            }
                        }
                        assert validL2PTable(pageDbOut, addrspacePage, l2pt);
                    }
                }
                assert validPageDbEntryTyped(pageDbOut, n);
            } else if pageDbOut[n].entry.DataPage? {
                if !hasStoppedAddrspace(pageDbOut, n) {
                    if pageDbIn[n].addrspace == addrspacePage {
                        assert forall i | 0 <= i < NR_L2PTES :: if i == mapping.l2index
                            then l2pt[i].InsecureMapping?
                            else l2pt[i] == pageDbIn[l1pte].entry.l2pt[i];
                    }
                    assert dataPageRefs(pageDbIn, pageDbIn[n].addrspace, n)
                        == dataPageRefs(pageDbOut, pageDbOut[n].addrspace, n);
                }
            }
        }
    }
}

lemma finalisePreservesPageDbValidity(pageDbIn: PageDb, addrspacePage: word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_finalise(pageDbIn, addrspacePage).0)
{
    reveal validPageDb();
    var pageDbOut := smc_finalise(pageDbIn, addrspacePage).0;
    var err := smc_finalise(pageDbIn, addrspacePage).1;

    if( err != KOM_ERR_SUCCESS ){
    } else {
        var a := addrspacePage;
        assert pageDbOut[a].entry.refcount == pageDbIn[a].entry.refcount;
        assert addrspaceRefs(pageDbOut, a) == addrspaceRefs(pageDbIn, a);

        forall ( n | validPageNr(n) 
            && pageDbOut[n].PageDbEntryTyped?
            && n != a )
            ensures validPageDbEntry(pageDbOut, n)
        {
            if( pageDbOut[n].entry.Addrspace? ){
                assert pageDbOut[n].entry.refcount == pageDbIn[n].entry.refcount;
                assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
            } else if pageDbOut[n].entry.DataPage? {
                if !hasStoppedAddrspace(pageDbOut, n) {
                    assert dataPageRefs(pageDbOut, pageDbOut[n].addrspace, n)
                        == dataPageRefs(pageDbIn, pageDbIn[n].addrspace, n);
                }
            }
        }
    }
}

lemma lemma_userspaceExecutionAndException_spsr(s:state, r:state)
    requires ValidState(s) && userspaceExecutionAndException(s, r)
    requires mode_of_state(s) != User && !spsr_of_state(s).f && !spsr_of_state(s).i
    ensures mode_of_state(r) != User && spsr_of_state(r).m == User
    ensures !spsr_of_state(r).f && !spsr_of_state(r).i
{
    assert ValidOperand(OLR);
    reveal userspaceExecutionAndException();
    assert ExtractAbsPageTable(s).Just?;
    var s', s2 :| equivStates(s, s')
        && evalEnterUserspace(s', s2)
        && (lemma_evalEnterUserspace_preservesAbsPageTable(s', s2);
           var (s3, expc, ex) := userspaceExecutionFn(s2, OperandContents(s, OLR));
            evalExceptionTaken(s3, ex, expc, r));
    var (s3, expc, ex) := userspaceExecutionFn(s2, OperandContents(s, OLR));
    assert mode_of_state(s3) == User by { reveal userspaceExecutionFn(); }
    lemma_evalExceptionTaken_Mode(s3, ex, expc, r);
    calc {
        !spsr_of_state(s).f && !spsr_of_state(s).i;
        !spsr_of_state(s').f && !spsr_of_state(s').i;
        !s2.conf.cpsr.f && !s2.conf.cpsr.i;
        { reveal userspaceExecutionFn(); }
        !s3.conf.cpsr.f && !s3.conf.cpsr.i;
        !spsr_of_state(r).f && !spsr_of_state(r).i;
    }
}

lemma lemma_validEnclaveExecutionStep_validPageDb(s1:state, d1:PageDb,
    rs:state, rd:PageDb, dispPg:PageNr, retToEnclave:bool)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires finalDispatcher(d1, dispPg)
    requires validEnclaveExecutionStep(s1, d1, rs, rd, dispPg, retToEnclave)
    requires mode_of_state(s1) != User
    requires !spsr_of_state(s1).f && !spsr_of_state(s1).i
    ensures validPageDb(rd)
    ensures finalDispatcher(rd, dispPg)
{
    reveal validEnclaveExecutionStep();
    reveal updateUserPagesFromState();

    if !retToEnclave {
        var s4, d4 :| userspaceExecutionAndException(s1, s4)
            && d4 == updateUserPagesFromState(s4, d1, dispPg)
            && rd == exceptionHandled(s4, d4, dispPg).2;
        lemma_userspaceExecutionAndException_spsr(s1, s4);
        lemma_exceptionHandled_validPageDb(s4, d4, dispPg);
        assert finalDispatcher(rd, dispPg);
    }
}

lemma lemma_validEnclaveExecution(s1:state, d1:PageDb,
    rs:state, rd:PageDb, dispPg:PageNr, steps:nat)
    requires ValidState(s1) && validPageDb(d1) && SaneConstants()
    requires finalDispatcher(d1, dispPg)
    requires validEnclaveExecution(s1, d1, rs, rd, dispPg, steps)
    requires mode_of_state(s1) != User
    requires !spsr_of_state(s1).f && !spsr_of_state(s1).i
    ensures validPageDb(rd)
    decreases steps
{
    reveal validEnclaveExecution();
    var retToEnclave := (steps > 0);
    var s5, d5 :|
        validEnclaveExecutionStep(s1, d1, s5, d5, dispPg, retToEnclave)
        && if retToEnclave then
        (lemma_validEnclaveExecutionStep_validPageDb(s1, d1, s5, d5, dispPg, retToEnclave);
        validEnclaveExecution(s5, d5, rs, rd, dispPg, steps - 1))
        else rd == d5;

    if retToEnclave {
        lemma_validEnclaveExecution(s5, d5, rs, rd, dispPg, steps - 1);
    }
}

lemma enterPreservesPageDbValidity(s:state, pageDbIn: PageDb, s':state,
    pageDbOut: PageDb, dispPage: word, arg1: word, arg2: word, arg3: word)
    requires ValidState(s) && validPageDb(pageDbIn) && ValidState(s')
    requires SaneConstants()
    requires smc_enter(s, pageDbIn, s', pageDbOut, dispPage, arg1, arg2, arg3)
    ensures validPageDb(pageDbOut)
{
    if (smc_enter_err(pageDbIn, dispPage, false) == KOM_ERR_SUCCESS) {
        var s1, steps:nat :|
            preEntryEnter(s, s1, pageDbIn, dispPage, arg1, arg2, arg3)
            && validEnclaveExecution(s1, pageDbIn, s', pageDbOut, dispPage, steps);
        lemma_validEnclaveExecution(s1, pageDbIn, s', pageDbOut, dispPage, steps);
    }
}

lemma resumePreservesPageDbValidity(s:state, pageDbIn: PageDb, s':state,
                                    pageDbOut: PageDb, dispPage: word)
    requires ValidState(s) && validPageDb(pageDbIn) && ValidState(s')
    requires SaneConstants()
    requires smc_resume(s, pageDbIn, s', pageDbOut, dispPage)
    ensures validPageDb(pageDbOut)
{
    if (smc_enter_err(pageDbIn, dispPage, true) == KOM_ERR_SUCCESS) {
        var s1, steps:nat :|
            preEntryResume(s, s1, pageDbIn, dispPage)
            && validEnclaveExecution(s1, pageDbIn, s', pageDbOut, dispPage, steps);
        lemma_validEnclaveExecution(s1, pageDbIn, s', pageDbOut, dispPage, steps);
    }
}

lemma stopPreservesPageDbValidity(pageDbIn: PageDb, addrspacePage: word)
    requires validPageDb(pageDbIn)
    ensures  validPageDb(smc_stop(pageDbIn, addrspacePage).0)
{
    reveal validPageDb();
    var pageDbOut := smc_stop(pageDbIn, addrspacePage).0;
    var err := smc_stop(pageDbIn, addrspacePage).1;

    if( err != KOM_ERR_SUCCESS ){
    } else {
        var a := addrspacePage;
        assert pageDbOut[a].entry.refcount == pageDbIn[a].entry.refcount;
        assert addrspaceRefs(pageDbOut, a) == addrspaceRefs(pageDbIn, a);

        forall ( n | validPageNr(n) 
            && pageDbOut[n].PageDbEntryTyped?
            && n != a )
            ensures validPageDbEntry(pageDbOut, n)
        {
            if( pageDbOut[n].entry.Addrspace? ){
                assert pageDbOut[n].entry.refcount == pageDbIn[n].entry.refcount;
                assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n);
            } else if pageDbOut[n].entry.DataPage? {
                if !hasStoppedAddrspace(pageDbOut, n) {
                    assert dataPageRefs(pageDbOut, pageDbOut[n].addrspace, n)
                        == dataPageRefs(pageDbIn, pageDbIn[n].addrspace, n);
                }
            }

        }

    }
}

lemma lemma_allocatePage_preservesMappingGoodness(
    pageDbIn:PageDb,securePage:word,
    addrspacePage:PageNr,entry:PageDbEntryTyped,pageDbOut:PageDb,err:word,
    abs_mapping:word)
    requires validPageDb(pageDbIn)
    requires validAddrspacePage(pageDbIn, addrspacePage)
    requires allocatePageEntryValid(entry)
    requires !entry.L2PTable?
    requires (pageDbOut, err) == allocatePage(pageDbIn,securePage,
        addrspacePage,entry)
    requires isValidMappingTarget(pageDbIn,addrspacePage,abs_mapping) ==
        KOM_ERR_SUCCESS;
    ensures validPageDb(pageDbOut)
    ensures isValidMappingTarget(pageDbOut,addrspacePage,abs_mapping) ==
        KOM_ERR_SUCCESS;
{
    allocatePagePreservesPageDBValidity(pageDbIn, securePage,
                                        addrspacePage, entry);
    reveal validPageDb();
}


lemma smchandlerPreservesPageDbValidity(s: state, pageDbIn: PageDb, s':state,
    pageDbOut: PageDb)
    requires ValidState(s) && validPageDb(pageDbIn) && SaneConstants()
    requires smchandler(s, pageDbIn, s', pageDbOut)
    ensures validPageDb(pageDbOut)
{
    reveal ValidRegState();
    var callno, arg1, arg2, arg3, arg4
        := s.regs[R0], s.regs[R1], s.regs[R2], s.regs[R3], s.regs[R4];
    var err, val := s'.regs[R0], s'.regs[R1];

    if (callno == KOM_SMC_INIT_ADDRSPACE) {
        initAddrspacePreservesPageDBValidity(pageDbIn, arg1, arg2);
    } else if(callno == KOM_SMC_INIT_DISPATCHER) {
        initDispatcherPreservesPageDBValidity(pageDbIn, arg1, arg2, arg3);
    } else if(callno == KOM_SMC_INIT_L2PTABLE) {
        initL2PTablePreservesPageDBValidity(pageDbIn, arg1, arg2, arg3);
    } else if(callno == KOM_SMC_MAP_SECURE) {
        var pg := maybeContentsOfPhysPage(s, arg4);
        mapSecurePreservesPageDBValidity(pageDbIn, arg1, arg2, arg3, arg4, pg);
    } else if(callno == KOM_SMC_ALLOC_SPARE) {
        allocSparePreservesPageDBValidity(pageDbIn, arg1, arg2);
    } else if(callno == KOM_SMC_MAP_INSECURE) {
        mapInsecurePreservesPageDbValidity(pageDbIn, arg1, arg2, arg3);
    } else if(callno == KOM_SMC_REMOVE) {
        removePreservesPageDBValidity(pageDbIn, arg1);
    } else if(callno == KOM_SMC_FINALISE) {
        finalisePreservesPageDbValidity(pageDbIn, arg1);
    } else if(callno == KOM_SMC_ENTER) {
        enterPreservesPageDbValidity(s, pageDbIn, s', pageDbOut, arg1, arg2, arg3, arg4);
    } else if(callno == KOM_SMC_RESUME) {
        resumePreservesPageDbValidity(s, pageDbIn, s', pageDbOut, arg1);
    } else if(callno == KOM_SMC_STOP) {
        stopPreservesPageDbValidity(pageDbIn, arg1);
    }
}

lemma kom_smc_map_measure_helper1(s:state, as_page:PageNr, metadata:seq<word>, contents:seq<word>, pagedb_in:PageDb)
    returns (base:addr, ctx:addr, input:seq<word>, trace_in:SHA256Trace, e:PageDbEntryTyped, pagedb:PageDb)
    requires SaneState(s)
    requires wellFormedPageDb(pagedb_in)
    requires validAddrspacePage(pagedb_in, as_page)
    requires validPageDb(pagedb_in)
    requires pageDbCorresponds(s.m, pagedb_in)
    requires pagedb_in[as_page].entry.state == InitState
    requires |metadata| == 2
    requires |contents| % SHA_BLOCKSIZE == 0
    ensures input == metadata + [0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0]
    ensures pagedb == updateMeasurement(pagedb_in, as_page, metadata, contents)
    ensures base == page_monvaddr(as_page)
    ensures ctx == base + ADDRSPACE_HASH
    ensures base + ADDRSPACE_HASHED_BLOCK_COUNT in s.m.addresses
    ensures s.m.addresses[base + ADDRSPACE_HASHED_BLOCK_COUNT] + 65 < 0x1_0000_0000
    ensures IsCompleteSHA256Trace(trace_in)
    ensures SHA256TraceIsCorrect(trace_in)
    ensures
        forall i :: 0 <= i < 8 ==>
            ctx + i*WORDSIZE in s.m.addresses && last(trace_in.H)[i] == s.m.addresses[ctx + i*WORDSIZE]
    ensures as_page in pagedb_in
    ensures pagedb_in[as_page].PageDbEntryTyped?
    ensures e == pagedb_in[as_page].entry
    ensures e.Addrspace?
    ensures ConcatenateSeqs(trace_in.M) == e.measurement
    ensures trace_in == e.shatrace
    ensures WordsToBytes(SeqLength(e.measurement) + 16) + PAGESIZE < MaxBytesForSHA();
{
    input := metadata + [0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0];
    var p := as_page;
    var pe := pagedb_in[p];
    var spe := extractPage(s.m, p);
    assert pageContentsCorresponds(p, pe, spe);
    e := pe.entry;
    assert e.Addrspace?;
    assert pageDbAddrspaceCorresponds(p, e, spe) by { reveal pageContentsCorresponds(); }
    assert validAddrspace(pagedb_in, p) by { reveal validPageDb(); }

    BoundedShaLength(pagedb_in, as_page);

    trace_in := e.shatrace;
    base := page_monvaddr(p);
    ctx := base + ADDRSPACE_HASH;

    assert forall i :: 0 <= i < 8 ==>
            ctx + i*WORDSIZE in s.m.addresses && last(trace_in.H)[i] == s.m.addresses[ctx + i*WORDSIZE]
        by { reveal pageDbAddrspaceCorresponds(); }

    assert base + ADDRSPACE_HASHED_BLOCK_COUNT in s.m.addresses
        && s.m.addresses[base + ADDRSPACE_HASHED_BLOCK_COUNT] + 65 < 0x1_0000_0000
        by { reveal pageDbAddrspaceCorresponds(); }

    pagedb := updateMeasurement(pagedb_in, as_page, metadata, contents);
}

function{:opaque} ConcatSha(m:seq<seq<word>>):seq<word>
{
    if |m| == 0 then [] else m[0] + ConcatSha(m[1..])
}

lemma lemma_ConcatSha_ConcatenateSeqs(m:seq<seq<word>>)
    ensures ConcatSha(m) == ConcatenateSeqs(m)
{
    reveal ConcatSha();
    if (|m| > 0)
    {
        lemma_ConcatSha_ConcatenateSeqs(m[1..]);
    }
}

lemma lemma_ConcatSha_Adds(s:seq<seq<word>>, s':seq<seq<word>>)
    ensures ConcatSha(s + s') == ConcatSha(s) + ConcatSha(s'); 
{
    lemma_ConcatSha_ConcatenateSeqs(s);
    lemma_ConcatSha_ConcatenateSeqs(s');
    lemma_ConcatSha_ConcatenateSeqs(s + s');
    lemma_ConcatenateSeqs_Adds'(s, s');
}

lemma lemma_sha256_concat(m:seq<seq<word>>, input:seq<word>)
    requires |input| == |m| * SHA_BLOCKSIZE
    requires
        (forall i :: 0 <= i < |m| ==>
            m[i] == SeqSlice(input, i * SHA_BLOCKSIZE, (i + 1) * SHA_BLOCKSIZE))
    ensures ConcatSha(m) == input
{
    assert ConcatSha([]) == [] by { reveal ConcatSha(); }
    if (|m| != 0)
    {
        var m' := m[1..];
        var input' := input[SHA_BLOCKSIZE..];
        lemma_sha256_concat(m', input');
        assert m == [m[0]] + m';
        assert ConcatSha([m[0]]) == m[0] by { reveal ConcatSha(); }
        calc
        {
            ConcatSha(m);
            ConcatSha([m[0]] + m');            { lemma_ConcatSha_Adds([m[0]], m'); }
            ConcatSha([m[0]]) + ConcatSha(m');
            m[0] + input';
            input;
        }
    }
}

lemma lemma_sha256_suffix(m1:seq<seq<word>>, m2:seq<seq<word>>, input:seq<word>)
    requires |input| == (|m2| - |m1|) * SHA_BLOCKSIZE
    requires m1 == SeqSlice(m2, 0, |m1|)
    requires
        (forall i {:trigger m2[|m1| + i]}{:trigger m2[|m1|..][i]} :: 0 <= i < |m2| - |m1| ==>
            m2[|m1| + i] == SeqSlice(input, i * SHA_BLOCKSIZE, (i + 1) * SHA_BLOCKSIZE))
    ensures ConcatenateSeqs(m2) == ConcatenateSeqs(m1) + input
{
    var suffix := m2[|m1|..];
    lemma_sha256_concat(suffix, input);
    calc
    {
        ConcatSha(m2);                     { assert m2 == m1 + suffix; }
        ConcatSha(m1 + suffix);            { lemma_ConcatSha_Adds(m1, suffix); }
        ConcatSha(m1) + ConcatSha(suffix);
        ConcatSha(m1) + input;
    }
    lemma_ConcatSha_ConcatenateSeqs(m1);
    lemma_ConcatSha_ConcatenateSeqs(m2);
}

lemma kom_smc_map_measure_helper2(pagedb_in:PageDb, pagedb:PageDb, e:PageDbEntryTyped,
    measurement:seq<word>, as_page:PageNr, metadata:seq<word>, input:seq<word>, contents:seq<word>,
    trace1:SHA256Trace, trace2:SHA256Trace, trace3:SHA256Trace)
    requires wellFormedPageDb(pagedb_in)
    requires validAddrspacePage(pagedb_in, as_page)
    requires validPageDb(pagedb_in)
    requires pagedb_in[as_page].entry.state.InitState?
    requires |measurement| % SHA_BLOCKSIZE == 0
    requires ConcatenateSeqs(trace1.M) == measurement;
    requires IsCompleteSHA256Trace(trace2)
    requires SHA256TraceIsCorrect(trace2)
    requires IsCompleteSHA256Trace(trace3)
    requires SHA256TraceIsCorrect(trace3)
    requires SeqLength(trace2.M) - SeqLength(trace1.M) == 1
    requires (SeqLength(trace3.M) - SeqLength(trace2.M)) * SHA_BLOCKSIZE == |contents|
    requires trace1.M == SeqSlice(trace2.M, 0, |trace1.M|)
    requires trace2.M == SeqSlice(trace3.M, 0, |trace2.M|)
    requires |metadata| == 2
    requires |contents| % SHA_BLOCKSIZE == 0
    requires input == metadata + [0, 0,  0, 0, 0, 0,  0, 0, 0, 0,  0, 0, 0, 0]
    requires trace2.M[|trace1.M|] == SeqSlice(input, 0, SHA_BLOCKSIZE)
    requires forall i :: 0 <= i < |trace3.M| - |trace2.M| ==>
        trace3.M[|trace2.M| + i] == SeqSlice(contents, i * SHA_BLOCKSIZE, (i + 1) * SHA_BLOCKSIZE)
    requires pagedb == updateMeasurement(pagedb_in, as_page, metadata, contents)
    requires as_page in pagedb_in
    requires pagedb_in[as_page].PageDbEntryTyped?
    requires e == pagedb_in[as_page].entry
    requires e.Addrspace?
    requires measurement == e.measurement
    ensures trace3 == newShaTraceForMeasurement(measurement + input + contents)
    ensures pagedb[as_page].entry.shatrace == trace3
{
    var padded_metadata := metadata + SeqRepeat(SHA_BLOCKSIZE - SeqLength(metadata), 0);
    var newmeasurement := measurement + padded_metadata + contents;
    assert newmeasurement == measurement + input + contents;
    var trace_new := newShaTraceForMeasurement(newmeasurement);

    assert SeqSlice(input, 0, SHA_BLOCKSIZE) == input;

    lemma_sha256_suffix(trace1.M, trace2.M, input);
    lemma_sha256_suffix(trace2.M, trace3.M, contents);
    lemma_SHATracesAreEqual(trace3, trace_new);
}
