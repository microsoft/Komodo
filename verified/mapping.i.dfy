include "mapping.s.dfy"

lemma lemma_installL1PTEInPageDb_dataPageRefs(d1:PageDb, d2:PageDb, asPg: PageNr, l1ptnr: PageNr, l2page: PageNr, l1index: int, n:PageNr)
    requires validPageDb(d1[l2page := PageDbEntryTyped(asPg, SparePage)])
    requires wellFormedPageDb(d2)
    requires isAddrspace(d1, asPg) && !stoppedAddrspace(d1[asPg])
    requires l1ptnr == d1[asPg].entry.l1ptnr
    requires d1[l1ptnr].PageDbEntryTyped? && d1[l1ptnr].entry.L1PTable?
    requires 0 <= l1index < NR_L1PTES
    requires d1[l1ptnr].entry.l1pt[l1index].Nothing?
    requires validL1PTE(d1, l2page) && d1[l2page].addrspace == d1[l1ptnr].addrspace
    requires forall e | e in d1[l2page].entry.l2pt :: e.NoMapping?
    requires d2 == installL1PTEInPageDb(d1, l1ptnr, l2page, l1index)
    requires n != l1ptnr && n != l2page && l2page != l1ptnr
    requires d1[n].PageDbEntryTyped? && d1[n].entry.DataPage?
    requires !hasStoppedAddrspace(d1, n)
    ensures isAddrspace(d1, d1[n].addrspace)
    ensures dataPageRefs(d1, d1[n].addrspace, n) == dataPageRefs(d2, d2[n].addrspace, n)
{
    reveal validPageDb();
    assert validPageDbEntryTyped(d1[l2page := PageDbEntryTyped(asPg, SparePage)], n);
    assert d2[n] == d1[n];
    if d1[n].addrspace == asPg {
        calc {
            dataPageRefs(d1, d1[n].addrspace, n);
            { assert d1[l1ptnr].PageDbEntryTyped? && d1[l1ptnr].entry.L1PTable?; }
            (set i1, i2 {:trigger d1[d1[l1ptnr].entry.l1pt[i1].v].entry.l2pt[i2]} |
                0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := d1[l1ptnr].entry.l1pt[i1]; l1e.Just?
                && d1[l1e.v].PageDbEntryTyped? && d1[l1e.v].entry.L2PTable?
                && var l2e := d1[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2));
            { assert forall n:PageNr | n != l1ptnr :: d1[n] == d2[n]; }
            (set i1, i2 {:trigger d2[d1[l1ptnr].entry.l1pt[i1].v].entry.l2pt[i2]} |
                0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := d1[l1ptnr].entry.l1pt[i1]; l1e.Just?
                && d2[l1e.v].PageDbEntryTyped? && d2[l1e.v].entry.L2PTable?
                && var l2e := d2[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2));
            {
                var l1pt := d1[l1ptnr].entry.l1pt;
                assert d2[l1ptnr].entry.l1pt == l1pt[l1index := Just(l2page)];
                assert l1pt[l1index].Nothing?;
                assert forall i1 | 0 <= i1 < NR_L1PTES && d2[l1ptnr].entry.l1pt[i1].Just?
                    :: d2[l1ptnr].entry.l1pt[i1].v == l2page || d2[l1ptnr].entry.l1pt[i1] == l1pt[i1];
                assert forall i2 | 0 <= i2 < NR_L2PTES :: d2[l2page].entry.l2pt[i2].NoMapping?;
            }
            (set i1, i2 {:trigger d2[d1[l1ptnr].entry.l1pt[i1].v].entry.l2pt[i2]} |
                && 0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := d2[l1ptnr].entry.l1pt[i1]; l1e.Just?
                && d2[l1e.v].PageDbEntryTyped? && d2[l1e.v].entry.L2PTable?
                && var l2e := d2[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2));
            dataPageRefs(d2, d2[n].addrspace, n);
        }
    } else { // different AS
        var a := d1[n].addrspace;
        var l1 := d1[a].entry.l1ptnr;
        calc {
            dataPageRefs(d1, a, n);
            (set i1, i2 {:trigger d1[d1[l1].entry.l1pt[i1].v].entry.l2pt[i2]} |
                d1[l1].PageDbEntryTyped? && d1[l1].entry.L1PTable?
                && 0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := d1[l1].entry.l1pt[i1]; l1e.Just?
                && d1[l1e.v].PageDbEntryTyped? && d1[l1e.v].entry.L2PTable?
                && var l2e := d1[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2));
            { assert l1 != l1ptnr; assert d1[a] == d2[a] && d1[l1] == d2[l1]; }
            (set i1, i2 {:trigger d1[d2[l1].entry.l1pt[i1].v].entry.l2pt[i2]} |
                d1[l1].PageDbEntryTyped? && d1[l1].entry.L1PTable?
                && 0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := d2[l1].entry.l1pt[i1]; l1e.Just?
                && d1[l1e.v].PageDbEntryTyped? && d1[l1e.v].entry.L2PTable?
                && var l2e := d1[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2));
            dataPageRefs(d2, a, n);
        }
    }
}

lemma lemma_installL1PTEPreservesPageDbValidity(pageDbIn: PageDb, asPg: PageNr,
                                        l1ptnr: PageNr, l2page: PageNr, l1index: int)
    requires validPageDb(pageDbIn[l2page := PageDbEntryTyped(asPg, SparePage)])
    requires isAddrspace(pageDbIn, asPg) && !stoppedAddrspace(pageDbIn[asPg])
    requires l1ptnr == pageDbIn[asPg].entry.l1ptnr
    requires pageDbIn[l1ptnr].PageDbEntryTyped? && pageDbIn[l1ptnr].entry.L1PTable?
    // l2pt belongs to this addrspace, and is empty
    requires validL1PTE(pageDbIn, l2page)
            && pageDbIn[l2page].addrspace == pageDbIn[l1ptnr].addrspace
    requires forall e | e in pageDbIn[l2page].entry.l2pt :: e.NoMapping?
    // no double mapping
    requires 0 <= l1index < NR_L1PTES
    requires forall i :: 0 <= i < NR_L1PTES && i != l1index
        ==> pageDbIn[l1ptnr].entry.l1pt[i] != Just(l2page)
    requires pageDbIn[l1ptnr].entry.l1pt[l1index].Nothing?
    ensures validPageDb(installL1PTEInPageDb(pageDbIn, l1ptnr, l2page, l1index))
{
    reveal validPageDb();

    var tmpDb := pageDbIn[l2page := PageDbEntryTyped(asPg, SparePage)];
    
    assert validL1PTable(pageDbIn, asPg, pageDbIn[l1ptnr].entry.l1pt);
    var pageDbOut := installL1PTEInPageDb(pageDbIn, l1ptnr, l2page, l1index);
    assert validL1PTable(pageDbOut, asPg, pageDbOut[l1ptnr].entry.l1pt);

    forall (n:PageNr | pageDbIn[n].PageDbEntryTyped? && n != l1ptnr && n != l2page)
        ensures validPageDbEntryTyped(pageDbOut, n)
    {
        assert pageDbOut[n] == pageDbIn[n];
        var a := pageDbIn[n].addrspace;
        assert pageDbIn[a] == pageDbOut[a];
        assert validPageDbEntryTyped(tmpDb, n);
        assert addrspaceRefs(pageDbOut, n) == addrspaceRefs(pageDbIn, n) == addrspaceRefs(tmpDb, n);
        if pageDbIn[n].entry.DataPage? {
            if !hasStoppedAddrspace(pageDbIn, n) {
                calc {
                    dataPageRefs(tmpDb, a, n);
                    dataPageRefs(pageDbIn, a, n);
                    { lemma_installL1PTEInPageDb_dataPageRefs(pageDbIn, pageDbOut,
                                        asPg, l1ptnr, l2page, l1index, n); }
                    dataPageRefs(pageDbOut, a, n);
                }
            }
            assert validPageDbEntry(pageDbOut, n);
        } else if pageDbIn[n].entry.L2PTable? {
            if !hasStoppedAddrspace(pageDbIn, n) {
                calc {
                    true;
                    referencedL2PTable(tmpDb, a, n);
                    referencedL2PTable(pageDbIn, a, n);
                    {
                        var l1ptnr' := pageDbIn[a].entry.l1ptnr;
                        assert l1ptnr' != l2page;
                        var l1pt' := pageDbIn[l1ptnr'].entry.l1pt;
                        var i :| 0 <= i < NR_L1PTES && l1pt'[i] == Just(n);
                        if l1ptnr' == l1ptnr {
                            assert l1index != i;
                            assert pageDbOut[l1ptnr].entry.l1pt[i] == l1pt'[i];
                        } else {
                            assert pageDbOut[l1ptnr'] == pageDbIn[l1ptnr'];
                        }
                    }
                    referencedL2PTable(pageDbOut, a, n);
                }
            }
            assert validPageDbEntry(pageDbOut, n);
        } else if pageDbIn[n].entry.Addrspace? {
            assert a == n;
            assert validAddrspace(tmpDb, n);
            if a == asPg {
                assert validAddrspace(pageDbOut, n);
            } else {
                assert validAddrspace(pageDbOut, n);
            }
        }
    }

    assert validPageDbEntry(pageDbOut, l2page)
    by {
        assert pageDbOut[l1ptnr].entry.l1pt[l1index] == Just(l2page);
        assert referencedL2PTable(pageDbOut, asPg, l2page);
    }
}

predicate validAndEmptyMapping(m:Mapping, d:PageDb, a:PageNr)
{
    validMapping(m, d, a)
    && var addrspace := d[a].entry;
    var l1pt := d[addrspace.l1ptnr].entry.l1pt;
    validL1PTable(d, a, l1pt)
    && var l2pt := d[l1pt[m.l1index].v].entry.l2pt;
    l2pt[m.l2index].NoMapping?
}

lemma {:fuel referencedL2PTable, 0} lemma_updateL2Pte_dataPageRefs(d1:PageDb, d2:PageDb, a:PageNr, mapping:Mapping, l2e:L2PTE, n:PageNr)
    requires validPageDb(d1) && wellFormedPageDb(d2)
    requires validMapping(mapping, d1, a) && validL2PTE(d1, a, l2e)
    requires l2e.SecureMapping? ==>
        validAndEmptyMapping(mapping, d1, a) && dataPageRefs(d1, a, l2e.page) == {}
    requires d2 == (reveal validPageDb(); updateL2Pte(d1, a, mapping, l2e))
    requires d1[n].PageDbEntryTyped? && d1[n].entry.DataPage? && d1[n].addrspace == a
    ensures |dataPageRefs(d2, a, n)| <= 1
{
    reveal validPageDb();
    assert validPageDbEntryTyped(d1, n);
    assert d2[n] == d1[n];

    var l1ptnr := d1[a].entry.l1ptnr;
    var l1pt := d1[l1ptnr].entry.l1pt;
    var l2ptnr := l1pt[mapping.l1index].v;
    var l2pt := d1[l2ptnr].entry.l2pt;
    assert l2e.SecureMapping? ==> l2pt[mapping.l2index].NoMapping?;
    var l2pt' := d2[l2ptnr].entry.l2pt;
    assert l2pt' == l2pt[mapping.l2index := l2e];

    if l2e.SecureMapping? && n == l2e.page { // same page: +1 refs
        calc {
            dataPageRefs(d1, a, n) + {(mapping.l1index, mapping.l2index)};
            { assert d1[l1ptnr].PageDbEntryTyped? && d1[l1ptnr].entry.L1PTable?; }
            (set i1, i2 {:trigger d1[l1pt[i1].v].entry.l2pt[i2]} |
                0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := l1pt[i1]; l1e.Just?
                && d1[l1e.v].PageDbEntryTyped? && d1[l1e.v].entry.L2PTable?
                && var l2e := d1[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2)) + {(mapping.l1index, mapping.l2index)};
            {
                assert forall n:PageNr | n != l2ptnr :: d1[n] == d2[n];
                assert dataPageRefs(d1, a, n) == {};
            }
            (set i1, i2 {:trigger d2[l1pt[i1].v].entry.l2pt[i2]} |
                0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := l1pt[i1]; l1e.Just?
                && d2[l1e.v].PageDbEntryTyped? && d2[l1e.v].entry.L2PTable?
                && var l2e := d2[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2)) + {(mapping.l1index, mapping.l2index)};
            {
                assert forall i | 0 <= i < NR_L2PTES && l2pt'[i].SecureMapping? ::
                    if i == mapping.l2index then l2pt'[i] == l2e
                    else l2pt'[i] == l2pt[i];
            }
            (set i1, i2 {:trigger d2[l1pt[i1].v].entry.l2pt[i2]}
                        {:trigger d2[d2[l1ptnr].entry.l1pt[i1].v].entry.l2pt[i2]} |
                0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := l1pt[i1]; l1e.Just?
                && d2[l1e.v].PageDbEntryTyped? && d2[l1e.v].entry.L2PTable?
                && var l2e := d2[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2));
            dataPageRefs(d2, a, n);
        }
    } else if l2pt[mapping.l2index].SecureMapping? && l2pt[mapping.l2index].page == n {
        // replacing mapping: -1 refs
        calc {
            dataPageRefs(d1, a, n);
            { assert d1[l1ptnr].PageDbEntryTyped? && d1[l1ptnr].entry.L1PTable?; }
            (set i1, i2 {:trigger d1[l1pt[i1].v].entry.l2pt[i2]} |
                0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := l1pt[i1]; l1e.Just?
                && d1[l1e.v].PageDbEntryTyped? && d1[l1e.v].entry.L2PTable?
                && var l2e := d1[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2));
            {
                assert forall n:PageNr | n != l2ptnr :: d1[n] == d2[n];
                assert forall i | 0 <= i < NR_L2PTES && l2pt'[i].SecureMapping? ::
                    l2pt'[i] == l2pt[i] || l2pt'[i] == l2e;
            }
            (set i1, i2 {:trigger d2[l1pt[i1].v].entry.l2pt[i2]} |
                0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := l1pt[i1]; l1e.Just?
                && d2[l1e.v].PageDbEntryTyped? && d2[l1e.v].entry.L2PTable?
                && var l2e := d2[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2)) + {(mapping.l1index, mapping.l2index)};
            dataPageRefs(d2, a, n) + {(mapping.l1index, mapping.l2index)};
        }
    } else {
        calc {
            dataPageRefs(d1, a, n);
            { assert d1[l1ptnr].PageDbEntryTyped? && d1[l1ptnr].entry.L1PTable?; }
            (set i1, i2 {:trigger d1[l1pt[i1].v].entry.l2pt[i2]} |
                0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := l1pt[i1]; l1e.Just?
                && d1[l1e.v].PageDbEntryTyped? && d1[l1e.v].entry.L2PTable?
                && var l2e := d1[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2));
            {
                assert forall n:PageNr | n != l2ptnr :: d1[n] == d2[n];
                assert forall i | 0 <= i < NR_L2PTES && l2pt'[i].SecureMapping? ::
                    l2pt'[i] == l2pt[i] || l2pt'[i] == l2e;
            }
            (set i1, i2 {:trigger d2[l1pt[i1].v].entry.l2pt[i2]} |
                0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                && var l1e := l1pt[i1]; l1e.Just?
                && d2[l1e.v].PageDbEntryTyped? && d2[l1e.v].entry.L2PTable?
                && var l2e := d2[l1e.v].entry.l2pt[i2]; l2e.SecureMapping?
                && l2e.page == n :: (i1, i2));
            dataPageRefs(d2, a, n);
        }
    }
}

lemma lemma_updateL2PtePreservesPageDb(d:PageDb,a:PageNr,mapping:Mapping,l2e:L2PTE)
    requires validPageDb(d)
    requires validMapping(mapping, d, a) && validL2PTE(d, a, l2e)
    requires l2e.SecureMapping? ==>
        validAndEmptyMapping(mapping, d, a) && dataPageRefs(d, a, l2e.page) == {}
    ensures validPageDb(reveal validPageDb(); updateL2Pte(d,a,mapping,l2e))
{
    reveal validPageDb();
    var d' := updateL2Pte(d,a,mapping,l2e);
    
    var addrspace := d[a].entry;
    assert validAddrspace(d, a);

    var l2index := mapping.l2index;
    var l1index := mapping.l1index;

    var l1p := d[a].entry.l1ptnr;
    var l1 := d[l1p].entry;
    var l1p' := d'[a].entry.l1ptnr;
    var l1' := d'[l1p'].entry;
    assert l1p' == l1p;
    assert l1' == l1;

    var l1pte := fromJust(l1.l1pt[l1index]);
    var l1pte' := fromJust(l1'.l1pt[l1index]);
    assert l1pte == l1pte';
    var l2pt := d[l1pte].entry.l2pt;
    var l2pt' := d'[l1pte].entry.l2pt;

    //it's now okay to drop the primes from everything but l2pt'

    assert !stoppedAddrspace(d[a]);
    assert !stoppedAddrspace(d'[a]);

    assert validPageDbEntry(d, a);
    assert validPageDbEntry(d', a) by
    {
        assert d'[a].entry.refcount == d[a].entry.refcount;
        assert addrspaceRefs(d', a) == addrspaceRefs(d, a);
        
    }

    assert validPageDbEntry(d, l1p);
    assert validPageDbEntry(d, l1pte);

    assert validPageDbEntry(d', l1p);
    assert validPageDbEntry(d', l1pte) by
    {
       assert d'[l1pte].entry.L2PTable?;
       assert !stoppedAddrspace(d'[a]);
       assert validL2PTE(d',a,l2e);
       assert wellFormedPageDbEntryTyped(d[l1pte].entry);
       assert wellFormedPageDbEntryTyped(d'[l1pte].entry);

       assert |l2pt| == |l2pt'|;

       forall ( i | 0 <= i < NR_L2PTES && i != l2index )
            ensures validL2PTE(d',a,l2pt'[i])
       {
            assert l2pt'[i] == l2pt[i];
            assert validL2PTE(d,a,l2pt[i]);
       }

    }

    forall ( p | validPageNr(p) && p != l1p && p != l1pte && p != a )
        ensures validPageDbEntry(d', p)
    {
        assert d'[p] == d[p];
        assert validPageDbEntry(d, p);
        assert addrspaceRefs(d', p) == addrspaceRefs(d, p);
        if d[p].PageDbEntryTyped? && d[p].entry.DataPage?
            && !hasStoppedAddrspace(d, p) {
            assert |dataPageRefs(d, d[p].addrspace, p)| <= 1;
            if d[p].addrspace == a {
                lemma_updateL2Pte_dataPageRefs(d, d', a, mapping, l2e, p);
            } else { // diff AS
                assert dataPageRefs(d, d[p].addrspace, p)
                    == dataPageRefs(d', d[p].addrspace, p);
            }
        }
    }
    
    assert wellFormedPageDb(d');
    assert pageDbEntriesValid(d');
    assert pageDbEntriesValidRefs(d');
}
