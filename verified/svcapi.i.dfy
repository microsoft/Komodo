include "svcapi.s.dfy"
include "pagedb.i.dfy"
include "mapping.i.dfy"

lemma lemma_nonDataPageRefs(d:PageDb, p:PageNr)
    requires validPageDb(d) && d[p].PageDbEntryTyped? && !hasStoppedAddrspace(d, p)
    requires !d[p].entry.DataPage?
    ensures isAddrspace(d, d[p].addrspace) && dataPageRefs(d, d[p].addrspace, p) == {}
{
    reveal validPageDb();
    var a := d[p].addrspace;
    var l1ptnr := d[a].entry.l1ptnr;
    var l1pt := d[l1ptnr].entry.l1pt;
    assert forall i, j | 0 <= i < NR_L1PTES && l1pt[i].Just? && 0 <= j < NR_L2PTES
        :: validL2PTable(d, a, d[l1pt[i].v].entry.l2pt)
        && validL2PTE(d, a, d[l1pt[i].v].entry.l2pt[j]);
}

lemma lemma_svcMapData_validPageDb(d:PageDb, asPg:PageNr, page:word, mapping:word)
    requires validPageDb(d) && validAddrspacePage(d, asPg)
    ensures validPageDb(svcMapData(d, asPg, page, mapping).0)
{
    reveal validPageDb();
    var rd := svcMapData(d, asPg, page, mapping).0;
    if rd != d {
        var datapg := DataPage(SeqRepeat(PAGESIZE/WORDSIZE, 0));
        var abs_mapping := wordToMapping(mapping);
        assert validAndEmptyMapping(abs_mapping, d, asPg)
            by { reveal wordToMapping(); }
        var l2pte := SecureMapping(page, abs_mapping.perm.w, abs_mapping.perm.x);
        lemma_allocateSparePage(d, page, datapg);
        lemma_nonDataPageRefs(d, page);
        lemma_updateL2PtePreservesPageDb(allocateSparePage(d, page, datapg),
            asPg, abs_mapping, l2pte);
    }
}

lemma lemma_singletonSet_obvious<T>(s:set<T>, e1:T, e2:T)
    requires |s| <= 1 && e1 in s && e2 in s
    ensures e1 == e2 && s == {e1}
{}

lemma lemma_svcUnmapData_validPageDb(d:PageDb, asPg:PageNr, page:word, mapVA:word)
    requires validPageDb(d) && validAddrspacePage(d, asPg) && d[asPg].entry.state.FinalState?
    ensures validPageDb(svcUnmapData(d, asPg, page, mapVA).0)
{
    reveal validPageDb();
    reveal wordToMapping();
    
    var rd := svcUnmapData(d, asPg, page, mapVA).0;
    if rd != d {
        var l1ptnr := d[asPg].entry.l1ptnr;
        var l1pt := d[l1ptnr].entry.l1pt;
        var mapping := wordToMapping(mapVA);
        var l2ptnr := l1pt[mapping.l1index].v;
        var l2pt := d[l2ptnr].entry.l2pt;
        var d1 := updateL2Pte(d, asPg, mapping, NoMapping);
        //assert d1 == d[l2ptnr := d1[l2ptnr]];
        var l2pt' := d1[l2ptnr].entry.l2pt;
        //assert l2pt' == l2pt[mapping.l2index := NoMapping];
        lemma_updateL2PtePreservesPageDb(d, asPg, mapping, NoMapping);
        assert rd == allocateSparePage(d1, page, SparePage);
        //assert rd == d1[page := rd[page]];

        assert forall i, j | 0 <= i < NR_L1PTES && l1pt[i].Just? && 0 <= j < NR_L2PTES
            :: validL2PTable(d, asPg, d[l1pt[i].v].entry.l2pt)
            && validL2PTE(d, asPg, d[l1pt[i].v].entry.l2pt[j])
            && validL2PTable(d1, asPg, d1[l1pt[i].v].entry.l2pt)
            && validL2PTE(d1, asPg, d1[l1pt[i].v].entry.l2pt[j]);

        var oldRefs := dataPageRefs(d, asPg, page);
        assert oldRefs == {(mapping.l1index, mapping.l2index)}
        by {
            var x := (mapping.l1index, mapping.l2index);
            assert |oldRefs| <= 1 && x in oldRefs;
            lemma_singletonSet_obvious(oldRefs, x, x);
        }

        forall (i1, i2 | 0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
            && l1pt[i1].Just? && var l2e := d1[l1pt[i1].v].entry.l2pt[i2];
            l2e.SecureMapping?) ensures d1[l1pt[i1].v].entry.l2pt[i2].page != page
        {
            if i1 == mapping.l1index && i2 == mapping.l2index {
                assert d1[l1pt[i1].v].entry.l2pt[i2].NoMapping?;
            } else {
                assert l2pt[mapping.l2index].SecureMapping? && l2pt[mapping.l2index].page == page;
                assert (i1, i2) !in oldRefs;
                assert d1[l1pt[i1].v].entry.l2pt[i2].page != page;
            }
        }

        assert validL2PTable(d1, asPg, d1[l2ptnr].entry.l2pt);

        forall i | 0 <= i < NR_L2PTES
            ensures validL2PTE(rd, asPg, l2pt'[i])
            ensures i == mapping.l2index <==> (l2pt[i].SecureMapping? && l2pt[i].page == page)
            ensures l2pt[i].SecureMapping? ==> dataPageRefs(d1, asPg, l2pt[i].page) == (
                if i == mapping.l2index then {} else dataPageRefs(d, asPg, l2pt[i].page))
        {
            assert validL2PTE(d1, asPg, l2pt[i]);
            if i == mapping.l2index {
                assert l2pt[i].SecureMapping? && l2pt[i].page == page;
            }
            if l2pt[i].SecureMapping? {
                var oldRefsI := dataPageRefs(d, asPg, l2pt[i].page);
                var newRefsI := dataPageRefs(d1, asPg, l2pt[i].page);
                assert (mapping.l1index, i) in oldRefsI;
                assert isExistingVAForDataPage(d, asPg, mapVA, page);
                if l2pt[i].page == page {
                    assert (mapping.l1index, mapping.l2index) in oldRefsI;
                    lemma_singletonSet_obvious(oldRefsI, (mapping.l1index, i),
                                               (mapping.l1index, mapping.l2index));
                    assert i == mapping.l2index;
                    assert l2pt'[i] == NoMapping;
                    assert (mapping.l1index, i) !in newRefsI;
                    assert (mapping.l1index, i) in oldRefsI;
                    assert |oldRefsI| == 1;
                    calc {
                        newRefsI;
                        { assert d1[l1ptnr].PageDbEntryTyped? && d1[l1ptnr].entry.L1PTable?
                            && d1[l1ptnr].entry.l1pt == l1pt; }
                        (set i1, i2 | 0 <= i1 < NR_L1PTES && 0 <= i2 < NR_L2PTES
                            && l1pt[i1].Just? && var l2e := d1[l1pt[i1].v].entry.l2pt[i2];
                            l2e.SecureMapping? && l2e.page == page :: (i1, i2));
                        ({});
                    }
                    assert newRefsI == {};
                } else {
                    assert oldRefsI == newRefsI;
                }
            }
        }

        forall (n:PageNr | rd[n].PageDbEntryTyped?)
            ensures validPageDbEntryTyped(rd, n)
        {
            if n == page {
                assert validPageDbEntryTyped(rd, n);
            } else if n == l2ptnr {
                assert rd[n] == d1[n];
                assert validL2PTable(d1, asPg, d1[l2ptnr].entry.l2pt);
                assert rd[l2ptnr].entry.l2pt == l2pt';
                assert validL2PTable(rd, asPg, l2pt');
                assert validPageDbEntryTyped(rd, n);
            } else {
                assert rd[n] == d[n];
                var an := d[n].addrspace;
                if d[n].entry.DataPage? {
                    if !hasStoppedAddrspace(d, n) {
                        calc {
                            dataPageRefs(d, an, n);
                            dataPageRefs(d1, an, n);
                            { assert forall n:PageNr | n != page :: rd[n] == d1[n]; }
                            dataPageRefs(rd, an, n);
                        }
                    }
                } else if d[n].entry.Addrspace? {
                    assert addrspaceRefs(rd, n) == addrspaceRefs(d, n);
                    assert validPageDbEntryTyped(rd, n);
                } else if d[n].entry.L2PTable? {
                    if !hasStoppedAddrspace(d, n) {
                        calc {
                            true;
                            validL2PTable(d, an, d[n].entry.l2pt);
                            validL2PTable(d1, an, d[n].entry.l2pt);
                            {
                                if an == asPg {
                                    forall i2 | 0 <= i2 < NR_L2PTES && var pte := d[n].entry.l2pt[i2];
                                               pte.SecureMapping? && pte.page == page
                                        ensures n == l2ptnr
                                    {
                                        //assert oldRefs == dataPageRefs(d, asPg, page);
                                        // FIXME: nothing in validPageDb says all L2s are linked to the L1
                                        var i1 :| 0 <= i1 < NR_L1PTES && l1pt[i1] == Just(n);
                                        assert (i1, i2) in oldRefs;
                                        assert oldRefs == {(mapping.l1index, mapping.l2index)};
                                        assert (i1, i2) == (mapping.l1index, mapping.l2index);
                                    }
                                } else {
                                    assert forall pte | pte in d[n].entry.l2pt
                                        && pte.SecureMapping? :: pte.page != page;
                                }
                            }
                            validL2PTable(rd, an, d[n].entry.l2pt);
                        }
                    }
                }
            }
        }
    }
}

lemma lemma_svcInitL2PTable_validPageDb(d:PageDb, asPg:PageNr, page:word, l1index:word)
    requires validPageDb(d) && validAddrspacePage(d, asPg) && d[asPg].entry.state.FinalState?
    ensures validPageDb(svcInitL2PTable(d, asPg, page, l1index).0)
{
    reveal validPageDb();
    
    var rd := svcInitL2PTable(d, asPg, page, l1index).0;
    if rd != d {
        var l1ptnr := d[asPg].entry.l1ptnr;
        var l1pt := d[l1ptnr].entry.l1pt;

        // no refs to the free page
        forall (i | 0 <= i < NR_L1PTES)
            ensures l1pt[i] != Just(page)
        {
            assert validSparePageForAS(d, asPg, page);
            assert !stoppedAddrspace(d[asPg]);
            assert validL1PTable(d, asPg, l1pt);
            assert l1pt[i].Just? ==> validL1PTE(d, fromJust(l1pt[i]));
        }

        var l2pt := L2PTable(SeqRepeat(NR_L2PTES, NoMapping));
        var d1 := allocateSparePage(d, page, l2pt);
        lemma_allocateSparePage(d, page, l2pt);
        var d2 := installL1PTEInPageDb(d1, l1ptnr, page, l1index);
        lemma_installL1PTEPreservesPageDbValidity(d1, asPg, l1ptnr, page, l1index);
    }
}

lemma lemma_svcHandled_validPageDb(s:state, sd:PageDb, dispPg:PageNr, regs:SvcReturnRegs, rd:PageDb)
    requires ValidState(s) && mode_of_state(s) != User
    requires validPageDb(sd) && validDispatcherPage(sd, dispPg)
    requires isReturningSvc(s)
    requires finalDispatcher(sd, dispPg)
    requires validPageNr(l1pOfDispatcher(sd, dispPg))
    requires (regs, rd) == svcHandled(s, sd, dispPg)
    ensures validPageDb(rd)
{
    reveal validPageDb();
    var addrspace := sd[dispPg].addrspace;
    assert validAddrspacePage(sd, addrspace);

    if regs.0 != KOM_ERR_SUCCESS {
        assert rd == sd;
    } else if s.regs[R0] == KOM_SVC_ATTEST || s.regs[R0] == KOM_SVC_VERIFY_STEP2 {
        assert rd == sd;
    } else if s.regs[R0] == KOM_SVC_VERIFY_STEP0 || s.regs[R0] == KOM_SVC_VERIFY_STEP1 {
        forall n:PageNr | n != dispPg && rd[n].PageDbEntryTyped?
            ensures validPageDbEntryTyped(rd, n)
        {
            assert rd[n] == sd[n];
            assert validPageDbEntryTyped(sd, n);
            var entry := rd[n].entry;
            if (entry.Addrspace?) {
                assert addrspaceRefs(rd, n) == addrspaceRefs(sd, n); // set equality
            } else if (entry.DataPage?) {
                calc {
                    dataPageRefs(sd, sd[n].addrspace, n);
                    { assert forall i:PageNr | rd[i].PageDbEntryTyped?
                        && i != dispPg :: rd[i] == sd[i]; }
                    dataPageRefs(rd, rd[n].addrspace, n);
                }
            }
        }
    } else if s.regs[R0] == KOM_SVC_MAP_DATA {
        lemma_svcMapData_validPageDb(sd, addrspace, s.regs[R1], s.regs[R2]);
    } else if s.regs[R0] == KOM_SVC_UNMAP_DATA {
        lemma_svcUnmapData_validPageDb(sd, addrspace, s.regs[R1], s.regs[R2]);
    } else if s.regs[R0] == KOM_SVC_INIT_L2PTABLE {
        lemma_svcInitL2PTable_validPageDb(sd, addrspace, s.regs[R1], s.regs[R2]);
    }
}
