include "svcapi.s.dfy"
include "pagedb.i.dfy"
include "mapping.i.dfy"

lemma lemma_svcMapData_validPageDb(d:PageDb, asPg:PageNr, page:word, mapping:word)
    requires validPageDb(d) && validAddrspacePage(d, asPg)
    ensures validPageDb(svcMapData(d, asPg, page, mapping).0)
{
    var rd := svcMapData(d, asPg, page, mapping).0;
    if rd != d {
        var datapg := DataPage(SeqRepeat(PAGESIZE/WORDSIZE, 0));
        var abs_mapping := wordToMapping(mapping);
        var l2pte := SecureMapping(page, abs_mapping.perm.w, abs_mapping.perm.x);
        lemma_allocateSparePage(d, page, datapg);
        lemma_updateL2PtePreservesPageDb(allocateSparePage(d, page, datapg),
            asPg, abs_mapping, l2pte);
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
            assert validL1PTable(d, l1ptnr);
            assert l1pt[i].Just? ==> validL1PTE(d, fromJust(l1pt[i]));
        }

        var l2pt := L2PTable(SeqRepeat(NR_L2PTES, NoMapping));
        var d1 := allocateSparePage(d, page, l2pt);
        lemma_allocateSparePage(d, page, l2pt);
        var d2 := installL1PTEInPageDb(d1, l1ptnr, page, l1index);
        installL1PTEPreservesPageDbValidity(d1, l1ptnr, page, l1index);
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
        forall n | validPageNr(n) ensures validPageDbEntry(rd, n)
        {
            var e := rd[n];
            if (e.PageDbEntryTyped?)
            {
                var entry := e.entry;
                if (entry.Addrspace?)
                {
                    assert addrspaceRefs(rd, n) == addrspaceRefs(sd, n); // set equality
                }
            }
        }
    } else if s.regs[R0] == KOM_SVC_MAP_DATA {
        lemma_svcMapData_validPageDb(sd, addrspace, s.regs[R1], s.regs[R2]);
    } else if s.regs[R0] == KOM_SVC_INIT_L2PTABLE {
        lemma_svcInitL2PTable_validPageDb(sd, addrspace, s.regs[R1], s.regs[R2]);
    }
}
