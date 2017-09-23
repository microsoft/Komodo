include "kom_common.i.dfy"
include "pagedb.i.dfy"

//-----------------------------------------------------------------------------
// 
//-----------------------------------------------------------------------------

predicate SaneSvcState(s:state, d:PageDb, dispPg: PageNr)
{
    SaneState(s) && s.conf.tlb_consistent
        && validPageDb(d) && pageDbCorresponds(s.m, d) && finalDispatcher(d, dispPg)
        && GlobalWord(s.m, CurDispatcherOp(), 0) == page_monvaddr(dispPg)
        && s.conf.ttbr0.ptbase == page_paddr(l1pOfDispatcher(d, dispPg))
}
