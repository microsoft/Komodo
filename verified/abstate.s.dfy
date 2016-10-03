include "pagedb.s.dfy"
include "ARMdef.dfy"
include "kom_common.s.dfy"

datatype SysState = SysState(hw:state, d:PageDb, g:Globs)
datatype Globs = Globs(g_cur_dispatcher:PageNr)

predicate validGlobs(d:PageDb, g:Globs)
{
    validDispatcherPage(d, g.g_cur_dispatcher)
}

predicate validSysState(s:SysState)
{
    ValidState(s.hw) && SaneMem(s.hw.m) && validPageDb(s.d) &&
    validGlobs(s.d, s.g) && globalsCorrespond(s)
}

predicate globalsCorrespond(s:SysState)
    requires ValidState(s.hw) && SaneMem(s.hw.m)
{
    GlobalFullContents(s.hw.m, CurAddrspaceOp())[0] == s.g.g_cur_dispatcher
}
