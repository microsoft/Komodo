include "pagedb.s.dfy"
include "ARMdef.dfy"
include "kom_common.s.dfy"

datatype SysState = SysState(hw:state, d:PageDb, g:Globs)
type bankedreg = map<mode,int>
datatype Globs = Globs(g_cur_dispatcher:PageNr,g_sps:bankedreg,g_lrs:bankedreg,
    g_psrs:bankedreg)

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
    && (forall m :: m in s.g.g_sps && m in s.g.g_lrs && m in s.g.g_psrs)

    && GlobalFullContents(s.hw.m, SavedSPs())[0] == s.g.g_sps[User]
    && GlobalFullContents(s.hw.m, SavedSPs())[1] == s.g.g_sps[FIQ]
    && GlobalFullContents(s.hw.m, SavedSPs())[2] == s.g.g_sps[IRQ]
    && GlobalFullContents(s.hw.m, SavedSPs())[3] == s.g.g_sps[Supervisor]
    && GlobalFullContents(s.hw.m, SavedSPs())[4] == s.g.g_sps[Abort]
    && GlobalFullContents(s.hw.m, SavedSPs())[5] == s.g.g_sps[Undefined]
    && GlobalFullContents(s.hw.m, SavedSPs())[6] == s.g.g_sps[Monitor]

    && GlobalFullContents(s.hw.m, SavedLRs())[0] == s.g.g_lrs[User]
    && GlobalFullContents(s.hw.m, SavedLRs())[1] == s.g.g_lrs[FIQ]
    && GlobalFullContents(s.hw.m, SavedLRs())[2] == s.g.g_lrs[IRQ]
    && GlobalFullContents(s.hw.m, SavedLRs())[3] == s.g.g_lrs[Supervisor]
    && GlobalFullContents(s.hw.m, SavedLRs())[4] == s.g.g_lrs[Abort]
    && GlobalFullContents(s.hw.m, SavedLRs())[5] == s.g.g_lrs[Undefined]
    && GlobalFullContents(s.hw.m, SavedLRs())[6] == s.g.g_lrs[Monitor]

    && GlobalFullContents(s.hw.m, SavedPSRs())[0] == s.g.g_psrs[User]
    && GlobalFullContents(s.hw.m, SavedPSRs())[1] == s.g.g_psrs[FIQ]
    && GlobalFullContents(s.hw.m, SavedPSRs())[2] == s.g.g_psrs[IRQ]
    && GlobalFullContents(s.hw.m, SavedPSRs())[3] == s.g.g_psrs[Supervisor]
    && GlobalFullContents(s.hw.m, SavedPSRs())[4] == s.g.g_psrs[Abort]
    && GlobalFullContents(s.hw.m, SavedPSRs())[5] == s.g.g_psrs[Undefined]
    && GlobalFullContents(s.hw.m, SavedPSRs())[6] == s.g.g_psrs[Monitor]
}

