include "pagedb.s.dfy"
include "pagedb.i.dfy"
include "ARMdef.dfy"
include "kev_common.s.dfy"

datatype SysState = SysState(hw:state, d:PageDb, g:Globs)
datatype Globs = Globs(g_cur_dispatcher:PageNr)

predicate validGlobs(d:PageDb, g:Globs)
{
    validL1PTPage(d, g.g_cur_dispatcher)
}

predicate validSysState(s:SysState)
{
    ValidState(s.hw) && SaneMem(s.hw.m) && validPageDb(s.d) &&
    pageDbCorresponds(s.hw.m, s.d) && validGlobs(s.d, s.g) && globalsCorrespond(s)
}

predicate globalsCorrespond(s:SysState)
    requires ValidState(s.hw) && SaneMem(s.hw.m)
{
	OSymbol("g_cur_dispatcher") in s.hw.m.globals &&
	|s.hw.m.globals[OSymbol("g_cur_dispatcher")]| == 1 &&
    s.hw.m.globals[OSymbol("g_cur_dispatcher")][0] == s.g.g_cur_dispatcher
}

