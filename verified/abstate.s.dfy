include "pagedb.s.dfy"
include "ARMdef.dfy"
include "kom_common.s.dfy"

datatype SysState = SysState(hw:state, d:PageDb)

predicate validSysState(s:SysState)
{
    ValidState(s.hw) /*&& SaneMem(s.hw.m)*/ && validPageDb(s.d)
}
