include "ARMdef.dfy"
include "pagedb.s.dfy"

datatype SysState = SysState(hw:state, d:PageDb)

predicate validSysState(s:SysState)
{
    ValidState(s.hw) && validPageDb(s.d)
}
