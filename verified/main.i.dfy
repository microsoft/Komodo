include "ARMprint.dfy"
include "smc_handler.gen.dfy"

method Main()
{
    printHeader();
    var n := printFunction("smc_handler", sp_code_smc_handler(), 0);
    printBss(KomGlobalDecls());
    printFooter();
}
