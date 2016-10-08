include "ARMdef.dfy"

function method KOM_MAGIC():int { 0x4b6d646f }

//-----------------------------------------------------------------------------
// SMC Call Numbers
//-----------------------------------------------------------------------------
function method KOM_SMC_QUERY():int           { 1  }
function method KOM_SMC_GETPHYSPAGES():int    { 2  }
function method KOM_SMC_INIT_ADDRSPACE():int  { 10 }
function method KOM_SMC_INIT_DISPATCHER():int { 11 }
function method KOM_SMC_INIT_L2PTABLE():int   { 12 }
function method KOM_SMC_MAP_SECURE():int      { 13 }
function method KOM_SMC_MAP_INSECURE():int    { 14 }
function method KOM_SMC_REMOVE():int          { 20 }
function method KOM_SMC_FINALISE():int        { 21 }
function method KOM_SMC_ENTER():int           { 22 }
function method KOM_SMC_RESUME():int          { 23 }
function method KOM_SMC_STOP():int            { 29 }

//-----------------------------------------------------------------------------
// Errors
//-----------------------------------------------------------------------------
function method KOM_ERR_SUCCESS():int            { 0  }
function method KOM_ERR_INVALID_PAGENO():int     { 1  }
function method KOM_ERR_PAGEINUSE():int          { 2  }
function method KOM_ERR_INVALID_ADDRSPACE():int  { 3  }
function method KOM_ERR_ALREADY_FINAL():int      { 4  }
function method KOM_ERR_NOT_FINAL():int          { 5  }
function method KOM_ERR_INVALID_MAPPING():int    { 6  }
function method KOM_ERR_ADDRINUSE():int          { 7  }
function method KOM_ERR_NOT_STOPPED():int        { 8  }
function method KOM_ERR_INTERRUPTED():int        { 9  }
function method KOM_ERR_FAULT():int              { 10 }
function method KOM_ERR_ALREADY_ENTERED():int    { 11 }
function method KOM_ERR_NOT_ENTERED():int        { 12 }
function method KOM_ERR_INVALID():int            { 0xffffffff }

//-----------------------------------------------------------------------------
// Memory Regions
//-----------------------------------------------------------------------------
function method KOM_MON_VBASE():addr
    { 0x4000_0000 }
function method KOM_DIRECTMAP_VBASE():addr
    { 0x8000_0000 }
function method KOM_DIRECTMAP_SIZE():word   { 0x8000_0000 }
function method KOM_SECURE_RESERVE():addr
    { 1 * 1024 * 1024 }
function method KOM_SECURE_NPAGES():word
    ensures KOM_SECURE_NPAGES() == 256;
    { KOM_SECURE_RESERVE() / PAGESIZE() }

// we don't support/consider more than 1GB of physical memory in our maps
function method KOM_PHYSMEM_LIMIT():addr
    { 0x4000_0000 }

function KOM_STACK_SIZE():addr
    { 0x4000 }

// we don't know where the stack is exactly, but we know how big it is
function {:axiom} StackLimit():addr
    ensures KOM_MON_VBASE() <= StackLimit()
    ensures StackLimit() <= KOM_DIRECTMAP_VBASE() - KOM_STACK_SIZE()

function StackBase():addr
{
    StackLimit() + KOM_STACK_SIZE()
}

predicate address_is_secure(m:addr)
{
    (KOM_DIRECTMAP_VBASE() + SecurePhysBase()) <= m <
        (KOM_DIRECTMAP_VBASE() + SecurePhysBase() + KOM_SECURE_RESERVE())
}

//-----------------------------------------------------------------------------
// Globals
//-----------------------------------------------------------------------------

function method PAGEDB_ENTRY_SIZE():int { 8 }
function method G_PAGEDB_SIZE():int
    { KOM_SECURE_NPAGES() * PAGEDB_ENTRY_SIZE() }

function method {:opaque} SavedSPs(): operand { OSymbol("g_saved_sps") }
function method {:opaque} SavedLRs(): operand { OSymbol("g_saved_lrs") }
function method {:opaque} SavedPSRs(): operand { OSymbol("g_saved_psrs") }
function method {:opaque} PageDb(): operand { OSymbol("g_pagedb") }
function method {:opaque} SecurePhysBaseOp(): operand { OSymbol("g_secure_physbase") }
function method {:opaque} CurAddrspaceOp(): operand { OSymbol("g_cur_addrspace") }

// the phys base is unknown, but never changes
function {:axiom} SecurePhysBase(): addr
    ensures 0 < SecurePhysBase() <= KOM_PHYSMEM_LIMIT() - KOM_SECURE_RESERVE();
    ensures PageAligned(SecurePhysBase());

function method KomGlobalDecls(): globaldecls
    ensures ValidGlobalDecls(KomGlobalDecls());
{
    reveal_PageDb(); reveal_SecurePhysBaseOp(); reveal_CurAddrspaceOp();
    reveal_SavedSPs(); reveal_SavedLRs(); reveal_SavedPSRs();
    map[SecurePhysBaseOp() := 4, //BytesPerWord() 
        CurAddrspaceOp() := 4,   //BytesPerWord()
        SavedSPs() := 28,        //BytesPerWord() * number of modes
        SavedLRs() := 28,        //BytesPerWord() * number of modes
        SavedPSRs() := 28,        //BytesPerWord() * number of modes
        PageDb() := G_PAGEDB_SIZE()]
}

//-----------------------------------------------------------------------------
// Application-level state invariants
//
// These are part of the spec, since we rely on the bootloader setting
// up our execution environment so they are ensured on SMC handler entry.
//-----------------------------------------------------------------------------

predicate ValidStack(s:state)
    requires ValidState(s)
{
    WordAligned(OperandContents(s, OSP))
    && StackLimit() < OperandContents(s, OSP) <= StackBase()
}

predicate SaneMem(s:memstate)
{
    SaneConstants() && ValidMemState(s)
    // globals are as we expect
    && GlobalFullContents(s, SecurePhysBaseOp()) == [SecurePhysBase()]
}

predicate SaneConstants()
{
    PhysBase() == KOM_DIRECTMAP_VBASE()
    && TheValidAddresses() == (
        // our secure phys mapping must be valid
        (set m:addr | KOM_DIRECTMAP_VBASE() + SecurePhysBase() <= m
               < KOM_DIRECTMAP_VBASE() + SecurePhysBase() + KOM_SECURE_RESERVE())
        // the stack must be mapped
        + (set m:addr | StackLimit() <= m < StackBase()))
    // TODO: our insecure phys mapping must be valid
    //ValidMemRange(KOM_DIRECTMAP_VBASE(),
    //    (KOM_DIRECTMAP_VBASE() + MonitorPhysBaseValue()))

    // globals are as we expect
    && KomGlobalDecls() == TheGlobalDecls()
    // XXX: workaround so dafny sees that these are distinct
    && SecurePhysBaseOp() != PageDb()
    && SecurePhysBaseOp() != CurAddrspaceOp()
    && CurAddrspaceOp() != PageDb()
    && SavedSPs() != SavedLRs()
    && SavedSPs() != SecurePhysBaseOp()
    && SavedSPs() != PageDb()
    && SavedSPs() != CurAddrspaceOp()
    && SavedSPs() != SavedPSRs()
    && SavedLRs() != SecurePhysBaseOp()
    && SavedLRs() != PageDb()
    && SavedLRs() != CurAddrspaceOp()
    && SavedLRs() != SavedPSRs()
    && SavedPSRs() != SecurePhysBaseOp()
    && SavedPSRs() != CurAddrspaceOp()
    && SavedPSRs() != PageDb()
    // && forall s, r | ValidState(s) :: ApplicationUsermodeContinuationInvariant(s, r)
    //     <==> ( s == r)
}

predicate SaneState(s:state)
{
    SaneConstants() && ValidState(s) && ValidStack(s) && SaneMem(s.m) && mode_of_state(s) == Monitor
}



predicate bankedRegsPreserved(hw:state, hw':state)
    requires ValidState(hw) && ValidState(hw')
{
    reveal_ValidRegState();
    reveal_ValidSRegState();
    reveal_ValidConfig();
    // It would probably be better if we had a lemma that proved that these 
    // were the same thing... but for now both seem equally trustworth, so 
    // let's use the one that's easier to prove
    // hw.conf.spsr[Monitor] == hw'.conf.spsr[Monitor] &&
    hw.sregs[spsr(Monitor)] == hw'.sregs[spsr(Monitor)] &&

    // Sadly this has to be unrolled
    hw.regs[LR(FIQ)] == hw'.regs[LR(FIQ)] &&
    hw.regs[LR(IRQ)] == hw'.regs[LR(IRQ)] &&
    hw.regs[LR(Supervisor)] == hw'.regs[LR(Supervisor)] &&
    hw.regs[LR(Abort)] == hw'.regs[LR(Abort)] &&
    hw.regs[LR(Undefined)] == hw'.regs[LR(Undefined)] &&
    hw.regs[LR(Monitor)] == hw'.regs[LR(Monitor)] &&

    hw.regs[SP(FIQ)] == hw'.regs[SP(FIQ)] &&
    hw.regs[SP(IRQ)] == hw'.regs[SP(IRQ)] &&
    hw.regs[SP(Supervisor)] == hw'.regs[SP(Supervisor)] &&
    hw.regs[SP(Abort)] == hw'.regs[SP(Abort)] &&
    hw.regs[SP(Undefined)] == hw'.regs[SP(Undefined)] &&
    hw.regs[SP(Monitor)] == hw'.regs[SP(Monitor)]

}
