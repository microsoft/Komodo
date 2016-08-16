include "ARMdef.dfy"

function method KEV_MAGIC():int { 0x4b766c72 }

//-----------------------------------------------------------------------------
// SMC Call Numbers
//-----------------------------------------------------------------------------
function method KEV_SMC_QUERY():int           { 1  }
function method KEV_SMC_GETPHYSPAGES():int    { 2  }
function method KEV_SMC_INIT_ADDRSPACE():int  { 10 }
function method KEV_SMC_INIT_DISPATCHER():int { 11 }
function method KEV_SMC_INIT_L2PTABLE():int   { 12 }
function method KEV_SMC_MAP_SECURE():int      { 13 }
function method KEV_SMC_MAP_INSECURE():int    { 14 }
function method KEV_SMC_REMOVE():int          { 20 }
function method KEV_SMC_FINALISE():int        { 21 }
function method KEV_SMC_ENTER():int           { 22 }
function method KEV_SMC_RESUME():int          { 23 }
function method KEV_SMC_STOP():int            { 29 }

//-----------------------------------------------------------------------------
// Errors
//-----------------------------------------------------------------------------
function method KEV_ERR_SUCCESS():int
    ensures KEV_ERR_SUCCESS() == 0;
    { 0 }
function method KEV_ERR_INVALID_PAGENO():int     { 1  }
function method KEV_ERR_PAGEINUSE():int          { 2  }
function method KEV_ERR_INVALID_ADDRSPACE():int  { 3  }
function method KEV_ERR_ALREADY_FINAL():int      { 4  }
function method KEV_ERR_NOT_FINAL():int          { 5  }
function method KEV_ERR_INVALID_MAPPING():int    { 6  }
function method KEV_ERR_ADDRINUSE():int          { 7  }
function method KEV_ERR_NOT_STOPPED():int        { 8  }
function method KEV_ERR_INTERRUPTED():int        { 9  }
function method KEV_ERR_FAULT():int              { 10 }
function method KEV_ERR_ALREADY_ENTERED():int    { 11 }
function method KEV_ERR_NOT_ENTERED():int        { 12 }
function method KEV_ERR_INVALID():int            { 0x1_0000_0000 }

//-----------------------------------------------------------------------------
// Memory Regions
//-----------------------------------------------------------------------------
function method KEVLAR_PAGE_SIZE():int { PAGESIZE() }

function method KEVLAR_MON_VBASE():int
    ensures KEVLAR_MON_VBASE() == 0x4000_0000;
    { 0x4000_0000 }
function method KEVLAR_DIRECTMAP_VBASE():int
    ensures KEVLAR_DIRECTMAP_VBASE() == 0x8000_0000;
    { 0x8000_0000 }
function method KEVLAR_DIRECTMAP_SIZE():int   { 0x8000_0000 }
function method KEVLAR_SECURE_RESERVE():int
    ensures KEVLAR_SECURE_RESERVE() == 1 * 1024 * 1024;
    { 1 * 1024 * 1024 }
function method KEVLAR_SECURE_NPAGES():int
    ensures KEVLAR_SECURE_NPAGES() == 256;
    { KEVLAR_SECURE_RESERVE() / KEVLAR_PAGE_SIZE() }

// we don't support/consider more than 1GB of physical memory in our maps
function method KEVLAR_PHYSMEM_LIMIT():int
    { 0x4000_0000 }

function KEVLAR_STACK_SIZE():int
    { 0x4000 }

// we don't know where the stack is exactly, but we know how big it is
function {:axiom} StackLimit():int
    ensures WordAligned(StackLimit())
    ensures KEVLAR_MON_VBASE() <= StackLimit()
    ensures StackLimit() <= KEVLAR_DIRECTMAP_VBASE() - KEVLAR_STACK_SIZE()

function StackBase():int
{
    StackLimit() + KEVLAR_STACK_SIZE()
}

predicate address_is_secure(m:mem)
{
    (KEVLAR_DIRECTMAP_VBASE() + SecurePhysBase()) <= m <
        (KEVLAR_DIRECTMAP_VBASE() + SecurePhysBase() + KEVLAR_SECURE_RESERVE())
}        

//-----------------------------------------------------------------------------
// Globals
//-----------------------------------------------------------------------------

function method PAGEDB_ENTRY_SIZE():int { 8 }
function method G_PAGEDB_SIZE():int
    ensures G_PAGEDB_SIZE() == KEVLAR_SECURE_NPAGES() * PAGEDB_ENTRY_SIZE();
    { KEVLAR_SECURE_NPAGES() * PAGEDB_ENTRY_SIZE() }

function method {:opaque} PageDb(): operand { op_sym("g_pagedb") }
function method {:opaque} SecurePhysBaseOp(): operand { op_sym("g_secure_physbase") }

// the phys base is unknown, but never changes
function {:axiom} SecurePhysBase(): int
    ensures 0 < SecurePhysBase() <= KEVLAR_PHYSMEM_LIMIT() - KEVLAR_SECURE_RESERVE();
    ensures PageAligned(SecurePhysBase());

function method KevGlobalDecls(): globaldecls
    ensures ValidGlobalDecls(KevGlobalDecls());
{
    reveal_PageDb(); reveal_SecurePhysBaseOp();
    GlobalDecls(map[SecurePhysBaseOp() := 4, //BytesPerWord()
                    PageDb() := G_PAGEDB_SIZE()])
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
    WordAligned(eval_op(s, op_sp()))
    && StackLimit() < eval_op(s, op_sp()) <= StackBase()
}

predicate SaneMem(s:memstate)
{
    ValidMemState(s)
    // TODO: our insecure phys mapping must be valid
    //&& ValidMemRange(s, KEVLAR_DIRECTMAP_VBASE(),
    //    (KEVLAR_DIRECTMAP_VBASE() + MonitorPhysBaseValue()))
    // our secure phys mapping must be valid
    && ValidMemRange(s, KEVLAR_DIRECTMAP_VBASE() + SecurePhysBase(),
        (KEVLAR_DIRECTMAP_VBASE() + SecurePhysBase() + KEVLAR_SECURE_RESERVE()))
    // the stack must be mapped
    && ValidMemRange(s, StackLimit(), StackBase())
    // globals are as we expect
    && KevGlobalDecls() == TheGlobalDecls()
    && GlobalFullContents(s, SecurePhysBaseOp()) == [SecurePhysBase()]
    // XXX: workaround so dafny sees that these are distinct
    && SecurePhysBaseOp() != PageDb()
}

predicate SaneState(s:state)
{
    ValidState(s) && ValidStack(s) && SaneMem(s.m) && mode_of_state(s) == Monitor
}
