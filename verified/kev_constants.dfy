
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
function method KEV_SMC_STOP():int            { 29 }

//-----------------------------------------------------------------------------
// Errors
//-----------------------------------------------------------------------------
function method KEV_ERR_SUCCESS():int            { 0 }
function method KEV_ERR_INVALID_PAGENO():int     { 1 }
function method KEV_ERR_PAGEINUSE():int          { 2 }
function method KEV_ERR_INVALID_ADDRSPACE():int  { 3 }
function method KEV_ERR_ALREADY_FINAL():int      { 4 }
function method KEV_ERR_NOT_FINAL():int          { 5 }
function method KEV_ERR_INVALID_MAPPING():int    { 6 }
function method KEV_ERR_ADDRINUSE():int          { 7 }
function method KEV_ERR_NOT_STOPPED():int        { 8 }
function method KEV_ERR_INVALID():int            { 0x1_0000_0000 }

//-----------------------------------------------------------------------------
// Memory Regions
//-----------------------------------------------------------------------------
function method KEVLAR_PAGE_SIZE():int        { 0x1000 }
function method KEVLAR_MON_VBASE():int        { 0x4000_0000 }  
function method KEVLAR_DIRECTMAP_VBASE():int  { 0x8000_0000 }
function method KEVLAR_DIRECTMAP_SIZE():int   { 0x8000_0000 }
function method KEVLAR_SECURE_RESERVE():int   { 1 * 1024 * 1024 }
function method KEVLAR_SECURE_NPAGES():int    { KEVLAR_SECURE_RESERVE() / KEVLAR_PAGE_SIZE() }

function method STACK_LOWER():int { 0x4000 }
function method STACK_UPPER():int { 0x8000 }

//-----------------------------------------------------------------------------
// Data Structures
//-----------------------------------------------------------------------------
function method G_PAGEDB():int { KEVLAR_MON_VBASE() }
function method G_PAGEDB_END():int { G_PAGEDB() + KEVLAR_SECURE_NPAGES() * PAGEDB_ENTRY_SIZE() }
function method G_PAGEDB_ENTRY(pageno:int):int { G_PAGEDB() + pageno * PAGEDB_ENTRY_SIZE() }

// entry = start address of pagedb entry
function method PAGEDB_ENTRY_TYPE(entry:int):int       { entry }
function method PAGEDB_ENTRY_ADDRSPACE(entry:int):int  { entry + 1 }
function method PAGEDB_ENTRY_SIZE():int                { 1 + ADDRSPACE_SIZE() }

// addrspc = start address of address space metadata
function method ADDRSPACE_L1PT(addrspc:int):int        { addrspc }
function method ADDRSPACE_L1PT_PHYS(addrspc:int):int   { addrspc + 1 }
function method ADDRSPACE_REF(addrspc:int):int         { addrspc + 2 }
function method ADDRSPACE_STATE(addrspc:int):int       { addrspc + 3 }
function method ADDRSPACE_SIZE():int                   { 4 }

function method KEV_PAGE_FREE():int                    { 0 }
function method KEV_PAGE_ADDRSPACE():int               { 1 }
function method KEV_PAGE_DISPATCHER():int              { 2 }
function method KEV_PAGE_L1PTABLE():int                { 3 }
function method KEV_PAGE_L2PTABLE():int                { 4 }
function method KEV_PAGE_DATA():int                    { 5 }
function method KEV_PAGE_INVALID():int                 { 6 }

function method KEV_ADDRSPACE_INIT():int               { 0 }
function method KEV_ADDRSPACE_FINAL():int              { 1 }
function method KEV_ADDRSPACE_STOPPED():int            { 2 }
