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
function method KEV_SMC_STOP():int            { 29 }

//-----------------------------------------------------------------------------
// Errors
//-----------------------------------------------------------------------------
function method KEV_ERR_SUCCESS():int
    ensures KEV_ERR_SUCCESS() == 0;
    { 0 }
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
function method KEVLAR_PAGE_SIZE():int
    ensures KEVLAR_PAGE_SIZE() == 0x1000
    { 0x1000 }
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

//TODO FIXME
function method G_SECURE_PHYSBASE():int
    ensures G_SECURE_PHYSBASE() == 0x4000_0000;
    { 0x4000_0000 }

//These were picked arbitrarily 
function method STACK_LOWER():int
    ensures STACK_LOWER() == 0x4000
    { 0x4000 }
function method STACK_UPPER():int
    ensures STACK_UPPER() == 0x8000
    { 0x8000 }

//-----------------------------------------------------------------------------
// Data Structures
//-----------------------------------------------------------------------------
function method G_PAGEDB_SIZE():int
    ensures G_PAGEDB_SIZE() == KEVLAR_SECURE_NPAGES() * PAGEDB_ENTRY_SIZE();
    { KEVLAR_SECURE_NPAGES() * PAGEDB_ENTRY_SIZE() }

// computes byte offset of a specific pagedb entry
function method G_PAGEDB_ENTRY(pageno:int):int 
    requires 0 <= pageno < KEVLAR_SECURE_NPAGES();
    ensures G_PAGEDB_ENTRY(pageno) == pageno * PAGEDB_ENTRY_SIZE();
    ensures WordAligned(G_PAGEDB_ENTRY(pageno))
{
    assert WordAligned(PAGEDB_ENTRY_SIZE());
    pageno * PAGEDB_ENTRY_SIZE()
}

// entry = start offset of pagedb entry
function method PAGEDB_ENTRY_TYPE():int { 0 }
function method PAGEDB_ENTRY_ADDRSPACE():int { 4 }
function method PAGEDB_ENTRY_SIZE():int { 8 }

// addrspc = start address of address space metadata
function method ADDRSPACE_L1PT(addrspace:int):int
    ensures ADDRSPACE_L1PT(addrspace) == addrspace;
    { addrspace }
function method ADDRSPACE_L1PT_PHYS(addrspace:int):int
    ensures ADDRSPACE_L1PT_PHYS(addrspace) == addrspace + 4;
    { addrspace + 4 }
function method ADDRSPACE_REF(addrspace:int):int
    ensures ADDRSPACE_REF(addrspace) == addrspace + 8;
    { addrspace + 8 }
function method ADDRSPACE_STATE(addrspace:int):int
    ensures ADDRSPACE_STATE(addrspace) == addrspace + 12;
    { addrspace + 12 }
function method ADDRSPACE_SIZE():int
    ensures ADDRSPACE_SIZE() == 16
    { 16 }

//-----------------------------------------------------------------------------
// Page Types
//-----------------------------------------------------------------------------
function method KEV_PAGE_FREE():int
    ensures KEV_PAGE_FREE() == 0; { 0 }
function method KEV_PAGE_ADDRSPACE():int
    ensures KEV_PAGE_ADDRSPACE() == 1; { 1 }
function method KEV_PAGE_DISPATCHER():int
    ensures KEV_PAGE_DISPATCHER() == 2; { 2 }
function method KEV_PAGE_L1PTABLE():int
    ensures KEV_PAGE_L1PTABLE() == 3; { 3 }
function method KEV_PAGE_L2PTABLE():int
    ensures KEV_PAGE_L2PTABLE() == 4; { 4 }
function method KEV_PAGE_DATA():int
    ensures KEV_PAGE_DATA() == 5; { 5 }

//-----------------------------------------------------------------------------
// Address Space States
//-----------------------------------------------------------------------------
function method KEV_ADDRSPACE_INIT():int
    ensures KEV_ADDRSPACE_INIT() == 0; { 0 }
function method KEV_ADDRSPACE_FINAL():int              { 1 }
function method KEV_ADDRSPACE_STOPPED():int            { 2 }
