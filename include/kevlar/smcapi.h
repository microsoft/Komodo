#define KVR_SMC_QUERY           1

#define KVR_MAGIC 0x4b766c72 // "Kvlr"

// returns KVR_MAGIC
uint32_t kvr_smc_query(void);

#define KVR_SMC_GETPHYSPAGES    2

uint32_t kvr_smc_get_phys_pages(void);
