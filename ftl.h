#ifndef __FEMU_FTL_H
#define __FEMU_FTL_H

#include "../nvme.h"

#define INVALID_PPA     (~(0ULL))
#define INVALID_LPN     (~(0ULL))
#define UNMAPPED_PPA    (~(0ULL))

enum {
    NAND_READ =  0,
    NAND_WRITE = 1,
    NAND_ERASE = 2,

    NAND_READ_LATENCY = 40000,
    NAND_PROG_LATENCY = 200000,
    NAND_ERASE_LATENCY = 2000000,
};

enum {
    USER_IO = 0,
    GC_IO = 1,
};

enum {
    SEC_FREE = 0,
    SEC_INVALID = 1,
    SEC_VALID = 2,

    PG_FREE = 0,
    PG_INVALID = 1,
    PG_VALID = 2
};

enum {
    FEMU_ENABLE_GC_DELAY = 1,
    FEMU_DISABLE_GC_DELAY = 2,

    FEMU_ENABLE_DELAY_EMU = 3,
    FEMU_DISABLE_DELAY_EMU = 4,

    FEMU_RESET_ACCT = 5,
    FEMU_ENABLE_LOG = 6,
    FEMU_DISABLE_LOG = 7,
};


#define BLK_BITS    (16)
#define PG_BITS     (16)
#define SEC_BITS    (8)
#define PL_BITS     (8)
#define LUN_BITS    (8)
#define CH_BITS     (7)

/* describe a physical page addr */
struct ppa {
    union {
        struct {
            uint64_t blk : BLK_BITS;
            uint64_t pg  : PG_BITS;
            uint64_t sec : SEC_BITS;
            uint64_t pl  : PL_BITS;
            uint64_t lun : LUN_BITS;
            uint64_t ch  : CH_BITS;
            uint64_t rsv : 1;
        } g;

        uint64_t ppa;
    };
};

typedef int nand_sec_status_t;

struct nand_page {
    nand_sec_status_t *sec;
    int nsecs;
    int status;
};

struct nand_block {
    struct nand_page *pg;
    int npgs;
    int ipc; /* invalid page count */
    int vpc; /* valid page count */
    int erase_cnt;
    int wp; /* current write pointer */
};

struct nand_plane {
    struct nand_block *blk;
    int nblks;
};

struct nand_lun {
    struct nand_plane *pl;
    int npls;
    uint64_t next_lun_avail_time;
    bool busy;
    uint64_t gc_endtime;
};

struct ssd_channel {
    struct nand_lun *lun;
    int nluns;
    uint64_t next_ch_avail_time;
    bool busy;
    uint64_t gc_endtime;
};

struct ssdparams {
    int secsz;        /* sector size in bytes */
    int secs_per_pg;  /* # of sectors per page */
    int pgs_per_blk;  /* # of NAND pages per block */
    int blks_per_pl;  /* # of blocks per plane */
    int pls_per_lun;  /* # of planes per LUN (Die) */
    int luns_per_ch;  /* # of LUNs per channel */
    int nchs;         /* # of channels in the SSD */

    int pg_rd_lat;    /* NAND page read latency in nanoseconds */
    int pg_wr_lat;    /* NAND page program latency in nanoseconds */
    int blk_er_lat;   /* NAND block erase latency in nanoseconds */
    int ch_xfer_lat;  /* channel transfer latency for one page in nanoseconds
                       * this defines the channel bandwith
                       */

    double gc_thres_pcent;
    int gc_thres_lines;
    double gc_thres_pcent_high;
    int gc_thres_lines_high;
    bool enable_gc_delay;

    /* below are all calculated values */
    int secs_per_blk; /* # of sectors per block */
    int secs_per_pl;  /* # of sectors per plane */
    int secs_per_lun; /* # of sectors per LUN */
    int secs_per_ch;  /* # of sectors per channel */
    int tt_secs;      /* # of sectors in the SSD */

    int pgs_per_pl;   /* # of pages per plane */
    int pgs_per_lun;  /* # of pages per LUN (Die) */
    int pgs_per_ch;   /* # of pages per channel */
    int tt_pgs;       /* total # of pages in the SSD */

    int blks_per_lun; /* # of blocks per LUN */
    int blks_per_ch;  /* # of blocks per channel */
    int tt_blks;      /* total # of blocks in the SSD */

    int secs_per_line;
    int pgs_per_line;
    int blks_per_line;
    int tt_lines;

    int pls_per_ch;   /* # of planes per channel */
    int tt_pls;       /* total # of planes in the SSD */

    int tt_luns;      /* total # of LUNs in the SSD */

    // FEMU CDFTL
    int tspace_size; /* translation space size in pages */
};

typedef struct line {
    int id;  /* line id, the same as corresponding block id */
    int ipc; /* invalid page count in this line */
    int vpc; /* valid page count in this line */
    QTAILQ_ENTRY(line) entry; /* in either {free,victim,full} list */
    /* position in the priority queue for victim lines */
    size_t                  pos;
} line;

/* wp: record next write addr */
struct write_pointer {
    struct line *curline;
    int ch;
    int lun;
    int pg;
    int blk;
    int pl;
};

struct line_mgmt {
    struct line *lines;
    /* free line list, we only need to maintain a list of blk numbers */
    QTAILQ_HEAD(free_line_list, line) free_line_list;
    pqueue_t *victim_line_pq;
    //QTAILQ_HEAD(victim_line_list, line) victim_line_list;
    QTAILQ_HEAD(full_line_list, line) full_line_list;
    int tt_lines;
    int free_line_cnt;
    int victim_line_cnt;
    int full_line_cnt;
};

struct nand_cmd {
    int type;
    int cmd;
    int64_t stime; /* Coperd: request arrival time */
};

struct ssd {
    char *ssdname;
    struct ssdparams sp;
    struct ssd_channel *ch;
    struct ppa *maptbl; /* page level mapping table */
    uint64_t *rmap;     /* reverse mapptbl, assume it's stored in OOB */
    struct write_pointer wp;
    struct line_mgmt lm;

    /* lockless ring for communication with NVMe IO thread */
    struct rte_ring **to_ftl;
    struct rte_ring **to_poller;
    bool *dataplane_started_ptr;
    QemuThread ftl_thread;

    // FEMU Intro & Add Command
    uint64_t        host_writes;
    uint64_t        gc_writes;

    // CMT/CTP hit rate logging
    uint64_t        cmt_hits;
    uint64_t        ctp_hits;
    uint64_t        cache_misses;
    uint64_t        total_requests;
};

void ssd_init(FemuCtrl *n);

#ifdef FEMU_DEBUG_FTL
#define ftl_debug(fmt, ...) \
    do { printf("[FEMU] FTL-Dbg: " fmt, ## __VA_ARGS__); } while (0)
#else
#define ftl_debug(fmt, ...) \
    do { } while (0)
#endif

#define ftl_err(fmt, ...) \
    do { fprintf(stderr, "[FEMU] FTL-Err: " fmt, ## __VA_ARGS__); } while (0)

#define ftl_log(fmt, ...) \
    do { printf("[FEMU] FTL-Log: " fmt, ## __VA_ARGS__); } while (0)


/* FEMU assert() */
#ifdef FEMU_DEBUG_FTL
#define ftl_assert(expression) assert(expression)
#else
#define ftl_assert(expression)
#endif

#endif

// FEMU CDFTL
struct map_page {
    struct ppa *dppn;
};

struct gtd_entry {
    struct ppa tppn;
    bool location;
    bool dirty;
};

struct cmt_entry {
    struct data {
        uint64_t dlpn;
        struct ppa dppn;
        bool dirty;
    } data;
    struct cmt_entry *prev;
    struct cmt_entry *next;
    struct cmt_entry *lru_prev;
    struct cmt_entry *lru_next;
};

struct cmt_hash {
    uint64_t hash_value;
    struct cmt_entry *cmt_entries;
    struct cmt_hash *hash_next;
};

typedef struct {
    struct cmt_entry *head; // MRU (Most Recently Used) - 리스트의 맨 앞
    struct cmt_entry *tail; // LRU (Least Recently Used) - 리스트의 맨 뒤
} cmt_lru_list;

struct ctp_entry {
    uint64_t tvpn;
    struct map_page *mp;
    struct ppa tppn;
    struct ctp_entry *prev;
    struct ctp_entry *next;
    struct ctp_entry *lru_prev;
    struct ctp_entry *lru_next;
};

struct ctp_hash {
    uint64_t hash_value;
    struct ctp_entry *ctp_entries;
    struct ctp_hash *hash_next;
};

typedef struct {
    struct ctp_entry *head; // MRU (Most Recently Used) - 리스트의 맨 앞
    struct ctp_entry *tail; // LRU (Least Recently Used) - 리스트의 맨 뒤
} ctp_lru_list;

// gtd, cmt, ctp
#define PAGE_DATA_SIZE 4096
#define NUM_MAPPINGS_PER_PAGE (PAGE_DATA_SIZE / sizeof(struct ppa))
#define MAX_TPPN 4096
#define MAX_TVPN 3072
#define MAX_CMTN 1024   // entry하나 당 8B
#define MAX_CTPN 32     // entry하나 당 4096B
#define NUM_CMT_BUCKETS 10
#define NUM_CTP_BUCKETS 5
#define BLOCK_LIST_SIZE 16

// gtd, cmt, ctp manipulate functions
int is_cache_full(void);
int is_ctp_full(void);

struct cmt_entry* cmt_creat_entry(void);
struct cmt_entry* cmt_find_entry(uint64_t dlpn);
void cmt_insert_entry(struct cmt_entry *new_entry);
void cmt_remove_entry(struct cmt_entry *entry);
void cmt_evict_entry(void);

struct ctp_entry* ctp_creat_entry(void);
struct ctp_entry* ctp_find_entry(uint64_t tvpn);
void ctp_insert_entry(struct ctp_entry *new_entry);
void ctp_remove_entry(struct ctp_entry *entry);
void ctp_evict_entry(void);

void tinit(void);
void gtd_init(void);
void cmt_init(void);
void ctp_init(void);

// CMT LRU List Functions
void cmt_lru_list_init(cmt_lru_list *list);
void cmt_lru_list_remove(cmt_lru_list *list, struct cmt_entry *entry);
void cmt_lru_list_add_to_front(cmt_lru_list *list, struct cmt_entry *entry);
void cmt_lru_list_move_to_front(cmt_lru_list *list, struct cmt_entry *entry);

// CTP LRU List Functions
void ctp_lru_list_init(ctp_lru_list *list);
void ctp_lru_list_remove(ctp_lru_list *list, struct ctp_entry *entry);
void ctp_lru_list_add_to_front(ctp_lru_list *list, struct ctp_entry *entry);
void ctp_lru_list_move_to_front(ctp_lru_list *list, struct ctp_entry *entry);

int select_victim_greedy(void);
void map_garbage_collection(void);
int cached_num(void);
void fetch_in(uint64_t dlpn);
void ctp_fetch_in(uint64_t dlpn);
void replace(uint64_t dlpn, uint64_t dppn);

/*** Translation Flash Space ***/
/* function prototypes */
int tnand_init(int nbanks, int nblks, int npages);
int tnand_read(int bank, int blk, int page, void *data);
int tnand_write(int bank, int blk, int page, void *data);
int tnand_erase(int bank, int blk);

/* return code */
#define NAND_SUCCESS        0
#define NAND_ERR_INVALID	-1
#define NAND_ERR_OVERWRITE	-2
#define NAND_ERR_POSITION	-3
#define NAND_ERR_EMPTY		-4

typedef struct _Page {
	uint8_t data[PAGE_DATA_SIZE];
} Page;

/*** Free T Block List (FIFO Queue) ***/
typedef struct {
	int* queue;
	int head;       // front
	int tail;       // rear
	int cap;        // buffer capacity
	int q_size;     // current size
} Queuetype;
Queuetype* create_queue(void);
void init_queue(Queuetype* h);
int is_full(const Queuetype* h);
int is_empty(const Queuetype* h);
void enqueue(Queuetype* h, int item);
int dequeue(Queuetype* h);

/*** Active T Block List (Min Heap) ***/
typedef struct {
	int heap[BLOCK_LIST_SIZE+1];
	int heap_size;
} Heaptype;
Heaptype* create_heap(void);
void init_heap(Heaptype* h);
void insert_minheap(Heaptype* h, int item);
int delete_minheap(Heaptype* h);

typedef struct {
	uint64_t bnum; // block number
	uint64_t p_cur; // page cursor
} BNUM;