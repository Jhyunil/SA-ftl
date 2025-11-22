#include "ftl.h"

// FEMU CDFTL
#define INVALID_PPN (-1)
Page* tnand;
uint8_t* is_w;
size_t NBANKS, NBLKS, NPAGES, PAGES_PER_BANK;

uint64_t cmtn; // size of current CMT
uint64_t ctpn; // size of current CTP
uint64_t tp2l[MAX_TPPN];
struct gtd_entry gtd[MAX_TVPN];
struct cmt_hash cmt[NUM_CMT_BUCKETS];
struct ctp_hash ctp[NUM_CTP_BUCKETS];
ctp_lru_list ctp_lru;
cmt_lru_list cmt_lru;

/*** Translation Flash Space ***/
int tnand_init(int nbanks, int nblks, int npages)
{
	if((nbanks <= 0 || nblks <= 0) || npages <= 0) return NAND_ERR_INVALID;

	size_t tmp, total_pages;
	tmp = (size_t)nbanks * (size_t)nblks;
	if(tmp > SIZE_MAX / (size_t)npages) return NAND_ERR_INVALID;
	total_pages = tmp * (size_t)npages;

	tnand = (Page*)calloc(total_pages, sizeof(Page));
	is_w = (uint8_t*)calloc(total_pages, sizeof(uint8_t));
	if(!tnand || !is_w) { free(tnand); free(is_w); return NAND_ERR_INVALID; }

	NBANKS = (size_t)nbanks;
	NBLKS = (size_t)nblks;
	NPAGES = (size_t)npages;
	PAGES_PER_BANK = NBLKS * NPAGES;
	
    // femu_log("\n\n\nTranslation Space1 : %d\n\n\n", (int)(total_pages * sizeof(Page)));
    // FILE *fp = fopen("/home/femu/translation_space.txt", "w");
    // if (fp == NULL) {
    //     femu_err("Failed to create translation_space.txt\n");
    //     return NAND_ERR_INVALID;
    // }
    // fprintf(fp, "Translation Space Size: %zu bytes\n", total_pages * sizeof(Page));
    // fclose(fp);

	return NAND_SUCCESS;
}

int tnand_write(int bank, int blk, int page, void *data)
{
	int flag_bk, flag_bl, flag_pg; 
	flag_bk = flag_bl = flag_pg = 0;
	size_t flat_idx = (bank * (PAGES_PER_BANK)) + (blk * (NPAGES)) + page; // page idx

	if(bank < 0 || bank >= NBANKS) flag_bk++;
	if(blk < 0 || blk >= NBLKS) flag_bl++;
	if(page < 0 || page >= NPAGES) flag_pg++;
	if((flag_bk || flag_bl) || flag_pg) return NAND_ERR_INVALID;
	if(is_w[flat_idx]) return NAND_ERR_OVERWRITE;
	if(page && !is_w[flat_idx-1]) return NAND_ERR_POSITION;


	memcpy(tnand[flat_idx].data, data, PAGE_DATA_SIZE * sizeof(uint8_t));
	// memcpy(tnand[flat_idx].spare, spare, PAGE_SPARE_SIZE * sizeof(uint8_t));
	is_w[flat_idx] = 1;

	return NAND_SUCCESS;
}

int tnand_read(int bank, int blk, int page, void *data)
{
	int flag_bk, flag_bl, flag_pg;
	flag_bk = flag_bl = flag_pg = 0;
	size_t flat_idx = (bank * (PAGES_PER_BANK)) + (blk * (NPAGES)) + page; // page idx

	if(bank < 0 || bank >= NBANKS) flag_bk++;
	if(blk < 0 || blk >= NBLKS) flag_bl++;
	if(page < 0 || page >= NPAGES) flag_pg++;
	if((flag_bk || flag_bl) || flag_pg) return NAND_ERR_INVALID;
	if(!is_w[flat_idx]) return NAND_ERR_EMPTY;

	memcpy(data, tnand[flat_idx].data, PAGE_DATA_SIZE * sizeof(uint8_t));
	// memcpy(spare, tnand[flat_idx].spare, PAGE_SPARE_SIZE * sizeof(uint8_t));

	return NAND_SUCCESS;
}

int tnand_erase(int bank, int blk)
{
	int flag_bk, flag_bl, flag_em; 
	flag_bk = flag_bl = flag_em = 0;
	size_t flat_b_idx = (bank * (PAGES_PER_BANK)) + (blk * (NPAGES)); // block idx
	size_t flat_idx = 0;

	if(bank < 0 || bank >= NBANKS) flag_bk++;
	if(blk < 0 || blk >= NBLKS) flag_bl++;
	if(flag_bk || flag_bl) return NAND_ERR_INVALID;

	for(int i = 0; i < NPAGES; i++) {
		flat_idx = flat_b_idx + i;
		flag_em += is_w[flat_idx];
		is_w[flat_idx] = 0;
	}
	if(!flag_em) return NAND_ERR_EMPTY;

	return NAND_SUCCESS;
}
/*** Translation Flash Space ***/

/*** Free T Block List (FIFO Queue) ***/
Queuetype* create_queue(void)
{
	return (Queuetype*)malloc(sizeof(Queuetype));
}

void init_queue(Queuetype* h)
{
	h->cap = BLOCK_LIST_SIZE + 1;
	h->queue = (int*)malloc(sizeof(int) * h->cap);
	h->head = 0;
	h->tail = 0;
	h->q_size = 0;
}

int is_full(const Queuetype* h)
{
	return h->q_size == (h->cap - 1);
}

int is_empty(const Queuetype* h)
{
	return h->q_size == 0;
}

void enqueue(Queuetype* h, int item)
{
	if (is_full(h)) {
		fprintf(stderr, "queue is full!\n");
		return;
	}
	h->queue[h->tail] = item;
	h->tail = (h->tail + 1) % h->cap;
	h->q_size++;
}

int dequeue(Queuetype* h)
{
	if (is_empty(h)) {
		fprintf(stderr, "queue is empty!\n");
		return INVALID_PPN;
	}
	int item = h->queue[h->head];
	h->head = (h->head + 1) % h->cap;
	h->q_size--;
	return item;
}

Heaptype* create_heap(void)
{
	return (Heaptype*)malloc(sizeof(Heaptype));
}

void init_heap(Heaptype* h)
{
	h->heap_size = 0;
}

void insert_minheap(Heaptype* h, int item)
{
	int i;
	i = ++(h->heap_size);

	while((i != 1) && (item < h->heap[i / 2])) {
		h->heap[i] = h->heap[i / 2];
		i /= 2;
	}
	h->heap[i] = item;
}

int delete_minheap(Heaptype* h)
{
	if(!h->heap_size) {
		printf("heap is empty!");
		return INVALID_PPN;
	}

	int parent, child;
	int item, tmp;

	item = h->heap[1];
	tmp = h->heap[(h->heap_size)--];
	parent = 1;
	child = 2;

	while(child <= h->heap_size) {
		if((child < h->heap_size) && (h->heap[child] > h->heap[child+1])) {
			child++;
		}
		if(tmp <= h->heap[child]) break;

		h->heap[parent] = h->heap[child];
		parent = child;
		child *= 2;
	}
	h->heap[parent] = tmp;
	return item;
}

Queuetype* fblk_list;   // free block for Write
Heaptype* ablk_list;    // active block for GC victim
BNUM tblk_curr;         // 현재 할당된 T Block number
int blk_invalid[BLOCK_LIST_SIZE];  // 각 T Block 별 invalid page 수
/*** Free T Block List (FIFO Queue) ***/

/*** cmt LRU 리스트 관련 함수 ***/
void cmt_lru_list_init(cmt_lru_list *list) 
{
    list->head = NULL;
    list->tail = NULL;
}

void cmt_lru_list_remove(cmt_lru_list *list, struct cmt_entry *entry) 
{
    if (entry->lru_prev) {
        // entry가 head가 아닌 경우
        entry->lru_prev->lru_next = entry->lru_next;
    } else {
        // entry가 head인 경우: head를 다음 노드로 업데이트
        list->head = entry->lru_next;
    }

    if (entry->lru_next) {
        // entry가 tail이 아닌 경우
        entry->lru_next->lru_prev = entry->lru_prev;
    } else {
        // entry가 tail인 경우: tail을 이전 노드로 업데이트
        list->tail = entry->lru_prev;
    }

    // 제거된 노드의 포인터는 NULL로 정리 (안전성)
    entry->lru_prev = NULL;
    entry->lru_next = NULL;
}

void cmt_lru_list_add_to_front(cmt_lru_list *list, struct cmt_entry *entry) 
{ // most recent accessed
    entry->lru_next = list->head; // 새 노드의 next는 현재 head
    entry->lru_prev = NULL;       // 새 노드는 head가 되므로 prev는 NULL

    if (list->head) {
        list->head->lru_prev = entry; // 기존 head의 prev를 새 노드로
    }
    list->head = entry; // 리스트의 head를 새 노드로 업데이트

    if (list->tail == NULL) {
        // 리스트가 비어있었다면 tail도 새 노드로 설정
        list->tail = entry;
    }
}

void cmt_lru_list_move_to_front(cmt_lru_list *list, struct cmt_entry *entry) 
{
    if (list->head == entry) {
        // 이미 head(MRU)에 있으므로 아무것도 하지 않음
        return;
    }
    
    // 1. 리스트에서 먼저 제거
    cmt_lru_list_remove(list, entry);
    // 2. 리스트의 맨 앞에 다시 추가
    cmt_lru_list_add_to_front(list, entry);
}

// ctp LRU 리스트 관련 함수
void ctp_lru_list_init(ctp_lru_list *list) 
{
    list->head = NULL;
    list->tail = NULL;
}

void ctp_lru_list_remove(ctp_lru_list *list, struct ctp_entry *entry) 
{
    if (entry->lru_prev) {
        // entry가 head가 아닌 경우
        entry->lru_prev->lru_next = entry->lru_next;
    } else {
        // entry가 head인 경우: head를 다음 노드로 업데이트
        list->head = entry->lru_next;
    }

    if (entry->lru_next) {
        // entry가 tail이 아닌 경우
        entry->lru_next->lru_prev = entry->lru_prev;
    } else {
        // entry가 tail인 경우: tail을 이전 노드로 업데이트
        list->tail = entry->lru_prev;
    }

    // 제거된 노드의 포인터는 NULL로 정리
    entry->lru_prev = NULL;
    entry->lru_next = NULL;
}

void ctp_lru_list_add_to_front(ctp_lru_list *list, struct ctp_entry *entry) 
{
    entry->lru_next = list->head; // 새 노드의 next는 현재 head
    entry->lru_prev = NULL;       // 새 노드는 head가 되므로 prev는 NULL

    if (list->head) {
        list->head->lru_prev = entry; // 기존 head의 prev를 새 노드로
    }
    list->head = entry; // 리스트의 head를 새 노드로 업데이트

    if (list->tail == NULL) {
        // 리스트가 비어있었다면 tail도 새 노드로 설정
        list->tail = entry;
    }
}

void ctp_lru_list_move_to_front(ctp_lru_list *list, struct ctp_entry *entry) 
{
    if (list->head == entry) {
        // 이미 head(MRU)에 있으므로 아무것도 하지 않음
        return;
    }
    
    // 1. 리스트에서 먼저 제거
    ctp_lru_list_remove(list, entry);
    // 2. 리스트의 맨 앞에 다시 추가
    ctp_lru_list_add_to_front(list, entry);
}
/*** cmt LRU 리스트 관련 함수 ***/

/*** gtd, cmt, ctp manipulate 함수 ***/
struct cmt_entry* cmt_find_entry(uint64_t dlpn)
{
    int hash_key = dlpn % NUM_CMT_BUCKETS;


    struct cmt_entry* ptr = cmt[hash_key].cmt_entries;
    while(ptr != NULL && ptr->data.dlpn != dlpn) {
        ptr = ptr->next;
    }

    return ptr;
}

struct ctp_entry* ctp_find_entry(uint64_t tvpn)
{
    int hash_key = tvpn % NUM_CTP_BUCKETS;


    struct ctp_entry* ptr = ctp[hash_key].ctp_entries;
    while(ptr != NULL && ptr->tvpn != tvpn) {
        ptr = ptr->next;
    }

    return ptr;
}

void tinit(void)
{
    gtd_init();
    cmt_init();
    ctp_init();
}

void gtd_init(void)
{ // initialize gtd and tp2l
    for(int i = 0; i < MAX_TVPN; i++) {
        gtd[i].tppn.ppa = INVALID_PPN; 
        gtd[i].location = true;
        gtd[i].dirty = false;
    }

    for(int i = 0; i < MAX_TPPN; i++) {
        tp2l[i] = INVALID_PPN;
    }
}

void cmt_init(void)
{
    for(int i = 0; i < NUM_CMT_BUCKETS; i++) {
        cmt[i].hash_value = i;
        cmt[i].cmt_entries = NULL;
        cmt[i].hash_next = (i != NUM_CMT_BUCKETS-1) ? &cmt[i+1] : NULL;
    }

    cmt_lru_list_init(&cmt_lru);
    cmtn = 0;
}

void ctp_init(void)
{
    for(int i = 0; i < NUM_CTP_BUCKETS; i++) {
        ctp[i].hash_value = i;
        ctp[i].ctp_entries = NULL;
        ctp[i].hash_next = (i != NUM_CTP_BUCKETS-1) ? &ctp[i+1] : NULL;
    }

    ctp_lru_list_init(&ctp_lru);
    ctpn = 0;
}

struct cmt_entry* cmt_creat_entry(void)
{
    struct cmt_entry* new_entry = (struct cmt_entry*)malloc(sizeof(struct cmt_entry));
    
    new_entry->data.dlpn = INVALID_PPN;
    new_entry->data.dppn.ppa = INVALID_PPN;
    new_entry->data.dirty = false;

    new_entry->prev = NULL;
    new_entry->next = NULL; 
    new_entry->lru_prev = NULL; 
    new_entry->lru_next = NULL;

    return new_entry;
}

struct ctp_entry* ctp_creat_entry(void)
{
    struct ctp_entry* new_entry = (struct ctp_entry*)malloc(sizeof(struct ctp_entry));
    new_entry->tvpn = INVALID_PPN;
    new_entry->mp = NULL;
    new_entry->tppn.ppa = INVALID_PPN;
    new_entry->prev = NULL;
    new_entry->next = NULL; 
    new_entry->lru_prev = NULL; 
    new_entry->lru_next = NULL;

    return new_entry;
}

void cmt_insert_entry(struct cmt_entry *new_entry)
{
    int hash_key = new_entry->data.dlpn % NUM_CMT_BUCKETS;

    // 해시 테이블에 삽입
    new_entry->next = cmt[hash_key].cmt_entries;
    if (cmt[hash_key].cmt_entries != NULL) {
        cmt[hash_key].cmt_entries->prev = new_entry;
    }
    cmt[hash_key].cmt_entries = new_entry;
    new_entry->prev = NULL;

    // LRU 리스트에 삽입
    cmt_lru_list_add_to_front(&cmt_lru, new_entry);
    cmtn++;
}

void ctp_insert_entry(struct ctp_entry *new_entry)
{
    int hash_key = new_entry->tvpn % NUM_CTP_BUCKETS;

    // 해시 테이블에 삽입
    new_entry->next = ctp[hash_key].ctp_entries;
    if (ctp[hash_key].ctp_entries != NULL) {
        ctp[hash_key].ctp_entries->prev = new_entry;
    }
    ctp[hash_key].ctp_entries = new_entry;
    new_entry->prev = NULL;

    // LRU 리스트에 삽입
    ctp_lru_list_add_to_front(&ctp_lru, new_entry);
    ctpn++;
}

void cmt_remove_entry(struct cmt_entry *entry)
{
    int hash_key = entry->data.dlpn % NUM_CMT_BUCKETS;

    // 해시 테이블에서 제거
    if (entry->prev != NULL) {
        entry->prev->next = entry->next;
    } else {
        cmt[hash_key].cmt_entries = entry->next;
    }
    if (entry->next != NULL) {
        entry->next->prev = entry->prev;
    }

    // LRU 리스트에서 제거
    cmt_lru_list_remove(&cmt_lru, entry);

    free(entry);
    cmtn--;
}

void ctp_remove_entry(struct ctp_entry *entry)
{
    int hash_key = entry->tvpn % NUM_CTP_BUCKETS;

    // 해시 테이블에서 제거
    if (entry->prev != NULL) {
        entry->prev->next = entry->next;
    } else {
        ctp[hash_key].ctp_entries = entry->next;
    }
    if (entry->next != NULL) {
        entry->next->prev = entry->prev;
    }

    // LRU 리스트에서 제거
    ctp_lru_list_remove(&ctp_lru, entry);

    free(entry->mp->dppn);
    free(entry->mp);
    free(entry);
    ctpn--;
}

int is_cache_full(void)
{   
    uint64_t total_curr_bytes = (cmtn * (PAGE_DATA_SIZE / NUM_MAPPINGS_PER_PAGE)) + (ctpn * PAGE_DATA_SIZE);
    uint64_t max_bytes = (MAX_CMTN * (PAGE_DATA_SIZE / NUM_MAPPINGS_PER_PAGE)) + MAX_CTPN * PAGE_DATA_SIZE;
    uint64_t add_bytes = (PAGE_DATA_SIZE / NUM_MAPPINGS_PER_PAGE) + PAGE_DATA_SIZE;
    return (total_curr_bytes + add_bytes > max_bytes);
}

int is_ctp_full(void)
{   
    return ctpn >= MAX_CTPN;
}

int select_victim_greedy(void)
{ // delete victim from alist, and return bnum of victim
	int max_criteria = -1;
	int target;
	int vdx = -1;

	int tmp[BLOCK_LIST_SIZE];
	int tdx = 0;
	while(ablk_list->heap_size) {
		tmp[tdx] = delete_minheap(ablk_list);

		if (tmp[tdx] == tblk_curr.bnum) {
			tdx++;
			continue;
		}

		target = blk_invalid[tmp[tdx]];
		if(max_criteria < target) {
			vdx = tdx;
			max_criteria = target;
		}
		tdx++;
	}
	for(int i = 0; i < tdx; i++) {
		if(i == vdx) continue;
		insert_minheap(ablk_list, tmp[i]);
	}

	if (vdx == -1) {
		printf("Not found victim\n");
		return INVALID_PPN;
	}
	return tmp[vdx];
}

void map_garbage_collection(void)
{
    int victim = select_victim_greedy();
	if(victim == INVALID_PPN) {
		printf("No victim found for GC\n");
		return;
	}

	uint64_t ppn_base = victim*NPAGES;
	uint64_t tvpn, tppn, old_tppn; // lpn은 mapping gc일 경우 mvpn으로 쓰임
	uint8_t data[PAGE_DATA_SIZE];

	for(int i = 0; i < NPAGES; i++) {
		old_tppn = ppn_base+i;
		tvpn = tp2l[old_tppn];
		if(tvpn == INVALID_PPN || gtd[tvpn].tppn.ppa != old_tppn) continue;

		// valid -> copy
        // case 1: cached (cmt, ctp)
        struct ctp_entry* ctp_curr = ctp_find_entry(tvpn);
        int flag = 0;

        if(ctp_curr != NULL && gtd[tvpn].dirty) {
            memcpy(data, ctp_curr->mp->dppn, PAGE_DATA_SIZE);
            flag = 1;
        } else tnand_read(0, victim, i, data);

        uint64_t* data_ptr = (uint64_t*)data;
        for(int j = 0; j < NUM_MAPPINGS_PER_PAGE; j++) {
            uint64_t dvpn = tvpn*NUM_MAPPINGS_PER_PAGE + j;
            // uint64_t dppn = data_ptr[j];
            struct cmt_entry* cmt_curr = cmt_find_entry(dvpn);
            if(cmt_curr != NULL && cmt_curr->data.dirty) {
                data_ptr[j] = cmt_curr->data.dppn.ppa;
                cmt_curr->data.dirty = false;
                if (flag == 1) {
                    femu_log("[ERROR] map gc error! cmt and ctp both dirty bit set\n");
                    ftl_assert(0);       
                }
            }
        }

        // case 2: not cached
		int blk = tblk_curr.bnum;
		int page = tblk_curr.p_cur++;
		int chk = tnand_write(0, blk, page, data);
		if(chk) printf("write in gc error! : %d\n", chk);

		tppn = blk*NPAGES + page;
		gtd[tvpn].tppn.ppa = tppn; // location 수정 x
        gtd[tvpn].dirty = false;
		tp2l[tppn] = tvpn;
		tp2l[old_tppn] = INVALID_PPN;
	}

	int chk = tnand_erase(0, victim);
	if(chk) printf("\nerase error!\n");
	blk_invalid[victim] = 0;
	enqueue(fblk_list, victim);

	return;
}

void cmt_evict_entry(void)
{ // evict one entry from CMT
    struct cmt_entry* victim = cmt_lru.tail;
    if(victim == NULL) {
        // femu_log("cmt_evict_entry victim is NULL\n");
        // femu_log("CMT Entry Number : %ld\n", cmtn);
        // femu_log("CTP Entry Number : %ld\n", ctpn);
        ctp_evict_entry();
        return;
    }

    struct ctp_entry* victim_ctp_entry = NULL;
    uint64_t victim_dlpn = victim->data.dlpn;
    uint64_t victim_tvpn = victim_dlpn / NUM_MAPPINGS_PER_PAGE;

    if((victim_ctp_entry = ctp_find_entry(victim_tvpn)) != NULL) { // Flush back victim to CTP
        victim_ctp_entry->mp->dppn[victim_dlpn % NUM_MAPPINGS_PER_PAGE] = victim->data.dppn;
        if(victim->data.dirty) {
            gtd[victim_tvpn].dirty = true;
            femu_log("[Error] dirty CMT flush to CTP1\n");
            ftl_assert(0);
        }
    } else if(victim->data.dirty) { // Flush to nand
        if(tblk_curr.p_cur >= NPAGES) {
            tblk_curr = (BNUM){dequeue(fblk_list), 0};
            insert_minheap(ablk_list, tblk_curr.bnum);

            if (fblk_list->q_size < 1) { // map gc
                map_garbage_collection();
            }
        }

        uint64_t victim_tppn = gtd[victim_tvpn].tppn.ppa;
        uint8_t* mapping_page = malloc(PAGE_DATA_SIZE);
        if(victim_tppn == INVALID_PPN) {    // 처음 접근하는 tvpn인 경우
            memset(mapping_page, 0xFF, PAGE_DATA_SIZE);
        } else {                            // 이미 nand에 존재하는 tvpn인 경우 
            tnand_read(0, victim_tppn / NPAGES, victim_tppn % NPAGES, (void*)mapping_page);
            tp2l[victim_tppn] = INVALID_PPN;
        }

        uint64_t blk = tblk_curr.bnum;
        uint64_t page = tblk_curr.p_cur++;
        uint64_t new_tppn = (blk * NPAGES) + page;
        
        uint64_t* m = (uint64_t*)mapping_page;
        m[victim_dlpn % NUM_MAPPINGS_PER_PAGE] = victim->data.dppn.ppa;
        tnand_write(0, blk, page, (void*)mapping_page);
        free(mapping_page);

        gtd[victim_tvpn].tppn.ppa = new_tppn;
        gtd[victim_tvpn].location = true;
        gtd[victim_tvpn].dirty = false;
        tp2l[new_tppn] = victim_tvpn;
    }
    // femu_log("Before removing CMT entry dlpn: %lu\n", victim->data.dlpn);
    cmt_remove_entry(victim); // Erase victim from CMT
}

void ctp_evict_entry(void)
{ // evict one entry from CTP
    struct ctp_entry* victim = ctp_lru.tail;
    if(victim == NULL) {
        femu_log("[ERROR] ctp_evict_entry victim is NULL\n");
        ftl_assert(0);
        return;
    }
    uint64_t victim_tvpn = victim->tvpn;
    uint64_t victim_tppn = victim->tppn.ppa;

    if(gtd[victim_tvpn].dirty) { // Flush to nand
        if(tblk_curr.p_cur >= NPAGES) {
            tblk_curr = (BNUM){dequeue(fblk_list), 0};
            insert_minheap(ablk_list, tblk_curr.bnum);

            if (fblk_list->q_size < 1) { // map gc
                map_garbage_collection();
            }
        }

        uint64_t blk = tblk_curr.bnum;
        uint64_t page = tblk_curr.p_cur++;
        uint64_t new_tppn = (blk * NPAGES) + page;
        
        // femu_log("tnand_write\n");
        tnand_write(0, blk, page, (void*)victim->mp->dppn);
        gtd[victim_tvpn].tppn.ppa = new_tppn;
        gtd[victim_tvpn].location = true;
        gtd[victim_tvpn].dirty = false;
        if(victim_tppn != INVALID_PPN) tp2l[victim_tppn] = INVALID_PPN;
        tp2l[new_tppn] = victim_tvpn;
    }
    ctp_remove_entry(victim); // Erase victim from CTP
}

int cached_num(void) {
    struct cmt_entry* lru_ptr = cmt_lru.head;
    int entry_num = 0; // number of mapping which is in CTP and CMT
    while(lru_ptr) {
        uint64_t tvpn = lru_ptr->data.dlpn / NUM_MAPPINGS_PER_PAGE;
        if(ctp_find_entry(tvpn)) entry_num++;
        lru_ptr = lru_ptr->lru_next;
    }

    return entry_num;
}

void fetch_in(uint64_t dlpn)
{ // Hyunil : fetch mapping and translation page into CMT and CTP together
    if(is_cache_full()) {
        // femu_log("Cache Full! fetch_in\n");
        cmt_evict_entry();                  // evict one entry from CMT for CMT fetch
        // femu_log("After CMT Evict fetch_in\n");

        if(cached_num() >= NUM_MAPPINGS_PER_PAGE) { // evict N entries from CMT for CTP fetch
            // femu_log("Evict N entries from CMT for CTP fetch_in\n");
            struct cmt_entry* lru_ptr = cmt_lru.tail;
            for(int i = 0; i < NUM_MAPPINGS_PER_PAGE; i++) {
                uint64_t lru_tvpn = lru_ptr->data.dlpn / NUM_MAPPINGS_PER_PAGE;
                struct ctp_entry* lru_ctp_entry = ctp_find_entry(lru_tvpn);
                struct cmt_entry* tmp = lru_ptr->lru_prev;
                if(lru_ctp_entry) {
                    lru_ctp_entry->mp->dppn[lru_ptr->data.dlpn % NUM_MAPPINGS_PER_PAGE] = lru_ptr->data.dppn;
                    if(lru_ptr->data.dirty) {
                        gtd[lru_tvpn].dirty = true;
                        // femu_log("[Error] dirty CMT flush to CTP2\n");
                        // ftl_assert(0);
                    }
                    cmt_remove_entry(lru_ptr);
                }              
                lru_ptr = tmp;
            }
        } else {                            // evict one entry from CTP for CTP fetch
            // femu_log("Evict one entry from CTP for CTP fetch_in\n");
            ctp_evict_entry();
        }
    }
    
    // Fetch mapping and tranlsation page into CMT and CTP
    uint64_t dlpn_off = dlpn % NUM_MAPPINGS_PER_PAGE;
    uint64_t tvpn = dlpn / NUM_MAPPINGS_PER_PAGE;
    uint64_t tppn = gtd[tvpn].tppn.ppa;
    struct ctp_entry* ctp_curr = ctp_creat_entry();
    // femu_log("Created CTP entry fetch_in\n");

    ctp_curr->tvpn = tvpn;
    ctp_curr->mp = malloc(sizeof(struct map_page));
    ctp_curr->mp->dppn = malloc(sizeof(struct ppa) * NUM_MAPPINGS_PER_PAGE);
    ctp_curr->tppn.ppa = tppn;
    if(tppn == INVALID_PPN) {   // 처음 접근하는 tvpn인 경우
        // femu_log("Before memset fetch_in\n");
        memset(ctp_curr->mp->dppn, 0xFF, PAGE_DATA_SIZE);
    } else {                    // 이미 nand에 존재하는 tvpn인 경우 
        // femu_log("Before Read CTP entry fetch_in\n");
        tnand_read(0, tppn / NPAGES, tppn % NPAGES, (void*)ctp_curr->mp->dppn);
        // femu_log("Read CTP entry from NAND fetch_in\n");
    }
    
    struct cmt_entry* cmt_curr = cmt_creat_entry();
    cmt_curr->data = (struct data){dlpn, ctp_curr->mp->dppn[dlpn_off], false};

    // femu_log("Inserting CMT and CTP entry fetch_in\n");
    cmt_insert_entry(cmt_curr); // fetch (dlpn, dppn) into CMT

    // femu_log("Inserting CTP entry fetch_in\n");
    ctp_insert_entry(ctp_curr); // fetch T_demand into CTP
    // femu_log("After Inserted CTP entry fetch_in\n");

    gtd[tvpn].location = false; // Update GTD (location)
}

void ctp_fetch_in(uint64_t dlpn)
{
    if(is_ctp_full()) {        
        if(cached_num() >= NUM_MAPPINGS_PER_PAGE) { // evict N entries from CMT for CTP fetch
            struct cmt_entry* lru_ptr = cmt_lru.tail;
            for(int i = 0; i < NUM_MAPPINGS_PER_PAGE; i++) {
                uint64_t lru_tvpn = lru_ptr->data.dlpn / NUM_MAPPINGS_PER_PAGE;
                struct ctp_entry* lru_ctp_entry = ctp_find_entry(lru_tvpn);
                struct cmt_entry* tmp = lru_ptr->lru_prev;
                if(lru_ctp_entry) {
                    lru_ctp_entry->mp->dppn[lru_ptr->data.dlpn % NUM_MAPPINGS_PER_PAGE] = lru_ptr->data.dppn;
                    if(lru_ptr->data.dirty) {
                        gtd[lru_tvpn].dirty = true;
                        // femu_log("[Error] dirty CMT flush to CTP3\n");
                        // ftl_assert(0);
                    }
                    cmt_remove_entry(lru_ptr);
                }
                lru_ptr = tmp;
            }
        } else {                            // evict one entry from CTP for CTP fetch
            ctp_evict_entry();
        }
    }
    
    // Fetch mapping and tranlsation page into CTP
    uint64_t tvpn = dlpn / NUM_MAPPINGS_PER_PAGE;
    uint64_t tppn = gtd[tvpn].tppn.ppa;
    struct ctp_entry* ctp_curr = ctp_creat_entry();

    ctp_curr->tvpn = tvpn;
    ctp_curr->mp = malloc(sizeof(struct map_page));
    ctp_curr->mp->dppn = malloc(sizeof(struct ppa) * NUM_MAPPINGS_PER_PAGE);
    ctp_curr->tppn.ppa = tppn;
    if(tppn == INVALID_PPN) {   // 처음 접근하는 tvpn인 경우
        memset(ctp_curr->mp->dppn, 0xFF, PAGE_DATA_SIZE);
    } else {                    // 이미 nand에 존재하는 tvpn인 경우 
        tnand_read(0, tppn / NPAGES, tppn % NPAGES, (void*)ctp_curr->mp->dppn);
    }
    
    ctp_insert_entry(ctp_curr); // fetch T_demand into CTP
    gtd[tvpn].location = false; // Update GTD (location)
}

void replace(uint64_t dlpn, uint64_t dppn)
{ // Donghyun : replace mapping entry in CMT/CTP with (dlpn, dppn)
    uint64_t tvpn = dlpn / NUM_MAPPINGS_PER_PAGE;
    uint64_t dlpn_off = dlpn % NUM_MAPPINGS_PER_PAGE;
    struct ctp_entry* ctp_curr = ctp_find_entry(tvpn);
    struct cmt_entry* cmt_curr = cmt_find_entry(dlpn);

    if (ctp_curr != NULL) {     // CTP Hit
        // femu_log("CTP Hit Replace!\n");
        ctp_curr->mp->dppn[dlpn_off].ppa = dppn;
        ctp_lru_list_move_to_front(&ctp_lru, ctp_curr); // ?

        if (cmt_curr != NULL) { // CMT Hit
            // femu_log("CTP Hit  && CMT Hit Replace!\n");
            cmt_remove_entry(cmt_curr);
        }

        gtd[tvpn].dirty = true; // Update GTD (dirty)
    } else {                    // CTP Miss        
        if (cmt_curr != NULL) { // CMT Hit
            // femu_log("CTP Miss && CMT Hit Replace!\n");
            cmt_curr->data.dppn.ppa = dppn;
            cmt_curr->data.dirty = true;
            cmt_lru_list_move_to_front(&cmt_lru, cmt_curr); // ?
        } else {                // CMT Miss
            // femu_log("CTP Miss && CMT Miss Replace!\n");
            ctp_fetch_in(dlpn);
            ctp_curr = ctp_find_entry(tvpn);

            if (ctp_curr == NULL) {
            // femu_log("CTP entry fetch failed!\n");
            }
            ctp_curr->mp->dppn[dlpn_off].ppa = dppn;
            ctp_lru_list_move_to_front(&ctp_lru, ctp_curr); // ?

            gtd[tvpn].dirty = true; // Update GTD (dirty)
        }
    }
}
/*** gtd, cmt, ctp manipulate 함수 ***/

#define FEMU_DEBUG_FTL

static void *ftl_thread(void *arg);

static inline bool should_gc(struct ssd *ssd)
{
    return (ssd->lm.free_line_cnt <= ssd->sp.gc_thres_lines);
}

static inline bool should_gc_high(struct ssd *ssd)
{
    return (ssd->lm.free_line_cnt <= ssd->sp.gc_thres_lines_high);
}

static inline struct ppa get_maptbl_ent(struct ssd *ssd, uint64_t lpn)
{
    // return ssd->maptbl[lpn];

    uint64_t tvpn = lpn / NUM_MAPPINGS_PER_PAGE;
    struct ppa dppn;
    struct ctp_entry* ctp_curr = ctp_find_entry(tvpn);
    if(ctp_curr != NULL) {
        // femu_log("map table fetch CTP hit!\n");
        dppn = ctp_curr->mp->dppn[lpn % NUM_MAPPINGS_PER_PAGE];
        // if(dppn.ppa == 139866079756432) {
        //     dppn.ppa = -1;
        // }
        if(ssd->maptbl[lpn].ppa != dppn.ppa) {
            femu_log("[CTP HIT] map table fetch [ERROR]! lpn: %lu, maptbl: %lu, fetched: %lu\n", lpn, ssd->maptbl[lpn].ppa, dppn.ppa);
            ftl_assert(0);
        }
        return dppn;
    }
    
    struct cmt_entry* cmt_curr = cmt_find_entry(lpn);
    if(cmt_curr != NULL) {
        // femu_log("map table fetch CMT hit!\n");
        dppn = cmt_curr->data.dppn;
        // if(dppn.ppa == 139866079756432) {
        //     dppn.ppa = -1;
        // }
        if(ssd->maptbl[lpn].ppa != dppn.ppa) {
            femu_log("[CMT HIT] map table fetch [ERROR]! lpn: %lu, maptbl: %lu, fetched: %lu\n", lpn, ssd->maptbl[lpn].ppa, dppn.ppa);
            ftl_assert(0);
        }
        return dppn;
    }

    // femu_log("[Get Maptbl] map table fetch miss!\n");
    fetch_in(lpn);


    // check
    dppn = get_maptbl_ent(ssd, lpn);
    // if(dppn.ppa == 139866079756432) {
    //     dppn.ppa = -1;
    // }
    if(ssd->maptbl[lpn].ppa != dppn.ppa) {
        femu_log("[ERROR] map table fetch error! lpn: %lu, maptbl: %lu, fetched: %lu\n", lpn, ssd->maptbl[lpn].ppa, dppn.ppa);
        ftl_assert(0);
    } else {
        // femu_log("[SUCCESS] map table fetch success! lpn: %lu, maptbl: %lu, fetched: %lu\n", lpn, ssd->maptbl[lpn].ppa, dppn.ppa);
    }

    return dppn;
}

static inline void set_maptbl_ent(struct ssd *ssd, uint64_t lpn, struct ppa *ppa)
{
    ftl_assert(lpn < ssd->sp.tt_pgs);
    ssd->maptbl[lpn] = *ppa;

    // replace, fetch_in
    replace(lpn, ppa->ppa);
}

static inline void set_maptbl_datagc(struct ssd *ssd, uint64_t lpn, struct ppa *ppa)
{
    ftl_assert(lpn < ssd->sp.tt_pgs);
    ssd->maptbl[lpn] = *ppa;

    // replace, fetch_in
    uint64_t tvpn = lpn / NUM_MAPPINGS_PER_PAGE;
    struct cmt_entry* cmt_curr = cmt_find_entry(lpn);
    if(cmt_curr != NULL) {
        cmt_curr->data.dppn.ppa = ppa->ppa;
        cmt_curr->data.dirty = true;
    } else {
        struct ctp_entry* ctp_curr = ctp_find_entry(tvpn);
        if(ctp_curr != NULL) {
            ctp_curr->mp->dppn[lpn % NUM_MAPPINGS_PER_PAGE].ppa = ppa->ppa;
            gtd[tvpn].dirty = true;
        } else {
            if(tblk_curr.p_cur >= NPAGES) {
                tblk_curr = (BNUM){dequeue(fblk_list), 0};
                insert_minheap(ablk_list, tblk_curr.bnum);

                if (fblk_list->q_size < 1) { // map gc
                    map_garbage_collection();
                }
            }

            uint64_t victim_tppn = gtd[tvpn].tppn.ppa;
            uint8_t* mapping_page = malloc(PAGE_DATA_SIZE);

            if(victim_tppn == INVALID_PPN) {    // 처음 접근하는 tvpn인 경우
                memset(mapping_page, 0xFF, PAGE_DATA_SIZE);
                femu_log("[Error] mapping dose not exist in anywhere datagc\n");
                ftl_assert(0);
            } else {                            // 이미 nand에 존재하는 tvpn인 경우 
                tnand_read(0, victim_tppn / NPAGES, victim_tppn % NPAGES, (void*)mapping_page);
                tp2l[victim_tppn] = INVALID_PPN;
            }

            uint64_t blk = tblk_curr.bnum;
            uint64_t page = tblk_curr.p_cur++;
            uint64_t new_tppn = (blk * NPAGES) + page;
            
            uint64_t* m = (uint64_t*)mapping_page;
            m[lpn % NUM_MAPPINGS_PER_PAGE] = ppa->ppa;
            tnand_write(0, blk, page, (void*)mapping_page);
            free(mapping_page);

            gtd[tvpn].tppn.ppa = new_tppn;
            gtd[tvpn].location = true;
            gtd[tvpn].dirty = false;
            tp2l[new_tppn] = tvpn;
        }
    }
}

static uint64_t ppa2pgidx(struct ssd *ssd, struct ppa *ppa)
{
    struct ssdparams *spp = &ssd->sp;
    uint64_t pgidx;

    pgidx = ppa->g.ch  * spp->pgs_per_ch  + \
            ppa->g.lun * spp->pgs_per_lun + \
            ppa->g.pl  * spp->pgs_per_pl  + \
            ppa->g.blk * spp->pgs_per_blk + \
            ppa->g.pg;

    ftl_assert(pgidx < spp->tt_pgs);

    return pgidx;
}

static inline uint64_t get_rmap_ent(struct ssd *ssd, struct ppa *ppa)
{
    uint64_t pgidx = ppa2pgidx(ssd, ppa);

    return ssd->rmap[pgidx];
}

/* set rmap[page_no(ppa)] -> lpn */
static inline void set_rmap_ent(struct ssd *ssd, uint64_t lpn, struct ppa *ppa)
{
    uint64_t pgidx = ppa2pgidx(ssd, ppa);

    ssd->rmap[pgidx] = lpn;
}

static inline int victim_line_cmp_pri(pqueue_pri_t next, pqueue_pri_t curr)
{
    return (next > curr);
}

static inline pqueue_pri_t victim_line_get_pri(void *a)
{
    return ((struct line *)a)->vpc;
}

static inline void victim_line_set_pri(void *a, pqueue_pri_t pri)
{
    ((struct line *)a)->vpc = pri;
}

static inline size_t victim_line_get_pos(void *a)
{
    return ((struct line *)a)->pos;
}

static inline void victim_line_set_pos(void *a, size_t pos)
{
    ((struct line *)a)->pos = pos;
}

static void ssd_init_lines(struct ssd *ssd)
{
    struct ssdparams *spp = &ssd->sp;
    struct line_mgmt *lm = &ssd->lm;
    struct line *line;

    lm->tt_lines = spp->blks_per_pl;
    ftl_assert(lm->tt_lines == spp->tt_lines);
    lm->lines = g_malloc0(sizeof(struct line) * lm->tt_lines);

    QTAILQ_INIT(&lm->free_line_list);
    lm->victim_line_pq = pqueue_init(spp->tt_lines, victim_line_cmp_pri,
            victim_line_get_pri, victim_line_set_pri,
            victim_line_get_pos, victim_line_set_pos);
    QTAILQ_INIT(&lm->full_line_list);

    lm->free_line_cnt = 0;
    for (int i = 0; i < lm->tt_lines; i++) {
        line = &lm->lines[i];
        line->id = i;
        line->ipc = 0;
        line->vpc = 0;
        line->pos = 0;
        /* initialize all the lines as free lines */
        QTAILQ_INSERT_TAIL(&lm->free_line_list, line, entry);
        lm->free_line_cnt++;
    }

    ftl_assert(lm->free_line_cnt == lm->tt_lines);
    lm->victim_line_cnt = 0;
    lm->full_line_cnt = 0;
}

static void ssd_init_write_pointer(struct ssd *ssd)
{
    struct write_pointer *wpp = &ssd->wp;
    struct line_mgmt *lm = &ssd->lm;
    struct line *curline = NULL;

    curline = QTAILQ_FIRST(&lm->free_line_list);
    QTAILQ_REMOVE(&lm->free_line_list, curline, entry);
    lm->free_line_cnt--;

    /* wpp->curline is always our next-to-write super-block */
    wpp->curline = curline;
    wpp->ch = 0;
    wpp->lun = 0;
    wpp->pg = 0;
    wpp->blk = 0;
    wpp->pl = 0;
}

static inline void check_addr(int a, int max)
{
    ftl_assert(a >= 0 && a < max);
}

static struct line *get_next_free_line(struct ssd *ssd)
{
    struct line_mgmt *lm = &ssd->lm;
    struct line *curline = NULL;

    curline = QTAILQ_FIRST(&lm->free_line_list);
    if (!curline) {
        ftl_err("No free lines left in [%s] !!!!\n", ssd->ssdname);
        return NULL;
    }

    QTAILQ_REMOVE(&lm->free_line_list, curline, entry);
    lm->free_line_cnt--;
    return curline;
}

static void ssd_advance_write_pointer(struct ssd *ssd)
{
    struct ssdparams *spp = &ssd->sp;
    struct write_pointer *wpp = &ssd->wp;
    struct line_mgmt *lm = &ssd->lm;

    check_addr(wpp->ch, spp->nchs);
    wpp->ch++;
    if (wpp->ch == spp->nchs) {
        wpp->ch = 0;
        check_addr(wpp->lun, spp->luns_per_ch);
        wpp->lun++;
        /* in this case, we should go to next lun */
        if (wpp->lun == spp->luns_per_ch) {
            wpp->lun = 0;
            /* go to next page in the block */
            check_addr(wpp->pg, spp->pgs_per_blk);
            wpp->pg++;
            if (wpp->pg == spp->pgs_per_blk) {
                wpp->pg = 0;
                /* move current line to {victim,full} line list */
                if (wpp->curline->vpc == spp->pgs_per_line) {
                    /* all pgs are still valid, move to full line list */
                    ftl_assert(wpp->curline->ipc == 0);
                    QTAILQ_INSERT_TAIL(&lm->full_line_list, wpp->curline, entry);
                    lm->full_line_cnt++;
                } else {
                    ftl_assert(wpp->curline->vpc >= 0 && wpp->curline->vpc < spp->pgs_per_line);
                    /* there must be some invalid pages in this line */
                    ftl_assert(wpp->curline->ipc > 0);
                    pqueue_insert(lm->victim_line_pq, wpp->curline);
                    lm->victim_line_cnt++;
                }
                /* current line is used up, pick another empty line */
                check_addr(wpp->blk, spp->blks_per_pl);
                wpp->curline = NULL;
                wpp->curline = get_next_free_line(ssd);
                if (!wpp->curline) {
                    /* TODO */
                    abort();
                }
                wpp->blk = wpp->curline->id;
                check_addr(wpp->blk, spp->blks_per_pl);
                /* make sure we are starting from page 0 in the super block */
                ftl_assert(wpp->pg == 0);
                ftl_assert(wpp->lun == 0);
                ftl_assert(wpp->ch == 0);
                /* TODO: assume # of pl_per_lun is 1, fix later */
                ftl_assert(wpp->pl == 0);
            }
        }
    }
}

static struct ppa get_new_page(struct ssd *ssd)
{
    struct write_pointer *wpp = &ssd->wp;
    struct ppa ppa;
    ppa.ppa = 0;
    ppa.g.ch = wpp->ch;
    ppa.g.lun = wpp->lun;
    ppa.g.pg = wpp->pg;
    ppa.g.blk = wpp->blk;
    ppa.g.pl = wpp->pl;
    ftl_assert(ppa.g.pl == 0);

    return ppa;
}

static void check_params(struct ssdparams *spp)
{
    /*
     * we are using a general write pointer increment method now, no need to
     * force luns_per_ch and nchs to be power of 2
     */

    //ftl_assert(is_power_of_2(spp->luns_per_ch));
    //ftl_assert(is_power_of_2(spp->nchs));
}

static void ssd_init_params(struct ssdparams *spp, FemuCtrl *n)
{
    spp->secsz = n->bb_params.secsz; // 512
    spp->secs_per_pg = n->bb_params.secs_per_pg; // 8
    spp->pgs_per_blk = n->bb_params.pgs_per_blk; //256
    spp->blks_per_pl = n->bb_params.blks_per_pl; /* 256 16GB */
    spp->pls_per_lun = n->bb_params.pls_per_lun; // 1
    spp->luns_per_ch = n->bb_params.luns_per_ch; // 8
    spp->nchs = n->bb_params.nchs; // 8

    spp->pg_rd_lat = n->bb_params.pg_rd_lat;
    spp->pg_wr_lat = n->bb_params.pg_wr_lat;
    spp->blk_er_lat = n->bb_params.blk_er_lat;
    spp->ch_xfer_lat = n->bb_params.ch_xfer_lat;

    /* calculated values */
    spp->secs_per_blk = spp->secs_per_pg * spp->pgs_per_blk;
    spp->secs_per_pl = spp->secs_per_blk * spp->blks_per_pl;
    spp->secs_per_lun = spp->secs_per_pl * spp->pls_per_lun;
    spp->secs_per_ch = spp->secs_per_lun * spp->luns_per_ch;
    spp->tt_secs = spp->secs_per_ch * spp->nchs;

    spp->pgs_per_pl = spp->pgs_per_blk * spp->blks_per_pl;
    spp->pgs_per_lun = spp->pgs_per_pl * spp->pls_per_lun;
    spp->pgs_per_ch = spp->pgs_per_lun * spp->luns_per_ch;
    spp->tt_pgs = spp->pgs_per_ch * spp->nchs;

    spp->blks_per_lun = spp->blks_per_pl * spp->pls_per_lun;
    spp->blks_per_ch = spp->blks_per_lun * spp->luns_per_ch;
    spp->tt_blks = spp->blks_per_ch * spp->nchs;

    spp->pls_per_ch =  spp->pls_per_lun * spp->luns_per_ch;
    spp->tt_pls = spp->pls_per_ch * spp->nchs;

    spp->tt_luns = spp->luns_per_ch * spp->nchs;

    /* line is special, put it at the end */
    spp->blks_per_line = spp->tt_luns; /* TODO: to fix under multiplanes */
    spp->pgs_per_line = spp->blks_per_line * spp->pgs_per_blk;
    spp->secs_per_line = spp->pgs_per_line * spp->secs_per_pg;
    spp->tt_lines = spp->blks_per_lun; /* TODO: to fix under multiplanes */

    spp->gc_thres_pcent = n->bb_params.gc_thres_pcent/100.0;
    spp->gc_thres_lines = (int)((1 - spp->gc_thres_pcent) * spp->tt_lines);
    spp->gc_thres_pcent_high = n->bb_params.gc_thres_pcent_high/100.0;
    spp->gc_thres_lines_high = (int)((1 - spp->gc_thres_pcent_high) * spp->tt_lines);
    spp->enable_gc_delay = true;


    check_params(spp);
}

static void ssd_init_nand_page(struct nand_page *pg, struct ssdparams *spp)
{
    pg->nsecs = spp->secs_per_pg;
    pg->sec = g_malloc0(sizeof(nand_sec_status_t) * pg->nsecs);
    for (int i = 0; i < pg->nsecs; i++) {
        pg->sec[i] = SEC_FREE;
    }
    pg->status = PG_FREE;
}

static void ssd_init_nand_blk(struct nand_block *blk, struct ssdparams *spp)
{
    blk->npgs = spp->pgs_per_blk;
    blk->pg = g_malloc0(sizeof(struct nand_page) * blk->npgs);
    for (int i = 0; i < blk->npgs; i++) {
        ssd_init_nand_page(&blk->pg[i], spp);
    }
    blk->ipc = 0;
    blk->vpc = 0;
    blk->erase_cnt = 0;
    blk->wp = 0;
}

static void ssd_init_nand_plane(struct nand_plane *pl, struct ssdparams *spp)
{
    pl->nblks = spp->blks_per_pl;
    pl->blk = g_malloc0(sizeof(struct nand_block) * pl->nblks);
    for (int i = 0; i < pl->nblks; i++) {
        ssd_init_nand_blk(&pl->blk[i], spp);
    }
}

static void ssd_init_nand_lun(struct nand_lun *lun, struct ssdparams *spp)
{
    lun->npls = spp->pls_per_lun;
    lun->pl = g_malloc0(sizeof(struct nand_plane) * lun->npls);
    for (int i = 0; i < lun->npls; i++) {
        ssd_init_nand_plane(&lun->pl[i], spp);
    }
    lun->next_lun_avail_time = 0;
    lun->busy = false;
}

static void ssd_init_ch(struct ssd_channel *ch, struct ssdparams *spp)
{
    ch->nluns = spp->luns_per_ch;
    ch->lun = g_malloc0(sizeof(struct nand_lun) * ch->nluns);
    for (int i = 0; i < ch->nluns; i++) {
        ssd_init_nand_lun(&ch->lun[i], spp);
    }
    ch->next_ch_avail_time = 0;
    ch->busy = 0;
}

static void ssd_init_maptbl(struct ssd *ssd)
{
    struct ssdparams *spp = &ssd->sp;

    ssd->maptbl = g_malloc0(sizeof(struct ppa) * spp->tt_pgs);
    for (int i = 0; i < spp->tt_pgs; i++) {
        ssd->maptbl[i].ppa = UNMAPPED_PPA;
    }
}

static void ssd_init_rmap(struct ssd *ssd)
{
    struct ssdparams *spp = &ssd->sp;

    ssd->rmap = g_malloc0(sizeof(uint64_t) * spp->tt_pgs);
    for (int i = 0; i < spp->tt_pgs; i++) {
        ssd->rmap[i] = INVALID_LPN;
    }
}

void ssd_init(FemuCtrl *n)
{
    struct ssd *ssd = n->ssd;
    struct ssdparams *spp = &ssd->sp;

    ftl_assert(ssd);

    ssd_init_params(spp, n);

    /* initialize ssd internal layout architecture */
    ssd->ch = g_malloc0(sizeof(struct ssd_channel) * spp->nchs);
    for (int i = 0; i < spp->nchs; i++) {
        ssd_init_ch(&ssd->ch[i], spp);
    }

    /* initialize maptbl */
    ssd_init_maptbl(ssd);

    /* initialize rmap */
    ssd_init_rmap(ssd);

    /* initialize all the lines */
    ssd_init_lines(ssd);

    /* initialize write pointer, this is how we allocate new pages for writes */
    ssd_init_write_pointer(ssd);

    qemu_thread_create(&ssd->ftl_thread, "FEMU-FTL-Thread", ftl_thread, n,
                       QEMU_THREAD_JOINABLE);

    // FEMU Intro & Add Command
    ssd->host_writes = 0;
    ssd->gc_writes = 0;

    // FEMU CDFTL
    // Translation Space Allocation
    spp->tspace_size = 4096 * 16 * spp->pgs_per_blk; // 4096B * 16 blocks * pages_per_block
    tnand_init(1, 16, spp->pgs_per_blk);

    ablk_list = create_heap(); // Active Mapping Block List (Min-Heap)
    init_heap(ablk_list);
    fblk_list = create_queue(); // Free Translation Block List (FIFO)
    init_queue(fblk_list);
    for(int j = 0; j < 16; j++) {
        enqueue(fblk_list, j);
        blk_invalid[j] = 0;
	}
    tblk_curr = (BNUM){dequeue(fblk_list), 0}; // Current Translation Block
    insert_minheap(ablk_list, tblk_curr.bnum);

    // Translation Metadata Allocation
    tinit();
}

static inline bool valid_ppa(struct ssd *ssd, struct ppa *ppa)
{
    struct ssdparams *spp = &ssd->sp;
    int ch = ppa->g.ch;
    int lun = ppa->g.lun;
    int pl = ppa->g.pl;
    int blk = ppa->g.blk;
    int pg = ppa->g.pg;
    int sec = ppa->g.sec;

    if (ch >= 0 && ch < spp->nchs && lun >= 0 && lun < spp->luns_per_ch && pl >=
        0 && pl < spp->pls_per_lun && blk >= 0 && blk < spp->blks_per_pl && pg
        >= 0 && pg < spp->pgs_per_blk && sec >= 0 && sec < spp->secs_per_pg)
        return true;

    return false;
}

static inline bool valid_lpn(struct ssd *ssd, uint64_t lpn)
{
    return (lpn < ssd->sp.tt_pgs);
}

static inline bool mapped_ppa(struct ppa *ppa)
{
    return !(ppa->ppa == UNMAPPED_PPA);
}

static inline struct ssd_channel *get_ch(struct ssd *ssd, struct ppa *ppa)
{
    return &(ssd->ch[ppa->g.ch]);
}

static inline struct nand_lun *get_lun(struct ssd *ssd, struct ppa *ppa)
{
    struct ssd_channel *ch = get_ch(ssd, ppa);
    return &(ch->lun[ppa->g.lun]);
}

static inline struct nand_plane *get_pl(struct ssd *ssd, struct ppa *ppa)
{
    struct nand_lun *lun = get_lun(ssd, ppa);
    return &(lun->pl[ppa->g.pl]);
}

static inline struct nand_block *get_blk(struct ssd *ssd, struct ppa *ppa)
{
    struct nand_plane *pl = get_pl(ssd, ppa);
    return &(pl->blk[ppa->g.blk]);
}

static inline struct line *get_line(struct ssd *ssd, struct ppa *ppa)
{
    return &(ssd->lm.lines[ppa->g.blk]);
}

static inline struct nand_page *get_pg(struct ssd *ssd, struct ppa *ppa)
{
    struct nand_block *blk = get_blk(ssd, ppa);
    return &(blk->pg[ppa->g.pg]);
}

static uint64_t ssd_advance_status(struct ssd *ssd, struct ppa *ppa, struct
        nand_cmd *ncmd)
{
    int c = ncmd->cmd;
    uint64_t cmd_stime = (ncmd->stime == 0) ? \
        qemu_clock_get_ns(QEMU_CLOCK_REALTIME) : ncmd->stime;
    uint64_t nand_stime;
    struct ssdparams *spp = &ssd->sp;
    struct nand_lun *lun = get_lun(ssd, ppa);
    uint64_t lat = 0;

    switch (c) {
    case NAND_READ:
        /* read: perform NAND cmd first */
        nand_stime = (lun->next_lun_avail_time < cmd_stime) ? cmd_stime : \
                     lun->next_lun_avail_time;
        lun->next_lun_avail_time = nand_stime + spp->pg_rd_lat;
        lat = lun->next_lun_avail_time - cmd_stime;
#if 0
        lun->next_lun_avail_time = nand_stime + spp->pg_rd_lat;

        /* read: then data transfer through channel */
        chnl_stime = (ch->next_ch_avail_time < lun->next_lun_avail_time) ? \
            lun->next_lun_avail_time : ch->next_ch_avail_time;
        ch->next_ch_avail_time = chnl_stime + spp->ch_xfer_lat;

        lat = ch->next_ch_avail_time - cmd_stime;
#endif
        break;

    case NAND_WRITE:
        /* write: transfer data through channel first */
        nand_stime = (lun->next_lun_avail_time < cmd_stime) ? cmd_stime : \
                     lun->next_lun_avail_time;
        if (ncmd->type == USER_IO) {
            lun->next_lun_avail_time = nand_stime + spp->pg_wr_lat;
        } else {
            lun->next_lun_avail_time = nand_stime + spp->pg_wr_lat;
        }
        lat = lun->next_lun_avail_time - cmd_stime;

#if 0
        chnl_stime = (ch->next_ch_avail_time < cmd_stime) ? cmd_stime : \
                     ch->next_ch_avail_time;
        ch->next_ch_avail_time = chnl_stime + spp->ch_xfer_lat;

        /* write: then do NAND program */
        nand_stime = (lun->next_lun_avail_time < ch->next_ch_avail_time) ? \
            ch->next_ch_avail_time : lun->next_lun_avail_time;
        lun->next_lun_avail_time = nand_stime + spp->pg_wr_lat;

        lat = lun->next_lun_avail_time - cmd_stime;
#endif
        break;

    case NAND_ERASE:
        /* erase: only need to advance NAND status */
        nand_stime = (lun->next_lun_avail_time < cmd_stime) ? cmd_stime : \
                     lun->next_lun_avail_time;
        lun->next_lun_avail_time = nand_stime + spp->blk_er_lat;

        lat = lun->next_lun_avail_time - cmd_stime;
        break;

    default:
        ftl_err("Unsupported NAND command: 0x%x\n", c);
    }

    return lat;
}

/* update SSD status about one page from PG_VALID -> PG_INVALID */
static void mark_page_invalid(struct ssd *ssd, struct ppa *ppa)
{
    struct line_mgmt *lm = &ssd->lm;
    struct ssdparams *spp = &ssd->sp;
    struct nand_block *blk = NULL;
    struct nand_page *pg = NULL;
    bool was_full_line = false;
    struct line *line;

    /* update corresponding page status */
    pg = get_pg(ssd, ppa);
    ftl_assert(pg->status == PG_VALID);
    pg->status = PG_INVALID;

    /* update corresponding block status */
    blk = get_blk(ssd, ppa);
    ftl_assert(blk->ipc >= 0 && blk->ipc < spp->pgs_per_blk);
    blk->ipc++;
    ftl_assert(blk->vpc > 0 && blk->vpc <= spp->pgs_per_blk);
    blk->vpc--;

    /* update corresponding line status */
    line = get_line(ssd, ppa);
    ftl_assert(line->ipc >= 0 && line->ipc < spp->pgs_per_line);
    if (line->vpc == spp->pgs_per_line) {
        ftl_assert(line->ipc == 0);
        was_full_line = true;
    }
    line->ipc++;
    ftl_assert(line->vpc > 0 && line->vpc <= spp->pgs_per_line);
    /* Adjust the position of the victime line in the pq under over-writes */
    if (line->pos) {
        /* Note that line->vpc will be updated by this call */
        pqueue_change_priority(lm->victim_line_pq, line->vpc - 1, line);
    } else {
        line->vpc--;
    }

    if (was_full_line) {
        /* move line: "full" -> "victim" */
        QTAILQ_REMOVE(&lm->full_line_list, line, entry);
        lm->full_line_cnt--;
        pqueue_insert(lm->victim_line_pq, line);
        lm->victim_line_cnt++;
    }
}

static void mark_page_valid(struct ssd *ssd, struct ppa *ppa)
{
    struct nand_block *blk = NULL;
    struct nand_page *pg = NULL;
    struct line *line;

    /* update page status */
    pg = get_pg(ssd, ppa);
    ftl_assert(pg->status == PG_FREE);
    pg->status = PG_VALID;

    /* update corresponding block status */
    blk = get_blk(ssd, ppa);
    ftl_assert(blk->vpc >= 0 && blk->vpc < ssd->sp.pgs_per_blk);
    blk->vpc++;

    /* update corresponding line status */
    line = get_line(ssd, ppa);
    ftl_assert(line->vpc >= 0 && line->vpc < ssd->sp.pgs_per_line);
    line->vpc++;
}

static void mark_block_free(struct ssd *ssd, struct ppa *ppa)
{
    struct ssdparams *spp = &ssd->sp;
    struct nand_block *blk = get_blk(ssd, ppa);
    struct nand_page *pg = NULL;

    for (int i = 0; i < spp->pgs_per_blk; i++) {
        /* reset page status */
        pg = &blk->pg[i];
        ftl_assert(pg->nsecs == spp->secs_per_pg);
        pg->status = PG_FREE;
    }

    /* reset block status */
    ftl_assert(blk->npgs == spp->pgs_per_blk);
    blk->ipc = 0;
    blk->vpc = 0;
    blk->erase_cnt++;
}

static void gc_read_page(struct ssd *ssd, struct ppa *ppa)
{
    /* advance ssd status, we don't care about how long it takes */
    if (ssd->sp.enable_gc_delay) {
        struct nand_cmd gcr;
        gcr.type = GC_IO;
        gcr.cmd = NAND_READ;
        gcr.stime = 0;
        ssd_advance_status(ssd, ppa, &gcr);
    }
}

/* move valid page data (already in DRAM) from victim line to a new page */
static uint64_t gc_write_page(struct ssd *ssd, struct ppa *old_ppa)
{
    struct ppa new_ppa;
    struct nand_lun *new_lun;
    uint64_t lpn = get_rmap_ent(ssd, old_ppa);

    ftl_assert(valid_lpn(ssd, lpn));
    new_ppa = get_new_page(ssd);
    /* update maptbl */
    // set_maptbl_ent(ssd, lpn, &new_ppa);
    femu_log("[Data GC valid copy mapping] LPN %lu: PPA 0x%lx -> 0x%lx\n", lpn, old_ppa->ppa, new_ppa.ppa);
    set_maptbl_datagc(ssd, lpn, &new_ppa);
    struct ppa tmp = get_maptbl_ent(ssd,lpn);
    femu_log("[Data GC valid copy mapping] LPN: %lu, get: 0x%lx, correct: 0x%lx\n", lpn, tmp.ppa, new_ppa.ppa);
    /* update rmap */
    set_rmap_ent(ssd, lpn, &new_ppa);

    mark_page_valid(ssd, &new_ppa);

    /* need to advance the write pointer here */
    ssd_advance_write_pointer(ssd);

    if (ssd->sp.enable_gc_delay) {
        struct nand_cmd gcw;
        gcw.type = GC_IO;
        gcw.cmd = NAND_WRITE;
        gcw.stime = 0;
        ssd_advance_status(ssd, &new_ppa, &gcw);
    }

    /* advance per-ch gc_endtime as well */
#if 0
    new_ch = get_ch(ssd, &new_ppa);
    new_ch->gc_endtime = new_ch->next_ch_avail_time;
#endif

    new_lun = get_lun(ssd, &new_ppa);
    new_lun->gc_endtime = new_lun->next_lun_avail_time;

    return 0;
}

static struct line *select_victim_line(struct ssd *ssd, bool force)
{
    struct line_mgmt *lm = &ssd->lm;
    struct line *victim_line = NULL;

    victim_line = pqueue_peek(lm->victim_line_pq);
    if (!victim_line) {
        return NULL;
    }

    if (!force && victim_line->ipc < ssd->sp.pgs_per_line / 8) {
        return NULL;
    }

    pqueue_pop(lm->victim_line_pq);
    victim_line->pos = 0;
    lm->victim_line_cnt--;

    /* victim_line is a danggling node now */
    return victim_line;
}

/* here ppa identifies the block we want to clean */
static void clean_one_block(struct ssd *ssd, struct ppa *ppa)
{
    // femu_log("one block copy triggered!\n");

    struct ssdparams *spp = &ssd->sp;
    struct nand_page *pg_iter = NULL;
    int cnt = 0;

    for (int pg = 0; pg < spp->pgs_per_blk; pg++) {
        ppa->g.pg = pg;
        pg_iter = get_pg(ssd, ppa);
        /* there shouldn't be any free page in victim blocks */
        ftl_assert(pg_iter->status != PG_FREE);
        if (pg_iter->status == PG_VALID) {
            gc_read_page(ssd, ppa);
            /* delay the maptbl update until "write" happens */
            gc_write_page(ssd, ppa);
            // FEMU Intro & Add Command
            ssd->gc_writes++;
            cnt++;
        }
    }

    ftl_assert(get_blk(ssd, ppa)->vpc == cnt);
}

static void mark_line_free(struct ssd *ssd, struct ppa *ppa)
{
    struct line_mgmt *lm = &ssd->lm;
    struct line *line = get_line(ssd, ppa);
    line->ipc = 0;
    line->vpc = 0;
    /* move this line to free line list */
    QTAILQ_INSERT_TAIL(&lm->free_line_list, line, entry);
    lm->free_line_cnt++;
}

static int do_gc(struct ssd *ssd, bool force)
{
    struct line *victim_line = NULL;
    struct ssdparams *spp = &ssd->sp;
    struct nand_lun *lunp;
    struct ppa ppa;
    int ch, lun;

    victim_line = select_victim_line(ssd, force);
    if (!victim_line) {
        return -1;
    }

    ppa.g.blk = victim_line->id;
    ftl_debug("GC-ing line:%d,ipc=%d,victim=%d,full=%d,free=%d\n", ppa.g.blk,
              victim_line->ipc, ssd->lm.victim_line_cnt, ssd->lm.full_line_cnt,
              ssd->lm.free_line_cnt);

    /* copy back valid data */
    for (ch = 0; ch < spp->nchs; ch++) {
        for (lun = 0; lun < spp->luns_per_ch; lun++) {
            ppa.g.ch = ch;
            ppa.g.lun = lun;
            ppa.g.pl = 0;
            lunp = get_lun(ssd, &ppa);
            clean_one_block(ssd, &ppa);
            mark_block_free(ssd, &ppa);

            if (spp->enable_gc_delay) {
                struct nand_cmd gce;
                gce.type = GC_IO;
                gce.cmd = NAND_ERASE;
                gce.stime = 0;
                ssd_advance_status(ssd, &ppa, &gce);
            }

            lunp->gc_endtime = lunp->next_lun_avail_time;
        }
    }

    /* update line status */
    mark_line_free(ssd, &ppa);

    return 0;
}

static uint64_t ssd_read(struct ssd *ssd, NvmeRequest *req)
{
    struct ssdparams *spp = &ssd->sp;
    uint64_t lba = req->slba;
    int nsecs = req->nlb;
    struct ppa ppa;
    uint64_t start_lpn = lba / spp->secs_per_pg;
    uint64_t end_lpn = (lba + nsecs - 1) / spp->secs_per_pg;
    uint64_t lpn;
    uint64_t sublat, maxlat = 0;

    if (end_lpn >= spp->tt_pgs) {
        ftl_err("start_lpn=%"PRIu64",tt_pgs=%d\n", start_lpn, ssd->sp.tt_pgs);
    }

    /* normal IO read path */
    for (lpn = start_lpn; lpn <= end_lpn; lpn++) {
        ppa = get_maptbl_ent(ssd, lpn);
        if (!mapped_ppa(&ppa) || !valid_ppa(ssd, &ppa)) {
            //printf("%s,lpn(%" PRId64 ") not mapped to valid ppa\n", ssd->ssdname, lpn);
            //printf("Invalid ppa,ch:%d,lun:%d,blk:%d,pl:%d,pg:%d,sec:%d\n",
            //ppa.g.ch, ppa.g.lun, ppa.g.blk, ppa.g.pl, ppa.g.pg, ppa.g.sec);
            continue;
        }

        struct nand_cmd srd;
        srd.type = USER_IO;
        srd.cmd = NAND_READ;
        srd.stime = req->stime;
        sublat = ssd_advance_status(ssd, &ppa, &srd);
        maxlat = (sublat > maxlat) ? sublat : maxlat;
    }

    return maxlat;
}

static uint64_t ssd_write(struct ssd *ssd, NvmeRequest *req)
{
    uint64_t lba = req->slba;
    struct ssdparams *spp = &ssd->sp;
    int len = req->nlb;
    uint64_t start_lpn = lba / spp->secs_per_pg;
    uint64_t end_lpn = (lba + len - 1) / spp->secs_per_pg;
    struct ppa ppa;
    uint64_t lpn;
    uint64_t curlat = 0, maxlat = 0;
    int r;

    if (end_lpn >= spp->tt_pgs) {
        ftl_err("start_lpn=%"PRIu64",tt_pgs=%d\n", start_lpn, ssd->sp.tt_pgs);
    }

    while (should_gc_high(ssd)) {
        /* perform GC here until !should_gc(ssd) */
        r = do_gc(ssd, true);
        if (r == -1)
            break;
    }

    for (lpn = start_lpn; lpn <= end_lpn; lpn++) {
        ppa = get_maptbl_ent(ssd, lpn);
        if (mapped_ppa(&ppa)) {
            /* update old page information first */
            mark_page_invalid(ssd, &ppa);
            set_rmap_ent(ssd, INVALID_LPN, &ppa);
        }

        /* new write */
        ppa = get_new_page(ssd);
        /* update maptbl */
        set_maptbl_ent(ssd, lpn, &ppa);
        /* update rmap */
        set_rmap_ent(ssd, lpn, &ppa);

        mark_page_valid(ssd, &ppa);

        /* need to advance the write pointer here */
        ssd_advance_write_pointer(ssd);

        struct nand_cmd swr;
        swr.type = USER_IO;
        swr.cmd = NAND_WRITE;
        swr.stime = req->stime;
        /* get latency statistics */
        curlat = ssd_advance_status(ssd, &ppa, &swr);
        maxlat = (curlat > maxlat) ? curlat : maxlat;

        // FEMU Intro & Add Command
        ssd->host_writes++;
    }

    return maxlat;
}

static uint64_t ssd_trim(struct ssd *ssd, NvmeRequest *req)
{
    struct ssdparams *spp = &ssd->sp;
    NvmeDsmRange *ranges = req->dsm_ranges;
    int nr_ranges = req->dsm_nr_ranges;
    // uint32_t attributes = req->dsm_attributes;
    
    int total_trimmed_pages = 0;
    int total_already_invalid = 0;
    int total_out_of_bounds = 0;
    
    if (!ranges || nr_ranges <= 0) {
        printf("TRIM: Invalid ranges or count\n");
        return 0;
    }
    
    // printf("TRIM: Processing %d ranges (attributes=0x%x)\n", nr_ranges, attributes);
    
    for (int range_idx = 0; range_idx < nr_ranges; range_idx++) {
        uint64_t slba = le64_to_cpu(ranges[range_idx].slba);
        uint32_t nlb = le32_to_cpu(ranges[range_idx].nlb);
        // uint32_t cattr = le32_to_cpu(ranges[range_idx].cattr);
        
        uint64_t start_lpn = slba / spp->secs_per_pg;
        uint64_t end_lpn = (slba + nlb - 1) / spp->secs_per_pg;
        uint64_t lpn;
        struct ppa ppa;
        int trimmed_pages = 0;
        int already_invalid = 0;

        // ftl_debug("TRIM Range %d: LBA %lu + %u sectors, LPN range %lu-%lu (%lu pages), cattr=0x%x\n", 
        //        range_idx, slba, nlb, start_lpn, end_lpn, end_lpn - start_lpn + 1, cattr);

        // Boundary check
        if (end_lpn >= spp->tt_pgs) {
            ftl_err("TRIM: Range %d exceeds FTL capacity - end_lpn=%lu, tt_pgs=%d\n", 
                   range_idx, end_lpn, spp->tt_pgs);
            total_out_of_bounds++;
            continue;  // Skip this range, continue with others
        }

        // Process each LPN in this range
        for (lpn = start_lpn; lpn <= end_lpn; lpn++) {
            ppa = get_maptbl_ent(ssd, lpn);
            
            // Skip already unmapped/invalid pages
            if (!mapped_ppa(&ppa) || !valid_ppa(ssd, &ppa)) {
                already_invalid++;
                continue;
            }

            // Invalidate the existing mapped page
            mark_page_invalid(ssd, &ppa);
            
            // Clear reverse mapping
            set_rmap_ent(ssd, INVALID_LPN, &ppa);
            
            // Set mapping table entry as unmapped
            ppa.ppa = UNMAPPED_PPA;
            set_maptbl_ent(ssd, lpn, &ppa);
            
            trimmed_pages++;
        }
        
        total_trimmed_pages += trimmed_pages;
        total_already_invalid += already_invalid;
        
        // ftl_debug("TRIM Range %d: %d pages trimmed, %d already invalid\n", 
        //        range_idx, trimmed_pages, already_invalid);
    }

    // ftl_debug("TRIM: Completed - %d pages trimmed, %d already invalid, %d out of bounds across %d ranges\n", 
    //        total_trimmed_pages, total_already_invalid, total_out_of_bounds, nr_ranges);

    // Free the ranges array
    g_free(ranges);
    req->dsm_ranges = NULL;
    req->dsm_nr_ranges = 0;
    req->dsm_attributes = 0;

    return 0;  // Assume TRIM operations have no NAND latency
}

static void *ftl_thread(void *arg)
{ //  FTL thread (FEMU Intro slide 11 page)
    FemuCtrl *n = (FemuCtrl *)arg;
    struct ssd *ssd = n->ssd;
    NvmeRequest *req = NULL;
    uint64_t lat = 0;
    int rc;
    int i;

    while (!*(ssd->dataplane_started_ptr)) {
        usleep(100000);
    }

    /* FIXME: not safe, to handle ->to_ftl and ->to_poller gracefully */
    ssd->to_ftl = n->to_ftl;
    ssd->to_poller = n->to_poller;

    while (1) {
        for (i = 1; i <= n->nr_pollers; i++) {
            if (!ssd->to_ftl[i] || !femu_ring_count(ssd->to_ftl[i]))
                continue;

            rc = femu_ring_dequeue(ssd->to_ftl[i], (void *)&req, 1); // femu ring
            if (rc != 1) {
                printf("FEMU: FTL to_ftl dequeue failed\n");
            }

            ftl_assert(req);
            switch (req->cmd.opcode) {
            case NVME_CMD_WRITE:
                lat = ssd_write(ssd, req);
                break;
            case NVME_CMD_READ:
                lat = ssd_read(ssd, req);
                break;
            case NVME_CMD_DSM:
                if (req->dsm_ranges && req->dsm_nr_ranges > 0) {
                    lat = ssd_trim(ssd, req);
                }
                break;
            default:
                //ftl_err("FTL received unkown request type, ERROR\n");
                ;
            }

            req->reqlat = lat;
            req->expire_time += lat;

            rc = femu_ring_enqueue(ssd->to_poller[i], (void *)&req, 1); // cq
            if (rc != 1) {
                ftl_err("FTL to_poller enqueue failed\n");
            }

            /* clean one line if needed (in the background) */
            if (should_gc(ssd)) {
                do_gc(ssd, false);
            }
        }
    }

    return NULL;
}
