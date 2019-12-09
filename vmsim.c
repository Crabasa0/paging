// =================================================================================================================================
/**
 * vmsim.c
 *
 * Allocate space that is then virtually mapped, page by page, to a simulated underlying space.  Maintain page tables and follow
 * their mappings with a simulated MMU.
 **/
// =================================================================================================================================



// =================================================================================================================================
// INCLUDES

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include "bs.h"
#include "mmu.h"
#include "vmsim.h"
// =================================================================================================================================



// =================================================================================================================================
// CONSTANTS AND MACRO FUNCTIONS

#define KB(n)      (n * 1024)
#define MB(n)      (KB(n) * 1024)
#define GB(n)      (MB(n) * 1024)
 
#define DEFAULT_REAL_MEMORY_SIZE   (MB(4) + KB(16)) //WAS MB(5)
#define PAGESIZE                   KB(4)
#define PT_AREA_SIZE               (MB(4) + KB(4))

#define OFFSET_MASK           (PAGESIZE - 1)
#define PAGE_NUMBER_MASK      (~OFFSET_MASK)
#define GET_UPPER_INDEX(addr) ((addr >> 22) & 0x3ff)
#define GET_LOWER_INDEX(addr) ((addr >> 12) & 0x3ff)
#define GET_OFFSET(addr)      (addr & OFFSET_MASK)
#define GET_PAGE_ADDR(addr)   (addr & PAGE_NUMBER_MASK)
#define IS_ALIGNED(addr)      ((addr & OFFSET_MASK) == 0)

#define IS_RESIDENT(pte)      (pte & PTE_RESIDENT_BIT)
#define IS_REFERENCED(pte)    (pte & PTE_REFERENCED_BIT)
#define IS_DIRTY(pte)         (pte & PTE_DIRTY_BIT)
#define SET_RESIDENT(pte)     (pte |= PTE_RESIDENT_BIT)
#define CLEAR_RESIDENT(pte)   (pte &= ~PTE_RESIDENT_BIT)
#define CLEAR_REFERENCED(pte) (pte &= ~PTE_REFERENCED_BIT)
#define CLEAR_DIRTY(pte)      (pte &= ~PTE_DIRTY_BIT)

// The boundaries and size of the real memory region.
static void*        real_base      = NULL;
static void*        real_limit     = NULL;
static uint64_t     real_size      = DEFAULT_REAL_MEMORY_SIZE;

// Where to find the next page of real memory for page table blocks.
static vmsim_addr_t pt_free_addr   = PAGESIZE;

// Where to find the next page of real memory for backing simulated pages.
static vmsim_addr_t real_free_addr = PT_AREA_SIZE;

// The base real address of the upper page table.
static vmsim_addr_t upper_pt       = 0;

// Used by the heap allocator, the address of the next free simulated address.
static vmsim_addr_t sim_free_addr  = 0;

// The highest available block number on bs
static unsigned int block_no 	   = 1;

// The array of lpt entries, used in the CLOCK algorithm
static uint64_t ENTRIES_LENGTH = (DEFAULT_REAL_MEMORY_SIZE - PT_AREA_SIZE) / PAGESIZE;
static pt_entry_t** entries = NULL;
static uint64_t cur_page_no = 0;

// The index of the first unused real page in MM, used to initialize entries in "entries"
//static uint64_t page_no = 0;

//DEBUG: store last created pte
static pt_entry_t* last_pte = 0x0;

//DEBUG: store if we have overflowed onto bs
static bool overflowed = false;
// =================================================================================================================================

// =============
//Declare my functions because this is C
vmsim_addr_t move_to_bs(pt_entry_t* lpt_entry);
void move_to_mm(pt_entry_t lpt_entry, vmsim_addr_t real_addr);
void swap(vmsim_addr_t in, pt_entry_t* out);
pt_entry_t* search();
uint64_t get_page_no(vmsim_addr_t real_addr);
void show_entries();
vmsim_addr_t get_real_address(pt_entry_t* lpte_pt);
// =============

// =================================================================================================================================
/**
 * Allocate a page of real memory space for a page table block.  Taken from a region of real memory reserved for this purpose.
 *
 * \return The _real_ base address of a page of memory for a page table block.
 */
vmsim_addr_t
allocate_pt () {

  vmsim_addr_t new_pt_addr = pt_free_addr;
  pt_free_addr += PAGESIZE;
  assert(IS_ALIGNED(new_pt_addr));
  assert(pt_free_addr <= PT_AREA_SIZE);
  void* new_pt_ptr = (void*)(real_base + new_pt_addr);
  memset(new_pt_ptr, 0, PAGESIZE);
  
  return new_pt_addr;
  
} // allocate_pt ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * Allocate a page of real memory space for backing a simulated page.  Taken from the general pool of real memory.
 *
 * \return The _real_ base address of a page of memory.
 */
vmsim_addr_t
allocate_real_page () {

  vmsim_addr_t new_real_addr = real_free_addr;
  real_free_addr += PAGESIZE;
  assert(IS_ALIGNED(new_real_addr));
  //assert(real_free_addr <= real_size); //TODO: change me!
  if (real_free_addr > real_size){    //out of space?
    if(!overflowed){//DEBUG: tell me if we have overflowed onto BS
      overflowed = true;
      //show_entries();
    }
    pt_entry_t* to_bs = search();      //find the lpt entry for a NRU page
    vmsim_addr_t real_page_addr = move_to_bs(to_bs);     //move that entry's contents to BS and give the newly freed page.
    return real_page_addr;            //return the address of the freed page.
  }
    
  void* new_real_ptr = (void*)(real_base + new_real_addr);
  memset(new_real_ptr, 0, PAGESIZE);

  return new_real_addr;
  
} // allocate_real_page ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_init () {

  // Only initialize if it hasn't already happened.
  if (real_base == NULL) {

    // Determine the real memory size, preferrably by environment variable, otherwise use the default.
    char* real_size_envvar = getenv("VMSIM_REAL_MEM_SIZE");
    if (real_size_envvar != NULL) {
      errno = 0;
      real_size = strtoul(real_size_envvar, NULL, 10);
      assert(errno == 0);
    }

    // Map the real storage space.
    real_base = mmap(NULL, real_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    assert(real_base != NULL);
    real_limit = (void*)((intptr_t)real_base + real_size);
    upper_pt = allocate_pt();

    // Initialize the simualted space allocator.  Leave page 0 unused, start at page 1.
    sim_free_addr = PAGESIZE;

    // Initialize the supporting components.
    mmu_init(upper_pt);
    bs_init();

    // Initialize the lpt entry array.
    ENTRIES_LENGTH = (real_size - PT_AREA_SIZE) / PAGESIZE;
    entries = malloc(sizeof(vmsim_addr_t) * ENTRIES_LENGTH);
    
  }
  
} // vmsim_init ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * Map a _simulated_ address to a _real_ one, ensuring first that the page table and real spaces are initialized.
 *
 * \param  sim_addr        The _simulated_ address to translate.
 * \param  write_operation Whether the memory access is to _read_ (`false`) or to _write_ (`true`).
 * \return the translated _real_ address.
 */ 
vmsim_addr_t
vmsim_map (vmsim_addr_t sim_addr, bool write_operation) {

  vmsim_init();

  assert(real_base != NULL);
  vmsim_addr_t real_addr = mmu_translate(sim_addr, write_operation);
  return real_addr;
  
} // vmsim_map ()
// =================================================================================================================================



// =================================================================================================================================
/**
 * Called when the translation of a _simulated_ address fails.  When this function is done, a _real_ page will back the _simulated_
 * one that contains the given address, with the page tables appropriately updated.
 *
 * \param sim_addr The _simulated_ address for which address translation failed.
 */
void
vmsim_map_fault (vmsim_addr_t sim_addr) {

  assert(upper_pt != 0);

  // Grab the upper table's entry.
  vmsim_addr_t upper_index    = GET_UPPER_INDEX(sim_addr);
  vmsim_addr_t upper_pte_addr = upper_pt + (upper_index * sizeof(pt_entry_t));
  pt_entry_t   upper_pte;
  vmsim_read_real(&upper_pte, upper_pte_addr, sizeof(upper_pte));

  // If the lower table doesn't exist, create it and update the upper table.
  if (upper_pte == 0) {

    upper_pte = allocate_pt();
    assert(upper_pte != 0);
    vmsim_write_real(&upper_pte, upper_pte_addr, sizeof(upper_pte));
    
  }

  // Grab the lower table's entry.
  vmsim_addr_t lower_pt       = GET_PAGE_ADDR(upper_pte);
  vmsim_addr_t lower_index    = GET_LOWER_INDEX(sim_addr);
  vmsim_addr_t lower_pte_addr = lower_pt + (lower_index * sizeof(pt_entry_t));
  pt_entry_t   lower_pte;
  vmsim_read_real(&lower_pte, lower_pte_addr, sizeof(lower_pte));

  // If there is no mapped page, create it and update the lower table.
  if (lower_pte == 0) {

    lower_pte = allocate_real_page();
    vmsim_addr_t real_addr = lower_pte;
    SET_RESIDENT(lower_pte);
    vmsim_write_real(&lower_pte, lower_pte_addr, sizeof(pt_entry_t));
    
    //record pointer to lower pte in entries
    entries[get_page_no(real_addr)] = (pt_entry_t*)(lower_pte_addr + real_base);

    //DEBUG: update last pte
    last_pte = &lower_pte;


  }  
  //unsigned int test = IS_RESIDENT(lower_pte);
  //printf("%u", test);
  //printf("%u", ~IS_RESIDENT(lower_pte));
  //fflush(stdout);
  if (IS_RESIDENT(lower_pte)==0){//if it is not resident, we need to swap it in
    pt_entry_t* out = search();
    swap(lower_pte_addr, out);
  }
    
  
} // vmsim_map_fault ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_read_real (void* buffer, vmsim_addr_t real_addr, size_t size) {

  // Get a pointer into the real space and check the bounds.
  void* ptr = real_base + real_addr;
  void* end = (void*)((intptr_t)ptr + size);
  assert(end <= real_limit);

  // Copy the requested bytes from the real space.
  memcpy(buffer, ptr, size);
  
} // vmsim_read_real ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_write_real (void* buffer, vmsim_addr_t real_addr, size_t size) {

  // Get a pointer into the real space and check the bounds.
  void* ptr = real_base + real_addr;
  void* end = (void*)((intptr_t)ptr + size);
  assert(end <= real_limit);

  // Copy the requested bytes into the real space.
  memcpy(ptr, buffer, size);
  
} // vmsim_write_real ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_read (void* buffer, vmsim_addr_t addr, size_t size) {

  vmsim_addr_t real_addr = vmsim_map(addr, false);
  vmsim_read_real(buffer, real_addr, size);

} // vmsim_read ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_write (void* buffer, vmsim_addr_t addr, size_t size) {

  vmsim_addr_t real_addr = vmsim_map(addr, true);
  vmsim_write_real(buffer, real_addr, size);

} // vmsim_write ()
// =================================================================================================================================



// =================================================================================================================================
vmsim_addr_t
vmsim_alloc (size_t size) {

  vmsim_init();

  // Pointer-bumping allocator with no reclamation.
  vmsim_addr_t addr = sim_free_addr;
  sim_free_addr += size;
  return addr;
  
} // vmsim_alloc ()
// =================================================================================================================================



// =================================================================================================================================
void
vmsim_free (vmsim_addr_t ptr) {

  // No relcamation, so nothing to do.

} // vmsim_free ()
// =================================================================================================================================


//Move_to_bs: takes a lower pte and moves its corresponding page to the backing store.
//Replaces the address in the pte with a block number
//Returns the real address of the newly freed memory.

vmsim_addr_t
move_to_bs(pt_entry_t* lpt_entry){
  pt_entry_t lpte_a = *lpt_entry;
	vmsim_addr_t real_addr = GET_PAGE_ADDR(lpte_a);
	bs_write(real_addr, block_no);
	int addr_remover = 0x3ff;
	lpte_a &= addr_remover;
	lpte_a |= (block_no << 10);
	block_no = block_no + 1;
	CLEAR_RESIDENT(lpte_a);
	vmsim_write_real(&lpte_a, get_real_address(lpt_entry), sizeof(pt_entry_t));

	void* real_ptr = (void*)(real_base + real_addr);

	memset(real_ptr, 0, PAGESIZE);
	return real_addr;
}

//Move_to_MM: takes a lower pte with a block number and a real address
//Copies the block from the bs into the real address, then assignes the real address to the pte


void
move_to_mm(vmsim_addr_t lpt_entry_ra, vmsim_addr_t real_addr){
  pt_entry_t lpt_entry;
  vmsim_read_real(&lpt_entry, lpt_entry_ra, sizeof(pt_entry_t));
	int blockno_getter = 0xfffc00;
	int block_number = (lpt_entry & blockno_getter) >> 10;
	bs_read(real_addr, block_number);
	lpt_entry &= 0x3ff;
	lpt_entry |= real_addr;
	SET_RESIDENT(lpt_entry);
	vmsim_write_real (&lpt_entry, lpt_entry_ra, sizeof(pt_entry_t));

	entries[get_page_no(real_addr)] = (pt_entry_t*)(real_base+lpt_entry_ra);

}

//Swap: Combines the above to swap a given page out and copy a given block in
void
swap(vmsim_addr_t in, pt_entry_t* out){
	vmsim_addr_t real_space = move_to_bs(out);
	move_to_mm(in, real_space);
}

//Search: Uses CLOCK algorithm to find a non-referenced lpt entry
pt_entry_t* 
search(){
  vmsim_addr_t pt = PT_AREA_SIZE;
  pt_entry_t lpte = *entries[cur_page_no];
  while IS_REFERENCED(lpte){
      pt_entry_t entry_no_ref = CLEAR_REFERENCED(lpte);
      vmsim_write_real(&entry_no_ref, get_real_address(entries[cur_page_no]),sizeof(pt_entry_t));
      cur_page_no = (cur_page_no + 1) % ENTRIES_LENGTH;
      lpte = *entries[cur_page_no];
    }
  return entries[cur_page_no];
}

uint64_t get_page_no(vmsim_addr_t real_addr){
  return (real_addr - PT_AREA_SIZE) / PAGESIZE;
}
//DEBUG: show_entries: prints the contents of the "entries" array:
void show_entries(){
  for (int i = 0; i < ENTRIES_LENGTH; i++){
  }
}
//get_real_address: Calculates the real address of the lpte given a pointer to the lpte
vmsim_addr_t get_real_address(pt_entry_t* lpte_pt){
  return (vmsim_addr_t)((void*)lpte_pt - real_base);
}
