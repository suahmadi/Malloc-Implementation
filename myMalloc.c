#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
inline static void assert(int e) {
  if (!e) {
    const char * msg = "Assertion Failed!\n";
    write(2, msg, strlen(msg));
    exit(1);
  }
}
#else
#include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 *
 */
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/* extra help functions */
static inline void add_chunk();
static inline bool is_last(header *head);
static inline void remove_node(header *head);
static inline header * find(size_t b_size);
static inline header * resize(size_t b_size, header *node);
static inline void insert(header *head);
static inline void update(header* old_head, header *new_head, size_t b_size);
static inline void deallocate(header *head);


/*
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
  return (header *)((char *) ptr + off);
}


/*
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
  return get_header_from_offset(h, get_size(h));
}

/*
 * helper function to update the header of the freelist
 *
 */
static inline void update(header* old_head, header* new_head, size_t b_size) {
  set_size(new_head, b_size);
  new_head->next = old_head->next;
  new_head->prev = old_head->prev;
  old_head->next->prev = new_head;
  old_head->prev->next = old_head;
}

/*
 * checks if it's in the last sentinel
 */
static inline bool is_last(header * head) {
  if (get_size(head) >= (N_LISTS + 2) * sizeof(size_t)) {
    return true;
  } 
  else {
    return false;
  }
}

/*
 * helper function to insert blocks
 */
static inline void insert(header *head) {
  int temp = (get_size(head) - ALLOC_HEADER_SIZE) / sizeof(size_t) - 1;

  if(temp > (N_LISTS - 1)) {
    temp = N_LISTS - 1;
  } else {
    temp = temp;
  }
  header *temp_head = &freelistSentinels[temp];
  head->next = temp_head->next;
  temp_head->next = head;
  temp_head->next->next->prev = head;
  head->prev = temp_head;
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

static inline void remove_node(header *head) {

  int temp = (get_size(head) - ALLOC_HEADER_SIZE) / sizeof(size_t) - 1;

  if (temp > (N_LISTS - 1)) {
    temp = N_LISTS - 1;
  } else {
    temp = temp;
  }
  header *list_ptr = &freelistSentinels[temp];

  for(header *node = list_ptr->next; node != list_ptr; node = node->next) {
    if (node == head) {
      node->prev->next = node->next;
      node->next->prev = node->prev;
    }
  }
}
/*
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
  set_state(fp,FENCEPOST);
  set_size(fp, ALLOC_HEADER_SIZE);
  fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

static inline header *find(size_t b_size) {

  int temp = (int) (b_size - ALLOC_HEADER_SIZE) / sizeof(size_t) - 1;
  if  (temp < 58) {
    temp = temp;
  } else {
    temp = 58;
  }

  for (int i = temp; i < N_LISTS; i++) {
    header *list_ptr = &freelistSentinels[i];
    for (header * node = list_ptr->next; node != list_ptr; node = node->next) {
      if (get_size(node) > b_size) {
        return resize(b_size, node);
      }
      if (get_size(node) == b_size) {
        node->prev->next = node->next;
        node->next->prev = node->prev;
        return node;
      }
    }
  }
  return NULL;
}

static inline header *resize(size_t b_size, header *node) {
  size_t temp = get_size(node);

  if (temp - b_size >= sizeof(header)) {
    set_size(node, temp - b_size);
    header* init_block = node;
    node = (header *) ((char*) node + get_size(node));
    set_size(node, b_size);
    node->left_size = get_size(init_block);
    header *right_block = (header *) ((char *) node + get_size(node));
    right_block->left_size = get_size(node);

    if(get_size(init_block) < (N_LISTS + 2) * sizeof(size_t)) {
      init_block->prev->next = init_block->next;
      init_block->next->prev = init_block->prev;
      insert(init_block);
    }
  }
  return node;
}

/*
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 *
 */

static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation

  size_t size_b = ((raw_size > (2 * sizeof(size_t))? raw_size + ALLOC_HEADER_SIZE : sizeof(header)) + sizeof(size_t) - 1) & ~(sizeof(size_t) - 1);

  header * head = find(size_b);

  if (head == NULL) {
    do {
      add_chunk();
      head = find(size_b);
    } while (head == NULL);
  }
  set_state(head, ALLOCATED);
  return head;
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

static inline void add_chunk() {

  header* block;
  header* prev_b;
  header* prev_FP;
  block = allocate_chunk(ARENA_SIZE);
  prev_b = block;
  prev_FP = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  bool flag = false;

  if (((char *) prev_FP - ALLOC_HEADER_SIZE) == (char *) lastFencePost) {
    header *left_lastFP = get_left_header(lastFencePost);
    size_t left_bsize = 0;
    if(get_state(left_lastFP) == UNALLOCATED) {
      left_bsize = get_size(left_lastFP);
      if (is_last(left_lastFP)) {
        flag = true;
      } else {
        remove_node(left_lastFP);
      }
    }
    block = get_header_from_offset(lastFencePost, -left_bsize);
    set_size(block, ALLOC_HEADER_SIZE * 2 + get_size(prev_b) + left_bsize);
    block->left_size = left_bsize? left_lastFP->left_size : lastFencePost->left_size;
    set_state(block, UNALLOCATED);

  } else {
    insert_os_chunk(prev_FP);

  }
  lastFencePost = get_header_from_offset(prev_b, get_size(prev_b));
  lastFencePost->left_size = get_size(block);

  if (!flag) {
    header *list_ptr = &freelistSentinels[N_LISTS - 1];
    block->next = list_ptr->next;
    list_ptr->next= block;
    block->next->prev = block;
    block->prev = list_ptr;
  }
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  header *head = ptr_to_header(p);
  deallocate(head);
}


static inline void deallocate(header * head) {

  if(get_state(head) == UNALLOCATED) {
    fprintf(stderr, "Double Free Detected\n");
    assert(false);
    exit(1);
  }

  header * l_block = (header *)((char *)head - head->left_size);
  header * r_block = (header *)((char *)head + get_size(head));

  if (get_state(l_block) == UNALLOCATED && get_state(r_block) == UNALLOCATED) {
    size_t temp_size = get_size(l_block) + get_size(head) + get_size(r_block);

    if (is_last(l_block)) {
      remove_node(r_block);
      set_size(l_block, temp_size);
    } else if (is_last(r_block)) {
      remove_node(l_block);
      update(r_block, l_block, temp_size);

    } else {
      remove_node(l_block);
      remove_node(r_block);
      set_size(l_block, temp_size);
      insert(l_block);
    }
    get_right_header(r_block)->left_size = temp_size;
  } else if (get_state(r_block) == UNALLOCATED) {
    if (is_last(r_block)) {
      update(r_block, head, get_size(head) + get_size(r_block));
    } else {
      remove_node(r_block);
      set_size(head, get_size(head) + get_size(r_block));
      insert(head);
    }
    r_block = (header *)((char *) head + get_size(head));
    r_block->left_size = get_size(head);
  } else if (get_state(l_block) == UNALLOCATED) {
    if (is_last(l_block)) {
      set_size(l_block, get_size(head) + get_size(l_block));
    } else {
      remove_node(l_block);
      set_size(l_block, get_size(head) + get_size(l_block));
      insert(l_block);
    }
    r_block->left_size = get_size(l_block);
  } else {
    insert(head);
  }
  set_state(head, UNALLOCATED);
}


/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
        fast != freelist;
        slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }
  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
  if (get_state(chunk) != FENCEPOST) {
    fprintf(stderr, "Invalid fencepost\n");
    print_object(chunk);
    return chunk;
  }

  for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
    if (get_size(chunk)  != get_right_header(chunk)->left_size) {
      fprintf(stderr, "Invalid sizes\n");
      print_object(chunk);
      return chunk;
    }
  }

  return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/*
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  if (!size) {
    return NULL;
  }
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return (header *)((char *)hdr + ALLOC_HEADER_SIZE);
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  if (p != NULL) {
    pthread_mutex_lock(&mutex);
    deallocate_object(p);
    pthread_mutex_unlock(&mutex);
  }
}

bool verify() {
  return verify_freelist() && verify_tags();
}
