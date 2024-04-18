/* mm_segregate */

/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros*/
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 이중 포인터를 사용해 bp가 가리키는 포인터를 가져옴 */
#define GET_PRED(bp) (*(void **)(bp))
#define GET_SUCC(bp) (*(void **)(bp + WSIZE))

// 가용 리스트의 개수
#define SEGREGATED_SIZE (12) 

// 해당 가용 리스트의 루트
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

static char *heap_listp;
static char *freelist_head = NULL;

size_t get_class(size_t asize) {
    if (asize < 2*DSIZE) return -1;
    size_t count = 0;
    while (asize != 1) {
        asize = asize>>1;
        count += 1;
        if (count == SEGREGATED_SIZE + 3) return SEGREGATED_SIZE - 1;
    }

    return count - 4;
}

/* 새로생긴 free block을 free lists에 연결해주는 함수 parameter bp에는 free list가 들어감 */
static void new_free_list_link(char *bp)
{
    size_t asize = GET_SIZE(HDRP(bp));
    size_t class = get_class(asize);

    if (GET_ROOT(class) == NULL) {
        GET_ROOT(class) = bp;
        GET_PRED(bp) = NULL;
        GET_SUCC(bp) = NULL;
        return;
    }
    else {
        GET_PRED(GET_ROOT(class)) = bp;
        GET_PRED(bp) = NULL;
        GET_SUCC(bp) = GET_ROOT(class);
        GET_ROOT(class) = bp;
    }
}

/* free list의 링크를 없애고 지운 free list의 앞뒤를 연결해주는 함수(free해주는건 별개) */
static void remove_free_list_link(char *bp)
{
    size_t asize = GET_SIZE(HDRP(bp));
    size_t class = get_class(asize);

    if (GET_PRED(bp) == NULL && GET_SUCC(bp) == NULL) {
        GET_ROOT(class) = NULL;
    }
    else if (GET_PRED(bp) == NULL) {
        GET_PRED(GET_SUCC(bp)) = NULL;
        GET_ROOT(class) = GET_SUCC(bp);
        GET_SUCC(bp) = NULL;
    }
    else if (GET_SUCC(bp) == NULL) {
        GET_SUCC(GET_PRED(bp)) = NULL;
        GET_PRED(bp) = NULL;
    }
    else {
        GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
        GET_PRED(bp) = NULL;
        GET_SUCC(bp) = NULL;
    }
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); /* 시작부분이면 prologue에 걸려서 1나옴*/
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); /* 끝부분이면 epilogue에 걸려서 1나옴*/
    size_t size = GET_SIZE(HDRP(bp));

    /* 전 블록이 할당되고 다음 블록은 할당되지 않은 경우 */
    if (prev_alloc && !next_alloc) {
        remove_free_list_link(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* 전 블록이 프리고 다음 블록이 할당된 경우 */
    else if (!prev_alloc && next_alloc) {
        remove_free_list_link(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* 앞뒤 블록 모두 프리인 경우 */
    else if (!prev_alloc && !next_alloc) {
        remove_free_list_link(PREV_BLKP(bp));
        remove_free_list_link(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    new_free_list_link(bp);
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epliogue header */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* coalesce if the previous block was free */    
    return coalesce(bp);
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 초기 힙 생성
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성, heap_listp에 힙의 시작 주소값 할당(가용 블록만 추적)
        return -1;
    PUT(heap_listp, 0);                                                    // 정렬 패딩

    PUT(heap_listp + (1 * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Header (크기: 헤더 1 + 푸터 1 + segregated list 크기)
    for (int i = 0; i < SEGREGATED_SIZE; i++)
        PUT(heap_listp + ((2 + i) * WSIZE), NULL);
    PUT(heap_listp + ((SEGREGATED_SIZE + 2) * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));                             // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치

    heap_listp += (2 * WSIZE);

    if (extend_heap(4) == NULL)
        return -1;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    size_t class = get_class(asize);

    while (class != SEGREGATED_SIZE) {
        void *bp = GET_ROOT(class);

        while (bp) {
            if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
	        }
            bp = GET_SUCC(bp);
        }
        class += 1;
    }

    return NULL; /* No fit */
}

static void place(void *bp, size_t asize)
{
    remove_free_list_link(bp);
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        new_free_list_link(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
  // If ptr is NULL, realloc is equivalent to mm_malloc(size)
  if (ptr == NULL)
    return mm_malloc(size);

  // If size is equal to zero, realloc is equivalent to mm_free(ptr)
  if (size == 0) {
    mm_free(ptr);
    return NULL;
  }
    
  /* Otherwise, we assume ptr is not NULL and was returned by an earlier malloc or realloc call.
   * Get the size of the current payload */
  size_t asize = ALIGN(size) + DSIZE;
  size_t copysize = GET_SIZE(HDRP(ptr));

  void *newptr;
  char *next = HDRP(NEXT_BLKP(ptr));
  size_t newsize = copysize + GET_SIZE(next);

  /* Case 1: Size is equal to the current payload size */
  if (asize == copysize)
    return ptr;

  // Case 2: Size is less than the current payload size 
  if (asize < copysize) {

    if((copysize - asize) >= 2*DSIZE) {  

      PUT(HDRP(ptr), PACK(asize, 1));
      PUT(FTRP(ptr), PACK(asize, 1));
      newptr = NEXT_BLKP(ptr);
      PUT(HDRP(newptr), PACK(copysize - asize, 0));
      PUT(FTRP(newptr), PACK(copysize - asize, 0));
      coalesce(newptr);
      return ptr;
    }

    // allocate a new block of the requested size and release the current block
    newptr = mm_malloc(asize);
    memcpy(newptr, ptr, asize - DSIZE);
    mm_free(ptr);
    return newptr;
  }

  // Case 3: Requested size is greater than the current payload size 
  else {

    // next block is unallocated and is large enough to complete the request
    // merge current block with next block up to the size needed and free the 
    // remaining block.
    if ( !GET_ALLOC(next) && newsize >= asize ) {
        if (newsize - asize >= 2*DSIZE) {
            // merge, split, and release
            remove_free_list_link(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            newptr = NEXT_BLKP(ptr);
            PUT(HDRP(newptr), PACK(newsize-asize, 1));
            PUT(FTRP(newptr), PACK(newsize-asize, 1));
            mm_free(newptr);
            return ptr;
        }
        else {
            remove_free_list_link(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(newsize, 1));
            PUT(FTRP(ptr), PACK(newsize, 1));
            return ptr;
        }
    }  
    
    // otherwise allocate a new block of the requested size and release the current block
    newptr = mm_malloc(asize); 
    memcpy(newptr, ptr, copysize - DSIZE);
    mm_free(ptr);
    return newptr;
  }

}