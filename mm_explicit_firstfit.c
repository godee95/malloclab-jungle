/*
 * Malloc using explicit free block with first-fit
 */


/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

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
    ""};
/*********************************************************/

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size(bytes) */
#define DSIZE 8 /* Double word size(bytes) */

/* Extend heap by this amount(bytes) sbrk() 함수기능 */
// 2의 12승, 4096byte 메모리 할당 효율성을 높이기 위한 정의
// 사용 가능한 block이 없을 경우 확장. 너무 작게 설정하면 자주 확장하므로 적절한 크기로 설정해줘야 함.
#define CHUNKSIZE (1<<12) 
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Paxk a size and allocated bit into a word */
// size는 블록의 크기 정보를 저장
// alloc은 블록의 할당 여부(0, 1) 나타냄
#define PACK(size, alloc) ((size) | (alloc)) // OR 연산자 이용해 블록의 헤더 값을 생성

/* Read and write a word at address p */
// header와 footer는 모두 word형식으로 저장ㄷ됨.
// 각 비트(bit)는 0 또는 1의 값을 가지는 bit의 모음
#define GET(p) (*(unsigned int *)(p)) // 포인터 p가 가리키는 4byte word(void point 형태)를 반환
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 포인터 p가 가리키는 word에 val값을 저장

/* Read the size and allocated fields from address p */
// ~0x7(111...11000) 마지막 3비트를 0으로 만들어줌.
// 마지막 3비트를 제외한 나머지 부분을 반환해 주소 'p'을 블록 크기를 추출
#define GET_SIZE(p) (GET(p) & ~0x7) // 상위 29bit에 블록 크기 반환
#define GET_ALLOC(p) (GET(p) & 0x1) // 하위 1bit에 할당 여부 반환(0 or 1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE) // bp 포인터가 가르키는 블록의 header 포인터 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // bp 포인터가 가르키는 블록의 footer 포인터 반환

/* Given block ptr bp, compute address of next and previous blocks */
// bp : 현재 블록을 가리키는 포인터
// bp 포인터가 가리키는 블록의 다음 블록 포인터 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 현재 블록 사이즈만큼 더해주고 word만큼 이동해(bp - WSIZE) header위치로 감.
// bp 포인터가 가리키는 블록의 이전 블록 포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 fooder로 이동해(bp - DSIZE) 이전 블록 사이즈만큼 빼줌

// free block 들의 정보를 모아둔 리스트 정보
// SUCC가 PRED보다 많이 쓰이므로 데이터를 접근하기 쉽도록 HEADER와 더 가까이 배치 
#define NEXT_FREE(bp) (*(void **)(bp))         /* Next free block의 시작주소 */
#define PREV_FREE(bp) (*(void **)(bp + WSIZE)) /* Prev free block의 시작주소 */


//***************************mm******************************
static char *heap_listp;
static char *free_listp; /* 가용 블록 리스트의 시작 */

/* LIFO - 반환되거나 분할로 생긴 가용 블록을 가용리스트 가장 앞에 추가 */
static void splice_in(void *bp)
{
    PREV_FREE(bp) = NULL; // 이전 블록은 없으니 NULL 할당
    NEXT_FREE(bp) = free_listp; // 현재 블록의 다음 가용 블록의 free_listp가 가리키는 포인터 할당
    PREV_FREE(free_listp) = bp; // 가용 블록의 이전 가용 블록을 현재 블록을 가리키는 포인터 할당
    free_listp = bp; // free_listp가 가리키는 블록으로 현재 블록을 가리키는 포인터 할당
}


/* 가용 블록을 free list에서 삭제 */
void splice_out(void *bp)
{
    if (bp) {
        // 이전 가용블록 없음
        if (PREV_FREE(bp)) {
            NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
        }
        else {
            free_listp = NEXT_FREE(bp);
        }
        if (NEXT_FREE(bp) != NULL) {
            // 이후 가용 블록 없음
            PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
        }
    }
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 footer에 접근해 할당 여부 반환
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 header에 접근해 할당 여부 반환
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 header에 접근해 size정보 반환

    // Case 1
    // if (prev_alloc && next_alloc) {
    //     // 이미 가용 리스트에 존재하는 블록은 연결하기 이전에 제거
    //     return bp;
    // }

    // Case 2
    if (prev_alloc && !next_alloc) {
        // 이전 블록 할당, 다음 블록 free
        // 다음 블록 header에 접근
        splice_out(NEXT_BLKP(bp)); // 미리 제거해 혹시 모를 포인터로 인한 오류 방지

        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록 사이즈 만큼 size 더해줌
        // block point는 현재 그대로 유지지
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록의 header 정보 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록의 footer 정보 갱신
    }

    // Case 3
    else if(!prev_alloc && next_alloc) {
        // 이전 블록 free, 다음 블록 할당
        // 이전 블록 footer에 접근
        splice_out(PREV_BLKP(bp));

        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        // block point를 이전 블록의 포인터 위치로 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록의 footer의 정보 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 header 정보 갱신
        bp = PREV_BLKP(bp); // block point를 이전 블록의 block point로 변경
    }

    // Case 4
    else if(!prev_alloc && !next_alloc) {
        // 이전 블록 free, 다음 블록 free
        // 이전 블록 footer와 다음 블록 header에 접근
        splice_out(NEXT_BLKP(bp));
        splice_out(PREV_BLKP(bp));

        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // block point를 이전 블록의 포인터 위치로 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 header 정보 갱신
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록의 fooder 정보 갱신
        bp = PREV_BLKP(bp); // block point를 이전 블록의 block point로 변경
    }

    splice_in(bp);

    return bp;
}

/*
두 가지 경우에 호출됨
1. 힙이 초기화될 때
2. mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때
*/
static void *extend_heap(size_t words) /* 워드 단위 */
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; /* 데이터 크기 words가 홀수이면 짝수로 만들어 줌(padding) */
    if ((long)(bp = mem_sbrk(size)) == -1)                    /* 사이즈를 해당 크기만큼 늘릴 수 없으면 */
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1) /* 메모리 할당 오류가 발생했으면 */
        return -1;
    PUT(heap_listp, 0);                                /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1)); /* Prologue, heap의 정렬 & heap의 sential역할(경계태그) */
    /* 왜 NEXT를 앞으로? payload 자리를 찾아가는 코드로 구성되어 있기 때문에 해당 자리에서 바로 찾을 수 있는 곳에 NEXT를 둬서 최대한의 동작을 줄임 */
    PUT(heap_listp + (2 * WSIZE), PACK(0, 0));               /* 프롤로그 NEXT NULL로 초기화. */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 0));               /* 프롤로그 PREV NULL로 초기화 */
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         /* Epilogue header */

    free_listp = heap_listp + DSIZE; /* 첫 가용블록의 payload */
    // free_listp = heap_listp + 2 * DSIZE;

    /*  Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *find_fit(size_t asize)
{
    void *p = free_listp;

    while (!GET_ALLOC(HDRP(p)))
    {
        if (GET_SIZE(HDRP(p)) >= asize)
        {
            return p;
        }
        p = NEXT_FREE(p);
    }
    return NULL; // No fit
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));  /* 가용 블록의 크기 */
    splice_out(bp);                    /* 사용할 가용블록을 가용리스트에서 없애기 */
    if ((csize - asize) >= (2 * DSIZE)) /* 분할의 가치가 있음 */
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1)); /* 헤더가 있기 때문에 푸터 찾을 수 있음 */
        bp = NEXT_BLKP(bp);
        splice_in(bp); /* 분할하고 남은 가용블록 가용리스트에 추가 */
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else /* 남은 가용 블록의 크기가 2*DSIZE보다 작으면 */
    {
        /* 다 쓰기(패딩) */
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
    size_t asize;      /* Adjsted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs */
    if (size <= DSIZE)
        asize = 2 * DSIZE; // 8의 배수로
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); /* 값으로 나눴을 때 나머지가 될 수 있는 수의 최댓값은 값-1 */

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); /* 배치하기 */
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) /* 바이트 단위 -> 워드 단위 */
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (!ptr)
        return;

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
    // 잠재적인 오류를 처리하기 위한 예외처리.
    if (ptr == NULL) {
        return mm_malloc(size);
    }
        
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    // 이미 할당된 메모리를 다른 곳으로 옮긴다.
    // 이를 통해 다양한 중간에 작은 메모리들로 인해
    // 나뉘어져 있던 메모리를 하나의 큰 메모리로 활용할 수 있다.
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE; /* 기존에 할당된 블록의 사이즈. */
    // 새로 할당해주는 size가 old block pointer가 가리키는 곳의 사이즈보다 작으면
    // copySize 값을 업데이트!
    if (size < copySize)
        copySize = size;

    // old block pointer가 가리키는 곳에서 copySize만큼 가져와 
    // new block pointer가 가리키는 곳에 할당해준다.
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}