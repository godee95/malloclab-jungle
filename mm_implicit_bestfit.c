/*
 * Malloc using implicit free block with best-fit
 */

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

/* Next Fit */
// #define FREE_LIST_NEXT(bp) (*(char **)(bp + WSIZE))
// #define SET_NEXT_FREE(bp, ptr) (*(void **)(bp + WSIZE) = ptr)
// #define SET_PREV_FREE(bp, ptr) (*(void **)(bp) = ptr)

/* 
 * mm_init - initialize the malloc package.
 */
static char *heap_listp; // 처음에 쓸 가용블록 heap을 만들어 줌
// static char *last_fitp; // Next Fit 구현을 위해 last block point 만들어줌
static void *coalesce(void *bp);

static void *extend_heap(size_t words)
{
    // printf("extend heap\n");
    char *bp; // 현재 블록을 가리키는 포인터 생성
    size_t size; // 확장하고 싶은 word 크기

    /* Allocate an even number of words to maintain alignment */
    // 정렬을 위해 짝수 갯수의 words 할당.
    size = (words % 2) ? (words + 1)*WSIZE : words * WSIZE;

    /* 메모리 확장 불가능 예외처리 */
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    

    /* Coalesce if the previous block was free */
    // 이전 블록이 가용이면, 가용 메모리 늘리기
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 footer에 접근해 할당 여부 반환
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 header에 접근해 할당 여부 반환
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 header에 접근해 size정보 반환

    // Case 1
    if (prev_alloc && next_alloc) {
        // 이전 블록과 다음 블록 모두 할당되어 있으면 현재 block point 반환
        return bp;
    }

    // Case 2
    else if (prev_alloc && !next_alloc) {
        // 이전 블록 할당, 다음 블록 free
        // 다음 블록 header에 접근

        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록 사이즈 만큼 size 더해줌
        // block point는 현재 그대로 유지지
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록의 header 정보 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록의 footer 정보 갱신
    }

    // Case 3
    else if(!prev_alloc && next_alloc) {
        // 이전 블록 free, 다음 블록 할당
        // 이전 블록 footer에 접근

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

        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // block point를 이전 블록의 포인터 위치로 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 header 정보 갱신
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록의 fooder 정보 갱신
        bp = PREV_BLKP(bp); // block point를 이전 블록의 block point로 변경
    }

    return bp;
}

/* Best Fit */
static void *best_fit(size_t asize)
{
    char *p = heap_listp; // prologue block
    char *bestp = NULL;
    size_t min_diff = (size_t)-1; // 현재까지 가장 적합한 블록을 찾기 위해 최솟갑으로 초기화

    while (GET_SIZE(HDRP(p)) != 0) // Epilogue block의 size가 0이니깐 0이 되면 탐색 종료.
    {
        if (!GET_ALLOC(HDRP(p)) && (GET_SIZE(HDRP(p)) >= asize)) {
            // printf("best_fit: found a fit at address %p\n", p);

            size_t diff = GET_SIZE(HDRP(p)) - asize;

            // 이전에 찾은 가장 적합한 블록보다 적합한 블록을 찾은 경우
            // 새로운 블록을 bestp에 저장하고 diff를 min_diff에 저장
            if (diff < min_diff) {
                bestp = p;
                min_diff = diff;
            }
        }
        p = (NEXT_BLKP(p)); // next_block 가리킴
    }

    if (bestp == NULL) {
        // printf("best_fit: no fit found\n");
        return NULL; // No fit found
    }

    return bestp;
}

static void place(void *bp, size_t asize)
{
    // find_fit에서 이미 asize보다 큰 free block 찾았으므로
    // 나머지 부분이 있거나 없거나 두가지 케이스밖에 없음
    size_t old_size = GET_SIZE(HDRP(bp)); // header에 접근해 free_block 사이즈 반환
    size_t remaining = old_size - asize; // 할당 한뒤, 남겨지는 사이즈 splitting

    if (remaining >= (2*DSIZE)) {
        // splitting
        // printf("Splitting block with size %zu into blocks with sizes %zu and %zu\n", old_size, asize, remaining);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        char *next_bp = NEXT_BLKP(bp); // free block splitting
        PUT(HDRP(next_bp), PACK(remaining, 0));
        PUT(FTRP(next_bp), PACK(remaining, 0));
    } else {
        // printf("Placing block with size %zu\n", old_size);
        PUT(HDRP(bp), PACK(old_size, 1));
        PUT(FTRP(bp), PACK(old_size, 1));
    }
}

int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    // Alignment padding, 빈공간 정렬을 효율적으로 하기 위해(짝수되도록)
    PUT(heap_listp, 0); 
    // Prologue Block, 8의 배수 정렬 효율적 & splitting 쉽도록
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // Prologue footer
    // free block의 끝을 나타내는 역할, heap 확장하는 과정에서 사용.
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // Epilogue header
    // prologue header와 prologue footer 사이의 첫 번째 블록을 가리킴
    // 메모리 할당 및 해제 시, 잘못된 방법으로 할당&해제 되는 것을 방지
    heap_listp += (2*WSIZE); 

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    // heap 크기가 작아서, heap을 확장해야 하는 경우, 호출하는 함수.
    // heap 확장이 실패하면 -1 반환.
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{

    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to exted heap if no fit */
    char *bp;

    /* Ignore spurious requests 잘못된 요청 예외처리 */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs */
    if (size <= DSIZE)
        asize = 2*DSIZE; // 8의 배수로 조정
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = best_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    // 넣어 줄 곳 없으면 heap 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    return bp; // 할당된 블록의 시작 주소 반환
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr)); // header 정보 이용해 현재 블록의 size 가져옴.

    // 빈공간으로 만들기
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

void *mm_realloc(void *ptr, size_t size)
{
    void *old_bp = ptr;
    void *new_bp;
    size_t copySize;

    new_bp = mm_malloc(size);

    if (new_bp == NULL)
        return NULL;

    copySize = GET_SIZE(HDRP(old_bp)) - DSIZE; // size에서 header와 footer 제외한 면적

    // 새로 할당해주는 size가 old block pointer가 가리키는 곳의 사이즈보다 작으면
    // copySize 값을 업데이트!
    if (size < copySize)
        copySize = size;

    // old block pointer가 가리키는 곳에서 copySize만큼 가져와 
    // new block pointer가 가리키는 곳에 할당해준다.
    memcpy(new_bp, old_bp, copySize); 
    mm_free(old_bp);

    return new_bp;
}