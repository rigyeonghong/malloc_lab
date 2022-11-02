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
    "week6",
    /* First member's full name */
    "rigyeonghong",
    /* First member's email address */
    "ghdflrud96@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* 메크로 */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 return */
#define PACK(size, alloc) ((size) | (alloc))

/* 인자 p가 참조하는 워드 읽어서 return */
/* 인자 p는 대개 (void*) 포인터. 직접적으로 역참조 불가 */ 
#define GET(p) (*(unsigned int *)(p))
/* 인자 p가 가리키는 워드에 val 저장 */
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 각각 주소 p에 있는 헤더, 풋터의 size와 할당 비트를 return */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 포인터 bp가 주어지면, 각각 블록 헤더와 풋터를 가리키는 포인터 return */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp가 주어지면, 각각 다음과 이전 블록의 블록 포인터를 return */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 함수 선언 */
static void *extend_heap(size_t);
static void *coalesce(void *);

/* 전역 변수 */
static char *heap_listp;

/* 
 * mm_init - 할당기 초기화 
 */
int mm_init(void)
{   
    /* 메모리 시스템에서 4워드 가져와 빈 가용 리스트 만들 수 있도록 초기화 */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue footer */
    heap_listp += (2*WSIZE);

    /* heap을 CHUNKSIZE 바이트로 확장 후 초기 가용 블록 생성 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}

/*
 * coalesc - 가용 블럭 생성시 통합 
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){        /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc){   /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){   /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{                                   /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/* 
 * expend_heap - malloc package 초기화
 *               1. 힙 초기화시
 *               2. mm_malloc이 적당한 fit을 못찾았을 때, 정렬 유지 위해 호출
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 정렬 유지 위해 짝수 word 할당 */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

    /* 가용 블럭의 헤더, 푸터 와 epilogue 헤더 초기화 */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block 헤더 */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block 푸터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue 헤더 */

    /* 이전 블록이 가용됬을 때 통합 */
    return coalesce(bp);
}

/* first-fit 검색 */
static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    /* No fit */
    return NULL;    
}

/* 
 * place - 맞는 블록 찾으면 할당기는 요청한 블록을 배치, 옵션으로 추가 부분 분할
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - size 바이트의 메모리 블록 요청
 *             brk pointer를 증가시켜 블록 할당        
 */
void *mm_malloc(size_t size)
{
    size_t asize;        /* 조정된 블록 크기 */
    size_t extendsize;   /* 적합하지 않을 경우 힙을 확장할 크기 */
    char *bp;

    /* 거짓 요청시 */
    if (size == 0)
        return NULL;

    /* 헤더와 풋터 위한 공간 확보 및 더블 워드 요건 만족시킴 */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else /* 8바이트 넘는 요청에 대해 오버헤드 바이트 추가, 인접 8의 배수로 반올림 */
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    /* 적절한 가용 블록을 가용 리스트에서 검색 */
    if ((bp = find_fit(asize)) != NULL){
        /* 맞는 블록 찾으면 할당기는 요청한 블록을 배치, 옵션으로 추가 부분 분할 */
        place(bp, asize);
        /* 새로 할당한 블록의 포인터 return */
        return bp;
    }

    /* 적절한 가용 블록을 가용 리스트에서 찾지 못하면, 힙을 새로운 가용 블록으로 확장 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    /* 요청한 블록을 새 가용 블록에 배치, 필요시 블록을 분할 */
    place(bp, asize);
    /* 새로 할당한 블록의 포인터 return */
    return bp;
}

/*
 * mm_free - 요청한 블록 반환하고 경계 태그 연결 사용해 상수 시간에 인접 가용 블록들과 통합
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    /* 인접 가용 블록들 통합 */
    coalesce(bp);
}


/*
 * mm_realloc - 동적 할당된 메모리 내용 유지하며 할당된 메모리 크기 변경
 */
void *mm_realloc(void *bp, size_t size)
{
    if ((int)size < 0)
        return NULL;
    else if ((int)size == 0)
    {
        mm_free(bp);
        return NULL;
    }
    else if (size > 0)
    {
        size_t oldsize = GET_SIZE(HDRP(bp));
        size_t newsize = size + (2 * WSIZE); /* 헤더와 푸터 위한 2 words 추가 */ 
        /* newsize가 oldsize보다 작거나 같으면 return bp */
        if (newsize <= oldsize)
        {
            return bp;
        }
        /* oldsize 보다 new size가 크면 바꿈 */
        else
        {
            /* 다음 블록의 할당 여부 비트 */
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
            size_t csize;
            /* next block이 가용 상태이고, old와 next block의 사이즈 합이 new size보다 크면 합쳐서 사용  */
            if (!next_alloc && ((csize = oldsize + GET_SIZE(HDRP(NEXT_BLKP(bp))))) >= newsize)
            {
                // remove_from_free_list(NEXT_BLK(bp));
                PUT(HDRP(bp), PACK(csize, 1));
                PUT(FTRP(bp), PACK(csize, 1));
                return bp;
            }
            /* next block이 할당된 상태이거나, old와 next block의 사이즈 합이 new size보다 작을 때 새 block 생성 */
            else
            {
                void *new_ptr = mm_malloc(newsize);
                place(new_ptr, newsize);
                memcpy(new_ptr, bp, newsize);
                mm_free(bp);
                return new_ptr;
            }
        }
    }
    else
        return NULL;
}