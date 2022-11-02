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
    "zxcvbee@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* 메크로 */
#define WSIZE 4
#define DSIZE 8
#define MINIMUM 16      /* 헤더, 푸터, 전자, 후자 초기화*/
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

/* Free List 상에서의 이전, 이후 블록의 포인터를 retutn */
#define PREC_FREEP(bp)  (*(void**)(bp))             /* 이전 블록의 bp */ 
#define SUCC_FREEP(bp)  (*(void**)(bp + WSIZE))     /* 이후 블록의 bp */ 

/* 정렬 유지 위해 가까운 배수로 반올림 */
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 함수 선언 */
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);
void remove_block(void *);

/* 전역 변수 */
static char *heap_listp;
static char *free_listp; /* free list의 맨 첫 블록을 가리키는 포인터 */ 

/* 
 * mm_init - 할당기 초기화 
 */
int mm_init(void)
{   
    /* 메모리에서 6워드 가져와 빈 가용 리스트 초기화 */
    /* padding, prol_header, prol_footer, PREC, SUCC, epil_header */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
    return -1;

    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), NULL);             /* prologue block안 PREC 포인터 NULL 초기화 */
    PUT(heap_listp + (3*WSIZE), NULL);             /* prologue block안 SUCC 포인터 NULL 초기화 */
    PUT(heap_listp + (4*WSIZE), PACK(MINIMUM, 1)); /* Prologue footer */
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));       /* Epilogue header */
    
    free_listp = heap_listp + 2*WSIZE;           /* free_listp를 탐색의 시작점으로 지정 */

    /* heap을 CHUNKSIZE 바이트로 확장 후 초기 가용 블록 생성 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}

/*
 * remove_block - 할당되거나 연결되는 가용 블록을 free list에서 삭제
 */
void remove_block(void *bp){
    /* free list의 첫번째 블록 삭제시 */ 
    if (bp == free_listp){
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);    /* free list의 맨 첫 블록을 가리키는 포인터가 다음 블록 가리키도록 */
    }
    /* free list안에서 삭제시 */ 
    else{
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
}

/*
 * put_freeblock - 새로 반환 및 생성된 가용 블록을 free list의 첫 부분에 추가 
 */
void put_freeblock(void* bp){
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(bp) = NULL;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
}

/*
 * coalesc - 가용 블럭 생성시 통합 
 */
static void *coalesce(void *bp)
{
    /* 직전 블록의 푸터, 직후 블록의 헤더 통해 가용 여부를 확인.*/ 
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc){   /* Case 1 */
        remove_block(NEXT_BLKP(bp));        /* 가용 상태인 직후 블록을 free list에서 제거 */ 
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){   /* Case 2 */
        remove_block(PREV_BLKP(bp));        /* 가용 상태인 직전 블록을 free list에서 제거 */ 
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));  
    }
    else if (!prev_alloc && !next_alloc){   /* Case 3 */
        remove_block(PREV_BLKP(bp));        /* 가용 상태인 직전 블록을 free list에서 제거 */ 
        remove_block(NEXT_BLKP(bp));        /* 가용 상태인 직후 블록을 free list에서 제거 */ 
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));  
        PUT(FTRP(bp), PACK(size, 0));  
    }
    /* 연결된 새 가용 블록을 free list에 추가 */
    put_freeblock(bp);
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

/* explicit free list */
/* first-fit 검색 */
static void *find_fit(size_t asize)
{
    void *bp;

    /* 가용 리스트에서 맞는 블록 검색 */
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)){
        if(asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }
    return NULL ;  
}

/* 
 * place - 맞는 블록 찾으면 할당기는 요청한 블록을 배치, 옵션으로 추가 부분 분할
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    /* 할당될 블록이므로 free list에서 삭제 */
    remove_block(bp);

    /* 분할이 가능한 경우 */
    if ((csize - asize) >= (2 * DSIZE))
    {
        /* 앞 블록은 할당 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        /* 뒷 블록은 가용 */
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        /* 가용 리스트에 블럭 추가 */
        put_freeblock(bp);
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
    void *oldptr = bp;  /* 크기를 조절하고 싶은 블록의 시작 포인터 */ 
    void *newptr;       /* 크기 조절 후 새 블록의 시작 포인터 */
    size_t copy_size;    /* 복사할 블록 크기 */

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    copy_size = GET_SIZE(HDRP(oldptr));

    /* 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당 */
    if (size < copy_size)
        copy_size = size;
    
    memcpy(newptr, oldptr, copy_size);  /* 새 블록에 복사할 블록 크기만큼 복사 */
    mm_free(oldptr);                    /* 이전 블록을 free */
    return newptr;
}