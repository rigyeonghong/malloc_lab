#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "week6",
    "Rigyeong Hong",
    "zxcvbee@naver.com",
    "Suyeon Woo",
    "woosean999@gmail.com",
};


/* 메크로 */
#define WSIZE 4          
#define DSIZE 8      
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE (1<<12)//+(1<<7) 
#define LISTLIMIT 20    

#define MAX(x, y) ((x) > (y) ? (x) : (y)) 

/* 정렬 유지 위해 가까운 배수로 반올림 */
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)

/* 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 return */
#define PACK(size, alloc) ((size) | (alloc))

/* 인자 p가 참조하는 워드 읽어서 return */
/* 인자 p는 대개 (void*) 포인터. 직접적으로 역참조 불가 */ 
#define GET(p)            (*(unsigned int *)(p))
/* 인자 p가 가리키는 워드에 val 저장 */
#define PUT(p, val)       (*(unsigned int *)(p) = (val))

/* 각각 주소 p에 있는 헤더, 풋터의 size와 할당 비트를 return */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)  // 1이 할당 0이 free

/* 블록 포인터 bp가 주어지면, 각각 블록 헤더와 풋터를 가리키는 포인터 return */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp가 주어지면, 각각 다음과 이전 블록의 블록 포인터를 return */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

/* Free List 상에서의 이전, 이후 블록의 포인터를 retutn */
#define PRED_bp(bp) ((char *)(bp))
#define SUCC_bp(bp) ((char *)(bp) + WSIZE)

/* segregated list에서 가용 블록의 이전, 이후 포인터 저장  */
#define SET_bp(p, bp) (*(unsigned int *)(p) = (unsigned int)(bp))

/* segregated list에서 가용 블록의 이전, 이후 주소 */
#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(SUCC_bp(bp)))

/* 전역변수 */
void *segregated_free_lists[LISTLIMIT]; 

/*  함수 선언 */
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *place(void *, size_t );
static void insert_node(void *, size_t );
static void delete_node(void *);


///////////////////////////////// Block information /////////////////////////////////////////////////////////
/*
 
A   : Allocated? (1: true, 0:false)
RA  : Reallocation tag (1: true, 0:false)
 
 < Allocated Block >
 
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                                                                                               |
            |                                                                                               |
            .                              Payload and padding                                              .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
 < Free block >
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |RA| A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its predecessor in Segregated list                          |
bp+WSIZE--> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its successor in Segregated list                            |
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            .                                                                                               .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
*/
///////////////////////////////// End of Block information /////////////////////////////////////////////////////////

//////////////////////////////////////// Helper functions //////////////////////////////////////////////////////////

/* 
 * expend_heap - malloc package 초기화
 *               1. 힙 초기화시
 *               2. mm_malloc, mm_realloc이 적당한 fit을 못찾았을 때, 정렬 유지 및 새 가용 메모리 획득 위해 호출
 */
static void *extend_heap(size_t size)
{
    void *bp;                   
    size_t asize; /* 조정한 크기 */
    
    /* 정렬 유지 위해 가까운 배수로 반올림 */
    asize = ALIGN(size);
    /* epilogue 블록 헤더에 이어서 double words로 정렬된 새 가용 메모리 블록 return */
    if ((bp = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    /* 가용 블럭의 헤더, 푸터 와 epilogue 헤더 초기화 */
    PUT(HDRP(bp), PACK(asize, 0));  
    PUT(FTRP(bp), PACK(asize, 0));   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 
    /* 가용 리스트에 가용 블록 넣기 */
    insert_node(bp, asize);

    /* 가용 블록 통합 */
    return coalesce(bp);
}

/* 
 * insert_node - 가용 블록 목록(free segregated list)에 가용 블록 추가
 */
static void insert_node(void *bp, size_t size) {
    int list = 0;
    void *search_bp = bp;
    void *insert_bp = NULL;
    
    /* seglist 선택 */
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    /* 크기 오름차순 유지 및 검색 */
    search_bp = segregated_free_lists[list];
    while ((search_bp != NULL) && (size > GET_SIZE(HDRP(search_bp)))) {
        insert_bp = search_bp;
        search_bp = PRED(search_bp);
    }
    
    /* seglist 해당 인덱스에 가용 블록들이 있을 때 */
    if (search_bp != NULL) {
        if (insert_bp != NULL) {
            /* 이미 존재하는 가용 블록들 중 알맞는 위치에 저장 */
            SET_bp(PRED_bp(bp), search_bp);
            SET_bp(SUCC_bp(search_bp), bp);
            SET_bp(SUCC_bp(bp), insert_bp);
            SET_bp(PRED_bp(insert_bp), bp);
        } else {
            SET_bp(PRED_bp(bp), search_bp);
            SET_bp(SUCC_bp(search_bp), bp);
            SET_bp(SUCC_bp(bp), NULL);
            segregated_free_lists[list] = bp;
        }
    /* seglist 해당 인덱스에 가용 블록들이 없을 때 */
    } else {
        SET_bp(PRED_bp(bp), NULL);
        SET_bp(SUCC_bp(bp), NULL);
        segregated_free_lists[list] = bp;
    }
    return;
}

/* 
 * delete_node - 가용 블록 목록(free segregated list)에 가용 블록 삭제
 */
static void delete_node(void *bp) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(bp));
    
    /* segregated list 선택 */
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    /* segregated list에서 가용 블록의 이전 가용 블록이 존재할 때 */
    if (PRED(bp) != NULL) {
        /* segregated list에서 가용 블록의 이후 가용 블록이 존재할 때 */
        if (SUCC(bp) != NULL) {
            SET_bp(SUCC_bp(PRED(bp)), SUCC(bp));
            SET_bp(PRED_bp(SUCC(bp)), PRED(bp));
        /* segregated list에서 가용 블록의 이후 가용 블록이 존재하지 않는 마지막일 때 */
        } else {
            SET_bp(SUCC_bp(PRED(bp)), NULL);
            segregated_free_lists[list] = PRED(bp);
        }
    /* segregated list에서 가용 블록의 이전이 가용 블록이 존재하지 않는 맨 앞일 때 */
    } else {
        /* segregated list에서 가용 블록의 이후 가용 블록이 존재할 때 */
        if (SUCC(bp) != NULL) {
            SET_bp(PRED_bp(SUCC(bp)), NULL);
        } else {
            segregated_free_lists[list] = NULL;
        }
    }
    return;
}

/*
 * coalesc - 가용 블럭 생성시 통합 
 */
static void *coalesce(void *bp)
{
    /* 직전 블록의 푸터, 직후 블록의 헤더 통해 가용 여부를 확인.*/ 
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc) {                         // Case 1
        return bp;
    }
    else if (prev_alloc && !next_alloc) {                   // Case 2
        delete_node(bp);                                    /* 현재, 다음 블록 가용 리스트에서 삭제 */
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {                 // Case 3 
        delete_node(bp);                                    /* 이전, 현재 블록 가용 리스트에서 삭제 */
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {                                                // Case 4
        delete_node(bp);                                    /* 이전, 현재, 이후 블록 가용 리스트에서 삭제 */
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    insert_node(bp, size);                                  /* 가용 리스트에 가용 블록 추가 */
    return bp;
}

/* 
 * place - 맞는 블록 찾으면 할당기는 요청한 블록을 배치, 옵션으로 추가 부분 분할
 */
static void *place(void *bp, size_t asize)
{
    size_t bp_size = GET_SIZE(HDRP(bp));
    size_t remainder = bp_size - asize;
    delete_node(bp);
    
    if (remainder <= DSIZE * 2) {
        PUT(HDRP(bp), PACK(bp_size, 1)); 
        PUT(FTRP(bp), PACK(bp_size, 1)); 
    }
    
    else if (asize >= 100) { 
        /* 가용 블록의 뒷부분부터 asize만큼 블록 분할 및 할당 후 나머지 앞부분 가용블록으로 추가 */
        PUT(HDRP(bp), PACK(remainder, 0));  
        PUT(FTRP(bp), PACK(remainder, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        insert_node(bp, remainder);
        return NEXT_BLKP(bp);
    }
    
    else {
        /* 가용 블록의 앞부분부터 asize만큼 블록 분할 및 할당 후 나머지 뒷부분 가용블록으로 추가 */
        PUT(HDRP(bp), PACK(asize, 1)); 
        PUT(FTRP(bp), PACK(asize, 1)); 
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remainder, 0)); 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remainder, 0)); 
        insert_node(NEXT_BLKP(bp), remainder);
    }
    return bp;
}


//////////////////////////////////////// End of Helper functions ////////////////////////////////////////



/* 
 * mm_init - 할당기 초기화 
 */
int mm_init(void)
{
    int list;         
    char *heap_start; /* 힙 시작 포인터 */
    
    /* segregated free lists 초기화 */
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    /* 초기 빈 힙 할당 */
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;
    
    PUT(heap_start, 0);                            /* Alignment padding */
    PUT(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_start + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    
    /* heap을 INITCHUNKSIZE 바이트로 확장 후 초기 가용 블록 생성 */
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
    
    return 0;
}

/* 
 * mm_malloc - size 바이트의 메모리 블록 할당 요청   
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* 적절한 블록 크기 */
    size_t extendsize;  /* 적합하지 않을 경우 확장할 힙 사이즈 */
    void *bp = NULL;
    
    /* 거짓 요청시 */
    if (size == 0)
        return NULL;
    
    /* 헤더와 풋터 위한 공간 확보 및 더블 워드 요건 만족시킴 */
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size+DSIZE);
    }
    
    int list = 0; 
    size_t searchsize = asize;
    /* seglist에서 가용 블록 찾기 */
    while (list < LISTLIMIT) {
        /* seglist의 마지막이거나, (할당받으려는 크기가 1보다 작으면서 seglist의 현재 인덱스(길이) 클래스의 가용 리스트가 있으면) */ 
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            /* 현재 길이 클래스의 가용 리스트 */ 
            bp = segregated_free_lists[list];

            /* 현재 길이 클래스의 가용 리스트가 존재하고, 할당하려는 블록 크기가 현재 길이 클래스보다 크지 않을 때까지 */
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp)))))
            {
                bp = PRED(bp);  
            }
            if (bp != NULL)
                break;
        }
        
        searchsize >>= 1;
        list++;
    }
    
    /* 가용 블록을 찾지 못하면, extend heap */
    if (bp == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);   
        if ((bp = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    
    /* 맞는 가용 블록 찾으면 요청한 블록을 배치, 옵션으로 추가 부분 분할 */
    bp = place(bp, asize);
    
    /* 새로 할당된 블록의 ptr return */
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
    
    insert_node(bp, size);
    coalesce(bp);
    
    return;
}

/*
 * mm_realloc - 동적 할당된 메모리 내용 유지하며 할당된 메모리 크기 변경
 */
void *mm_realloc(void *bp, size_t size)
{
    void *new_bp = bp;      /* return할 ptr */
    size_t new_size = size; /* 요청한 realloc 크기 */
    int remainder;          /* 적절한 블록 크기 */
    int extendsize;         /* 힙 확장 크기 */
    
    /* 거짓 요청시 */
    if (size == 0)
        return NULL;
    
    /* 헤더와 풋터 위한 공간 확보 및 더블 워드 요건 만족시킴 */
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }

    /* 다음 블록이 가용 블록이거나 에필로그 블록인지 확인 */
    if (!GET_ALLOC(HDRP(NEXT_BLKP(bp))) || !GET_SIZE(HDRP(NEXT_BLKP(bp)))) {
        remainder = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp))) - new_size;
        if (remainder < 0) {
            extendsize = MAX(-remainder, CHUNKSIZE);
            if (extend_heap(extendsize) == NULL)
                return NULL;
            remainder += extendsize;
        }
        
        delete_node(NEXT_BLKP(bp));   /* 분할된 채 가용 seglist에 들어있는 다음 블록 삭제 */ 
        
        PUT(HDRP(bp), PACK(new_size + remainder, 1));
        PUT(FTRP(bp), PACK(new_size + remainder, 1)); 
    } else {
        new_bp = mm_malloc(new_size - DSIZE);  
        memcpy(new_bp, bp, size); 
        mm_free(bp);
    }
    return new_bp;
}