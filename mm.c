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
#include <limits.h>

#include "mm.h"
#include "memlib.h"


static void place(void *, size_t );

static void *find_best_fit(size_t );

static void *coalesce(void *);

static void *extend_heap(size_t );

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team 6",
    /* First member's full name */
    "Choi GwangMin",
    /* First member's email address */
    "ckm7907cb@gmail.com",
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

/* Custom define */
// word and header footer 사이즈를 byte로.
#define WSIZE 4
// double word size를 byte로
#define DSIZE 8
// heap을 늘릴 때 얼만큼 늘릴거냐? 4kb 분량.
#define CHUNKSIZE (1<<12)

// x,y 중 큰 값을 가진다.
#define MAX(x,y) ((x) > (y)? (x) : (y))

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산), 헤더에서 써야하기 때문에 만듬
#define PACK(size, alloc) ((size) | (alloc))

/* address p위치에 words를 read와 write를 한다. */
// 포인터를 써서 p를 참조한다. 주소와 값(값에는 다른 블록의 주소를 담는다.)를 알 수 있다.
// 다른 블록을 가리키거나 이동할 때 쓸 수 있다.
#define GET(p)      (*(unsigned int *)(p))
// 블록의 주소를 담는다. 위치를 담아야지 나중에 헤더나 푸터를 읽어서 이동 혹은 연결할 수 있다.
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* adress p위치로부터 size를 읽고 field를 할당 */
// '~'은 역수니까 1111_1000이 됨. 비트 연산하면 000 앞에거만 가져올 수 있음. 즉, 헤더에서 블록 size만 가져오겠다.
#define GET_SIZE(p)     (GET(p) & ~0x7)
// 0000_0001이 됨. 헤더에서 가용여부만 가져오겠다.
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* given block ptr bp, header와 footer의 주소를 계산 */
// bp가 어디에있던 상관없이 WSIZE 앞에 위치한다.
#define HDRP(bp)        ((char *)(bp) - WSIZE)
// 헤더의 끝 지점부터 GET SIZE(블록의 사이즈)만큼 더한 다음 word를 2번 빼는게(그 뒤 블록의 헤드에서 앞으로 2번) footer의 시작 위치가 된다.
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* GIVEN Block ptr bp, 이전 블록과 다음 블록의 주소를 계산 */
// 그 다음 블록의 bp 위치로 이동한다.(bp에서 해당 블록의 크기만큼 이동 -> 그 다음 블로그이 헤더 뒤로 감.)
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
// 그 전 블록의 bp 위치로 이동. (이전 블록 footer로 이동하면 그 전 블록의 사이즈를 알 수 있으니 그만큼 그 전으로 이동.)
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))
static char *heap_listp; // 처음에 쓸 큰 가용블록 힙을 만들어줌

/* 
 * mm_init - initialize the malloc package.
 * 최초 가용 블록으로 힙 생성하기
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    // alignment : heap_listp 첫번째는 0 (패딩)
    PUT(heap_listp, 0);
    // Prologue header : heap_listp + 4byte 에는 header 저장 (DSIZE, 1)
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    // Prologue footer : heap_listp + 8byte 에는 footer 저장 (header와 같음) footer은 header와 같은 양식
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    // Epilogue header : heap_listp + 12byte 에는 마지막을 알려주는 size: 0, allocate : 1
    PUT(heap_listp + (3*WSIZE), PACK(0,1));
    // heap_listp(나중에 bp) 가 가리키는 부분은 header와 footer의 중간으로 지정.
    heap_listp += (2*WSIZE);

    // 두 가지 다른 경우에 호출
    // 1. 힙이 초기화 될때, 2. mm_malloc이 적당한 맞춤 fit을 찾지 못할때 -이해중
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

// 새 가용 블록으로 힙 확장하기
static void *extend_heap(size_t words)
{
    // 요청한 크기를 인접 2워드의 배수로 반올림을 하여, 그 후에 추가적인 힙 공간 요청
    char *bp;
    size_t size;

    // 요청한 크기를 2워드의 배수로 반올림하고 추가 힙 공간을 요청함.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // size가 짝수여야 하는 것을 확정(명시적으로 알려주기 위해 쓰임. 거의 주석(안쓰임 무조건 words는 짝수여서))
    if ((int)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    // 확장한 공간의 -WSIZE를 하면 새로 확장한 header의 주소에 size, 0 (no 할당)
    PUT(HDRP(bp), PACK(size, 0));
    // 확장한 공간의 공간만큼 이동후 -DWIZE를 하면 새로 확장한 footer 주소에 size, 0
    PUT(FTRP(bp), PACK(size, 0));
    // 헤더의 사이즈만큼 이동 후 - WSIZE 만큼 뒤로 가면 확장한 크기의 마지막 부분 word에 EP를 다시 넣는다.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    // 전 블록의 footer의 allocate 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // 다음 블록의 header의 allocate 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 현재 블록의 사이즈 확인
    size_t size = GET_SIZE(HDRP(bp));

    // 전 블록의 footer의 allocate가 1이고 다음 블록의 header의 allocate가 1이라면
    if (prev_alloc && next_alloc){
        // 그냥 bp 리턴(똑같은거 다시 돌려보네주기)
        return bp;
    }

    // 전블록의 footer의 allocate가 1이고 다음 블록의 header의 allocate가 0이라면
    else if (prev_alloc && !next_alloc){
        // 현재 블록 사이즈에 다음 헤더의 블록 사이즈만큼 추가
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // 현재 헤더에 더한 size 더한 값 집어넣기
        PUT(HDRP(bp), PACK(size,0));
        // 이때 전에서 헤더의 사이즈가 바뀌었으니 footer의 위치는 후의 블록의 사이즈만큼 더 멀것이다.
        // 현재 푸터에 더한 size 더한 값 집어 넣기
        PUT(FTRP(bp), PACK(size,0));
    }

    // 전블록의 footer의 allocate가 0이고 다음 블록의 header의 allocate가 1이라면
    else if (!prev_alloc && next_alloc){
        // 현재 블록 사이즈에 이전 헤더의 블록 사이즈 만큼 추가
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        // 현재 footer의 사이즈 재조정 후 allocate 0으로 조정
        PUT(FTRP(bp), PACK(size, 0));
        // 이전 header의 사이즈 재조정 후 allocate 0으로 조정
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        // 이전의 헤더 WSIZE 추가의 포인터를 bp로 설정
        bp = PREV_BLKP(bp);
    }

    // 전 블록의 footer와 다음 블록의 header의 allocate가 둘다 0이라면
    else {
        // 사이즈를 이전 블록의 사이즈와 이후 블록의 사이즈를 더함. 총(이전+현재+다음) 블록 사이즈
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        // 전 블록의 헤더에 사이즈를 바꿔줌
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        // 이때 전에서 헤더의 사이즈가 바뀌었으니 footer의 위치는 후의 블록의 사이즈만큼 더 멀것이다.
        // 현재 푸터에 더한 size 더한 값 집어 넣기
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        // 이전의 헤더 WSIZE 추가의 포인터를 bp로 설정
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    //현재 bp의 사이즈를 가져옴(size)
    size_t size = GET_SIZE(HDRP(bp));

    //헤더의 allocate를 0으로 설정
    PUT(HDRP(bp), PACK(size,0));
    //푸터의 allocate를 0으로 설정
    PUT(FTRP(bp), PACK(size,0));
    // case 별로 확인해서 allocate 설정
    coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    // 가져온 size가 0이면 null
    if (size == 0)
        return NULL;

    // 사이즈가 8byte보다 작으면
    if (size <= DSIZE)
        // asize를 16byte로 설정 (이것이 header(4) + payload+paging(8) + footer(4))
        asize = 2*DSIZE;
    
    // 8byte보다 크다면?
    else
        //asize를 8 * ((size + 8 + 7) / 8)
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/DSIZE);
    
    // 들어갈 위치를 찾았다면
    if ((bp = find_best_fit(asize)) != NULL){
        // bp에 asize만큼 할당하기.
        place(bp, asize);
        return bp;
    }

    // 적절한 값이 들어갈 위치를 찾지 못했다면, 사이즈 늘려주기.
    // 늘려줄 size는 asize와 CHUNKSIZE를 비교해서 더 큰 값으로 늘려주기.
    extendsize = MAX(asize, CHUNKSIZE);
    // extendsize만큼 늘려주고 bp 체크
    if ((bp = extend_heap(extendsize/WSIZE))==NULL)
        return NULL;
    // 늘려준뒤 bp에 asize 할당
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

static void *find_best_fit(size_t asize)
{
    void *bp;
    void *tmp_bp;
    size_t tmp_size = ULONG_MAX;

    // bp는 heaplistp, 얻은 사이즈가 0보다 클때까지, bp는 다음 블록으로
    for (bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)){
        // 만약 확인하는 블록에 할당이 안되있고, asize보다 크기가 더 크다면,
        if(!GET_ALLOC(HDRP(bp))&&(asize <= GET_SIZE(HDRP(bp))&&(tmp_size>GET_SIZE(HDRP(bp))))){
            tmp_size = GET_SIZE(HDRP(bp));
            tmp_bp = bp;
        }
    }
    if (tmp_size != ULONG_MAX){
        return tmp_bp;
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    // 현재 사이즈 설정 (그게 그말(말이 마음이고 마음이 말이다))
    size_t csize = GET_SIZE(HDRP(bp));

    // (현재 사이즈 - 넣을 사이즈) 가 16byte보다 크다면
    if ((csize - asize) >= (2*DSIZE)){
        // bp의 헤더를 asize로 변경
        PUT(HDRP(bp),PACK(asize, 1));
        // bp의 footer을 asize로 변경
        PUT(FTRP(bp), PACK(asize,1));
        // 다음 블록으로 이동
        bp = NEXT_BLKP(bp);
        // 다음 블록의 헤더와 푸터를 지정
        PUT(HDRP(bp), PACK(csize-asize,0));
        PUT(FTRP(bp),PACK(csize-asize,0));
    }
    // csize와 asize가 완전히 크기가 같다면
    else{
        // 그냥~ 그 부분의 헤더와 푸터를 1로 바꿔버림.
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // 처음 가리키는 포인터를 oldptr로 저장.
    void *oldptr = ptr;
    // 새로운 포인터 생성.
    void *newptr;
    size_t copySize;
    
    // 사이즈만큼 새로 만든 포인터의 bp를 newptr로 지정.
    newptr = mm_malloc(size);
    // 만약 malloc을 한 bp의 값이 null 라면
    if (newptr == NULL)
      return NULL;
    // oldptr로 저장했던 헤더의 사이즈를 찾아서 copySize로 저장.
    copySize = GET_SIZE(HDRP(oldptr));    //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE); (원래 책에는 이렇게 써져있었음.)
    
    // 만약 copySize가 넘겨받은 size보다 크다면
    if (size < copySize)
        // copySize를 size로 바꿔주기.
        copySize = size;
    
    //새로운 포인터에 복사할 대상(oldptr)과 copySize만큼 복사합니다.
    memcpy(newptr, oldptr, copySize);
    // 전에 있던 블록의 할당은 0으로
    mm_free(oldptr);
    return newptr;
}