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

/*

We will be using an explicit bidirectional list allocation. 
The fitting policy is first fit. We will use immediate coalescing.

*/

/*
MACROS (the #defines)
// Get and set will be used since we have so many void pointers flying around
get - get the address stored at a pointer
set - set the value to a pointer
pack - bitwise operation to merge size and allocated bit


FUNCTIONS (actual functions)
coalesce function - checks all cases and coalesces accordingly
heap checker - make sure alles gut
first fitter - to find the free block to fit, else return end of heap/extend heap accordingly
extend heap - increase size of heap according to how request from malloc, return pointer. 
allocate free - given pointer to free block, allocates that and splits remainder of free block. hi ! 
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
    "603B",
    /* First member's full name */
    "Brian Shin",
    /* First member's email address */
    "shs522@nyu.edu",
    /* Second member's full name (leave blank if none) */
    "Navya Suri",
    /* Second member's email address (leave blank if none) */
    "ns3774@nyu.edu"};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

#define DSIZE 8
#define WSIZE 4
#define CHUNKSIZE 4096

#define MINIMUM 12

#define MAX(a, b) ((a > b) ? a : b)

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
// MACROS defined below - we got these from the text book

// Packs the size and the allocated bit into one word
// bitwise 'or' operation
#define PACK(size, alloc) ((size) | alloc)

// GET returns the word at address of p
// PUT sets a value to the pointer p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// Read the size and allocaated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

// #define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))

// Next Free Block, Previous Free Block
// The way it works - get the address of ptr, add 8 to it. Then return a pointer to this address.
#define NFB(ptr) (*(char **)((char *)ptr + WSIZE))
#define PFB(ptr) (*(char **)(char *)ptr)

// FUNCTION DECLARTIONS
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void insertfree(char *p);
static void deleteblock(char *lp);

// GLOBAL VARIABLES
char *heap_pointer;
char *list_pointer;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap(free list) */
    if ((heap_pointer = mem_sbrk(6 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_pointer, 0);                              /* Alignment padding */
    PUT(heap_pointer + (1 * WSIZE), PACK(MINIMUM, 1)); /* Prologue header */
    PUT(heap_pointer + (2 * WSIZE), 0);                /* Previous pointer */
    PUT(heap_pointer + (3 * WSIZE), 0);                /* Next Pointer */

    PUT(heap_pointer + MINIMUM + WSIZE, PACK(MINIMUM, 1)); /* Prologue footer */
    PUT(heap_pointer + MINIMUM + WSIZE * 2, PACK(0, 1));   /* Epilogue Header */

    list_pointer = heap_pointer + 2*WSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize, extendsize;
    char *p;

    if (heap_pointer == 0)
    {
        mm_init();
    }

    if (size == 0)
    {
        return NULL;
    }

    if (size <= WSIZE)
        asize = 2 * WSIZE;
    else
        asize = WSIZE * ((size + WSIZE + WSIZE - 1) / WSIZE);

    p = find_fit(asize);
    if (p != NULL)
    {
        place(p, asize);
        return p;
    }

    // Calculate how much to extend
    extendsize = MAX(asize, CHUNKSIZE);
    p = extend_heap(extendsize / WSIZE);
    if (p == NULL)
        return NULL;

    // Set the block header and return the pointer
    place(p, asize);
    return p;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *extend_heap(size_t words)
{
    char *ptr;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (size < MINIMUM)
        size = MINIMUM;
    if ((long)(ptr = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(ptr), PACK(size, 0));         /* Free block header */
    PUT(FTRP(ptr), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(ptr);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc;
    if (PREV_BLKP(bp) == bp)
        prev_alloc = 1;
    prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t bsize = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        // Nothing to do if both neighbors are allocated
        ;
    }

    else if (prev_alloc && !next_alloc)
    {
        printf("Case 2");
        bsize += GET_SIZE(HDRP(NEXT_BLKP(bp))); //increase the size
        deleteblock(NEXT_BLKP(bp));             // delete next block
        PUT(HDRP(bp), PACK(bsize, 0));          // change the header to the new size
        PUT(FTRP(bp), PACK(bsize, 0));          // change the footer to the new size
    }

    else if (!prev_alloc && next_alloc)
    {
        printf("Case 3");
        bsize += GET_SIZE(HDRP(PREV_BLKP(bp)));
        deleteblock(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(bsize, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(bsize, 0));
        bp = PREV_BLKP(bp);
    }

    else if (!prev_alloc && !next_alloc)
    {
        printf("Case 4");
        bsize += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                 GET_SIZE(FTRP(NEXT_BLKP(bp)));
        deleteblock(NEXT_BLKP(bp));
        deleteblock(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(bsize, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(bsize, 0));
        bp = PREV_BLKP(bp);
    }

    /* Insert Coalesced block in free list */
    insertfree(bp);

    return bp;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * WSIZE))
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

// LIST Functions - insert free block, given its pointer

static void insertfree(char *p)
{
    // we always insert to the beginning of the list

    if (list_pointer == NULL)
    {
        // put the previous to null and next to null and set list to point to p
        PFB(p) = NULL;
        NFB(p) = NULL;
        list_pointer = p;
        return; // end here (i forgot this and we had to debug for a long while)
    }

    // list pointer points to a node. make the current pointer point to this node and reset the head
    NFB(p) = list_pointer; // the next block of the current should be the current head
    PFB(list_pointer) = p; // the previous block of the current head should be the new p
    PFB(p) = NULL;         // the previous block of the current p should be null, since it will be the new head
    list_pointer = p;      // reset the head
}

// remove free block: (1) First Block (2) Middle Block (3) Last Block

static void deleteblock(char *lp)
{
    // Check what type of block lp is: (1) Only Block (2) First Block (3) Middle Block (4) Last Block)

    // Return when Free List is Empty
    if (list_pointer == 0)
    {
        return;
    }

    // Case 1: (1) Only Block

    else if ((PFB(lp) == NULL) && (NFB(lp) == NULL))
    {
        list_pointer = 0;
    }

    // Case 2: (2) First Block

    else if ((PFB(lp) == NULL) && (NFB(lp) != NULL))
    {
        list_pointer = NFB(lp);
        PFB(list_pointer) = NULL;
    }

    // Case 3: (3) Middle Block

    else if ((PFB(lp) != NULL) && (NFB(lp) != NULL))
    {
        PFB(&NFB(lp)) = PFB(lp);
        NFB(&PFB(lp)) = NFB(lp);
    }

    // Case 4: (4) Last Block

    else if ((PFB(lp) != NULL) && (NFB(lp) == NULL))
    {
        NFB(&PFB(lp)) = NULL;
    }
}

static void *find_fit(size_t size)
{

    // traverse through the free list and return at the first time you find a block that can be allocated
    char *it = list_pointer;

    while (it != NULL)
    {
        // void *ad = *(it) + WSIZE;

        // return pointer if the size is enough
        // char* x = it+WSIZE;
        if (GET_SIZE(HDRP(it)) >= size) // PROBLEM HERE MUST FIX
        {
            return it;
        }

        // If the current one is not big enough, then traverse to the next
        it = NFB(it);
    }

    // It hasn't returned meaning that there is no free block in the list
    return NULL;

    // originally, we extended the heap and returned a new pointer here, but the book did the opposite.
    // we changed our code to follow the way the book does it.
    // Extend heap function
}