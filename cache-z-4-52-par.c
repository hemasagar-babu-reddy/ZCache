/* cache.c - cache module routines */

/* SimpleScalar(TM) Tool Suite
 * Copyright (C) 1994-2003 by Todd M. Austin, Ph.D. and SimpleScalar, LLC.
 * All Rights Reserved. 
 * 
 * THIS IS A LEGAL DOCUMENT, BY USING SIMPLESCALAR,
 * YOU ARE AGREEING TO THESE TERMS AND CONDITIONS.
 * 
 * No portion of this work may be used by any commercial entity, or for any
 * commercial purpose, without the prior, written permission of SimpleScalar,
 * LLC (info@simplescalar.com). Nonprofit and noncommercial use is permitted
 * as described below.
 * 
 * 1. SimpleScalar is provided AS IS, with no warranty of any kind, express
 * or implied. The user of the program accepts full responsibility for the
 * application of the program and the use of any results.
 * 
 * 2. Nonprofit and noncommercial use is encouraged. SimpleScalar may be
 * downloaded, compiled, executed, copied, and modified solely for nonprofit,
 * educational, noncommercial research, and noncommercial scholarship
 * purposes provided that this notice in its entirety accompanies all copies.
 * Copies of the modified software can be delivered to persons who use it
 * solely for nonprofit, educational, noncommercial research, and
 * noncommercial scholarship purposes provided that this notice in its
 * entirety accompanies all copies.
 * 
 * 3. ALL COMMERCIAL USE, AND ALL USE BY FOR PROFIT ENTITIES, IS EXPRESSLY
 * PROHIBITED WITHOUT A LICENSE FROM SIMPLESCALAR, LLC (info@simplescalar.com).
 * 
 * 4. No nonprofit user may place any restrictions on the use of this software,
 * including as modified by the user, by any other authorized user.
 * 
 * 5. Noncommercial and nonprofit users may distribute copies of SimpleScalar
 * in compiled or executable form as set forth in Section 2, provided that
 * either: (A) it is accompanied by the corresponding machine-readable source
 * code, or (B) it is accompanied by a written offer, with no time limit, to
 * give anyone a machine-readable copy of the corresponding source code in
 * return for reimbursement of the cost of distribution. This written offer
 * must permit verbatim duplication by anyone, or (C) it is distributed by
 * someone who received only the executable form, and is accompanied by a
 * copy of the written offer of source code.
 * 
 * 6. SimpleScalar was developed by Todd M. Austin, Ph.D. The tool suite is
 * currently maintained by SimpleScalar LLC (info@simplescalar.com). US Mail:
 * 2395 Timbercrest Court, Ann Arbor, MI 48105.
 * 
 * Copyright (C) 1994-2003 by Todd M. Austin, Ph.D. and SimpleScalar, LLC.
 */


#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include "host.h"
#include "misc.h"
#include "machine.h"
#include "cache.h"

/* cache access macros */
#define CACHE_TAG(cp, addr)	((addr) >> (cp)->tag_shift)
#define CACHE_SET(cp, addr)	(((addr) >> (cp)->set_shift) & (cp)->set_mask)
#define CACHE_BLK(cp, addr)	((addr) & (cp)->blk_mask)
#define CACHE_TAGSET(cp, addr)	((addr) & (cp)->tagset_mask)

/* extract/reconstruct a block address */
#define CACHE_BADDR(cp, addr)	((addr) & ~(cp)->blk_mask)
#define CACHE_MK_BADDR(cp, tag, set)					\
  (((tag) << (cp)->tag_shift)|((set) << (cp)->set_shift))

/* index an array of cache blocks, non-trivial due to variable length blocks */
#define CACHE_BINDEX(cp, blks, i)					\
  ((struct cache_blk_t *)(((char *)(blks)) +				\
			  (i)*(sizeof(struct cache_blk_t) +		\
			       ((cp)->balloc				\
				? (cp)->bsize*sizeof(byte_t) : 0))))

/* cache data block accessor, type parameterized */
#define __CACHE_ACCESS(type, data, bofs)				\
  (*((type *)(((char *)data) + (bofs))))

/* cache data block accessors, by type */
#define CACHE_DOUBLE(data, bofs)  __CACHE_ACCESS(double, data, bofs)
#define CACHE_FLOAT(data, bofs)	  __CACHE_ACCESS(float, data, bofs)
#define CACHE_WORD(data, bofs)	  __CACHE_ACCESS(unsigned int, data, bofs)
#define CACHE_HALF(data, bofs)	  __CACHE_ACCESS(unsigned short, data, bofs)
#define CACHE_BYTE(data, bofs)	  __CACHE_ACCESS(unsigned char, data, bofs)

/*cache block hashing macros, this macro is used to index into a cache
   set hash table (to find the correct block on N in an N-way cache), the
   cache set index function is CACHE_SET, defined above */
#define CACHE_HASH(cp, key)					\
  (((key >> 24) ^ (key >> 16) ^ (key >> 8) ^ key) % cp->nsets)
#define CACHE_HASH1(cp, key)			\
  (((key >> 4) ^ (key >> 2) ^ key))
#define CACHE_HASH2(cp, key)						\
  (((key >> 3) ^ key))
#define CACHE_HASH3(cp, key)						\
  (((key >> 2) ^ key))
#define CACHE_HASH4(cp, key)						\
  (((key >> 5) ^ (key >> 1) ^ key))

/*#define CACHE_HASH1(cp, key)				\
  (((key >> 24) ^ (key >> 12) ^ (key>>6) ^ key))
#define CACHE_HASH2(cp, key)						\
  (((key >> 32) ^ (key >> 16) ^ (key>>8) ^ key))
#define CACHE_HASH3(cp, key)						\
  (((key >> 20) ^ (key >> 10) ^ (key >> 5) ^ key))
#define CACHE_HASH4(cp, key)						\
  (((key >> 18) ^ (key >> 9) ^ (key >> 1) ^ key))
*/
/*#define CACHE_HASH1(cp, key)			\
  (((key+43) ^ key))
#define CACHE_HASH2(cp, key)						\
  (((key+317) ^ key))
#define CACHE_HASH3(cp, key)						\
  (((key+713) ^ key))
#define CACHE_HASH4(cp, key)						\
((key+87))*/
 /*#define CACHE_HASH1(cp, key)			\
  ((key))
#define CACHE_HASH2(cp, key)						\
  ((key))
#define CACHE_HASH3(cp, key)						\
  ((key))
#define CACHE_HASH4(cp, key)						\
  ((key))
 */


/* copy data out of a cache block to buffer indicated by argument pointer p */
#define CACHE_BCOPY(cmd, blk, bofs, p, nbytes)	\
  if (cmd == Read)							\
    {									\
      switch (nbytes) {							\
      case 1:								\
	*((byte_t *)p) = CACHE_BYTE(&blk->data[0], bofs); break;	\
      case 2:								\
	*((half_t *)p) = CACHE_HALF(&blk->data[0], bofs); break;	\
      case 4:								\
	*((word_t *)p) = CACHE_WORD(&blk->data[0], bofs); break;	\
      default:								\
	{ /* >= 8, power of two, fits in block */			\
	  int words = nbytes >> 2;					\
	  while (words-- > 0)						\
	    {								\
	      *((word_t *)p) = CACHE_WORD(&blk->data[0], bofs);	\
	      p += 4; bofs += 4;					\
	    }\
	}\
      }\
    }\
  else /* cmd == Write */						\
    {									\
      switch (nbytes) {							\
      case 1:								\
	CACHE_BYTE(&blk->data[0], bofs) = *((byte_t *)p); break;	\
      case 2:								\
        CACHE_HALF(&blk->data[0], bofs) = *((half_t *)p); break;	\
      case 4:								\
	CACHE_WORD(&blk->data[0], bofs) = *((word_t *)p); break;	\
      default:								\
	{ /* >= 8, power of two, fits in block */			\
	  int words = nbytes >> 2;					\
	  while (words-- > 0)						\
	    {								\
	      CACHE_WORD(&blk->data[0], bofs) = *((word_t *)p);		\
	      p += 4; bofs += 4;					\
	    }\
	}\
    }\
  }

/* bound sqword_t/dfloat_t to positive int */
#define BOUND_POS(N)		((int)(MIN(MAX(0, (N)), 2147483647)))

/* unlink BLK from the hash table bucket chain in SET */
static void
unlink_htab_ent(struct cache_t *cp,		/* cache to update */
		struct cache_set_t *set,	/* set containing bkt chain */
		struct cache_blk_t *blk)	/* block to unlink */
{
  struct cache_blk_t *prev, *ent;
  int index = CACHE_HASH(cp, blk->tag);

  /* locate the block in the hash table bucket chain */
  for (prev=NULL,ent=set->hash[index];
       ent;
       prev=ent,ent=ent->hash_next)
    {
      if (ent == blk)
	break;
    }
  assert(ent);

  /* unlink the block from the hash table bucket chain */
  if (!prev)
    {
      /* head of hash bucket list */
      set->hash[index] = ent->hash_next;
    }
  else
    {
      /* middle or end of hash bucket list */
      prev->hash_next = ent->hash_next;
    }
  ent->hash_next = NULL;
}

/* insert BLK onto the head of the hash table bucket chain in SET */
static void
link_htab_ent(struct cache_t *cp,		/* cache to update */
	      struct cache_set_t *set,		/* set containing bkt chain */
	      struct cache_blk_t *blk)		/* block to insert */
{
  int index = CACHE_HASH(cp, blk->tag);

  /* insert block onto the head of the bucket chain */
  blk->hash_next = set->hash[index];
  set->hash[index] = blk;
}

/* where to insert a block onto the ordered way chain */
enum list_loc_t { Head, Tail };

/* insert BLK into the order way chain in SET at location WHERE */
static void
update_way_list(struct cache_set_t *set,	/* set contained way chain */
		struct cache_blk_t *blk,	/* block to insert */
		enum list_loc_t where)		/* insert location */
{
  /* unlink entry from the way list */
  if (!blk->way_prev && !blk->way_next)
    {
      /* only one entry in list (direct-mapped), no action */
      assert(set->way_head == blk && set->way_tail == blk);
      /* Head/Tail order already */
      return;
    }
  /* else, more than one element in the list */
  else if (!blk->way_prev)
    {
      assert(set->way_head == blk && set->way_tail != blk);
      if (where == Head)
	{
	  /* already there */
	  return;
	}
      /* else, move to tail */
      set->way_head = blk->way_next;
      blk->way_next->way_prev = NULL;
    }
  else if (!blk->way_next)
    {
      /* end of list (and not front of list) */
      assert(set->way_head != blk && set->way_tail == blk);
      if (where == Tail)
	{
	  /* already there */
	  return;
	}
      set->way_tail = blk->way_prev;
      blk->way_prev->way_next = NULL;
    }
  else
    {
      /* middle of list (and not front or end of list) */
      assert(set->way_head != blk && set->way_tail != blk);
      blk->way_prev->way_next = blk->way_next;
      blk->way_next->way_prev = blk->way_prev;
    }

  /* link BLK back into the list */
  if (where == Head)
    {
      /* link to the head of the way list */
      blk->way_next = set->way_head;
      blk->way_prev = NULL;
      set->way_head->way_prev = blk;
      set->way_head = blk;
    }
  else if (where == Tail)
    {
      /* link to the tail of the way list */
      blk->way_prev = set->way_tail;
      blk->way_next = NULL;
      set->way_tail->way_next = blk;
      set->way_tail = blk;
    }
  else
    panic("bogus WHERE designator");
}

/* create and initialize a general cache structure */
struct cache_t *			/* pointer to cache created */
cache_create(char *name,		/* name of the cache */
	     int nsets,			/* total number of sets in cache */
	     int bsize,			/* block (line) size of cache */
	     int balloc,		/* allocate data space for blocks? */
	     int usize,			/* size of user data to alloc w/blks */
	     int assoc,			/* associativity of cache */
	     enum cache_policy policy,	/* replacement policy w/in sets */
	     /* block access function, see description w/in struct cache def */
	     unsigned int (*blk_access_fn)(enum mem_cmd cmd,
					   md_addr_t baddr, int bsize,
					   struct cache_blk_t *blk,
					   tick_t now),
	     unsigned int hit_latency)	/* latency in cycles for a hit */
{
  struct cache_t *cp;
  struct cache_blk_t *blk;
  int i, j, bindex, h0, h1, h2, h3;
  md_addr_t ta, ha;
  /* check all cache parameters */
  if (nsets <= 0)
    fatal("cache size (in sets) `%d' must be non-zero", nsets);
  if ((nsets & (nsets-1)) != 0)
    fatal("cache size (in sets) `%d' is not a power of two", nsets);
  /* blocks must be at least one datum large, i.e., 8 bytes for SS */
  if (bsize < 8)
    fatal("cache block size (in bytes) `%d' must be 8 or greater", bsize);
  if ((bsize & (bsize-1)) != 0)
    fatal("cache block size (in bytes) `%d' must be a power of two", bsize);
  if (usize < 0)
    fatal("user data size (in bytes) `%d' must be a positive value", usize);
  if (assoc <= 0)
    fatal("cache associativity `%d' must be non-zero and positive", assoc);
  if ((assoc & (assoc-1)) != 0)
    fatal("cache associativity `%d' must be a power of two", assoc);
  if (!blk_access_fn)
    fatal("must specify miss/replacement functions");

  /* allocate the cache structure */
  cp = (struct cache_t *)
    calloc(1, sizeof(struct cache_t) + (nsets-1)*sizeof(struct cache_set_t));
  if (!cp)
    fatal("out of virtual memory");

  /* initialize user parameters */
  cp->name = mystrdup(name);
  cp->nsets = nsets;
  cp->bsize = bsize;
  cp->balloc = balloc;
  cp->usize = usize;
  cp->assoc = assoc;
  cp->policy = policy;
  cp->hit_latency = hit_latency;

  /* miss/replacement functions */
  cp->blk_access_fn = blk_access_fn;

  /* compute derived parameters */
  cp->hsize = CACHE_HIGHLY_ASSOC(cp) ? (assoc >> 2) : 0;
  cp->blk_mask = bsize-1;
  cp->set_shift = log_base2(bsize);
  cp->set_mask = nsets-1;
  cp->tag_shift = cp->set_shift + log_base2(nsets);
  cp->tag_mask = (1 << (32 - cp->tag_shift))-1;
  cp->tagset_mask = ~cp->blk_mask;
  cp->bus_free = 0;

  /* print derived parameters during debug */
  debug("%s: cp->hsize     = %d", cp->name, cp->hsize);
  debug("%s: cp->blk_mask  = 0x%08x", cp->name, cp->blk_mask);
  debug("%s: cp->set_shift = %d", cp->name, cp->set_shift);
  debug("%s: cp->set_mask  = 0x%08x", cp->name, cp->set_mask);
  debug("%s: cp->tag_shift = %d", cp->name, cp->tag_shift);
  debug("%s: cp->tag_mask  = 0x%08x", cp->name, cp->tag_mask);

  /* initialize cache stats */
  cp->hits = 0;
  cp->misses = 0;
  cp->replacements = 0;
  cp->writebacks = 0;
  cp->invalidations = 0;

  /* blow away the last block accessed */
  cp->last_tagset = 0;
  cp->last_blk = NULL;

  /* allocate data blocks */
  cp->data = (byte_t *)calloc(nsets * assoc,
			      sizeof(struct cache_blk_t) +
			      (cp->balloc ? (bsize*sizeof(byte_t)) : 0));
  if (!cp->data)
    fatal("out of virtual memory");
  /* slice up the data blocks */
  for (bindex=0,i=0; i<nsets; i++)
    {
      cp->sets[i].way_head = NULL;
      cp->sets[i].way_tail = NULL;
      cp->sets[i].way_one = NULL;
      cp->sets[i].way_two = NULL;
      cp->sets[i].way_three = NULL;
      cp->sets[i].way_four = NULL;
      /* get a hash table, if needed */
      if (cp->hsize)
	{
	  cp->sets[i].hash =
	    (struct cache_blk_t **)calloc(cp->hsize,
					  sizeof(struct cache_blk_t *));
	  if (!cp->sets[i].hash)
	    fatal("out of virtual memory");
	}
      /* NOTE: all the blocks in a set *must* be allocated contiguously,
	 otherwise, block accesses through SET->BLKS will fail (used
	 during random replacement selection) */
      
	cp->sets[i].blks = CACHE_BINDEX(cp, cp->data, bindex);
	if(strcmp(cp->name, "ul2") != 0){
	/* link the data blocks into ordered way chain and hash table bucket
	   chains, if hash table exists */
	  for (j=0; j<assoc; j++){
	    // locate next cache block 
	    blk = CACHE_BINDEX(cp, cp->data, bindex);
	    bindex++;
	      
	    // invalidate new cache block 
	    blk->status = 0;
	    blk->tag = 0;
	    blk->addr = 0;
	    blk->ready = 0;
	    blk->last_access = 0;
	    blk->user_data = (usize != 0
			      ? (byte_t *)calloc(usize, sizeof(byte_t)) : NULL);

	    // insert cache block into set hash table 
	    if (cp->hsize)
	      link_htab_ent(cp, &cp->sets[i], blk);

	    // insert into head of way list, order is arbitrary at this point 
	    blk->way_next = cp->sets[i].way_head;
	    blk->way_prev = NULL;
	    if (cp->sets[i].way_head)
	      cp->sets[i].way_head->way_prev = blk;
	    cp->sets[i].way_head = blk;
	    if (!cp->sets[i].way_tail)
	      cp->sets[i].way_tail = blk;
	  }
      }
      else if(!strcmp(cp->name,"ul2")){
	  if (cp->assoc == 4){
	    /*cp->sets[h0].way_one = cp->sets[i].way_head;
	    cp->sets[h1].way_two = (cp->sets[i].way_head)->way_next;
	    cp->sets[h2].way_three = (cp->sets[i].way_head)->way_next->way_next;
	    cp->sets[h3].way_four = (cp->sets[i].way_tail);*/
	    blk = CACHE_BINDEX(cp, cp->data, bindex);
	    bindex++;
      
	    // invalidate new cache block 
	    blk->status = 0;
	    blk->tag = 0;
	    blk->addr = 0;
	    blk->ready = 0;
	    blk->last_access = 0;
	    blk->user_data = (usize != 0
			      ? (byte_t *)calloc(usize, sizeof(byte_t)) : NULL);
	    
	    // insert cache block into set hash table 
	    if (cp->hsize)
	      link_htab_ent(cp, &cp->sets[i], blk);
	    // insert into head of way list, order is arbitrary at this point 
	    //blk->way_next = (cp->sets[h0].way_two);
	    //blk->way_prev = NULL;
	    cp->sets[i].way_one = blk;
	    //if (cp->sets[i].way_head)
	    //cp->sets[i].way_head->way_prev = blk;
	    //cp->sets[i].way_head = blk;
	    //if (!cp->sets[i].way_tail)
	    // cp->sets[i].way_tail = blk;
	    //cp->sets[i].way_one = cp->sets[i].way_head;
	    

	    // locate next cache block 
	    blk = CACHE_BINDEX(cp, cp->data, bindex);
	    bindex++;
	    
	    // invalidate new cache block 
	    blk->status = 0;
	    blk->tag = 0;
	    blk->addr = 0;
	    blk->ready = 0;
	    blk->last_access = 0;
	    blk->user_data = (usize != 0
			      ? (byte_t *)calloc(usize, sizeof(byte_t)) : NULL);
	    
	    // insert cache block into set hash table 
	    if (cp->hsize)
	      link_htab_ent(cp, &cp->sets[i], blk);
	    
	    // insert into head of way list, order is arbitrary at this point 
	    //blk->way_next = cp->sets[h1].way_three;
	    //blk->way_prev = cp->sets[h1].way_one;
	    cp->sets[i].way_two = blk;
	    //if (cp->sets[i].way_head)
	    // cp->sets[i].way_head->way_prev = blk;
	    //cp->sets[i].way_head = blk;
	    //if (!cp->sets[i].way_tail)
	    // cp->sets[i].way_tail = blk;
	    //cp->sets[i].way_two = (cp->sets[i].way_head)->way_next;
	    
	    // locate next cache block 
	    blk = CACHE_BINDEX(cp, cp->data, bindex);
	    bindex++;
	    
	    // invalidate new cache block 
	    blk->status = 0;
	    blk->tag = 0;
	    blk->addr = 0;
	    blk->ready = 0;
	    blk->last_access = 0;
	    blk->user_data = (usize != 0
			? (byte_t *)calloc(usize, sizeof(byte_t)) : NULL);
	    
	    // insert cache block into set hash table 
	    if (cp->hsize)
	      link_htab_ent(cp, &cp->sets[i], blk);
	    
	    // insert into head of way list, order is arbitrary at this point 
	    //blk->way_next = cp->sets[h2].way_four;
	    //blk->way_prev = cp->sets[h2].way_two;
	    cp->sets[i].way_three = blk;
	    //if (cp->sets[i].way_head)
	    //  cp->sets[i].way_head->way_prev = blk;
	    //cp->sets[i].way_head = blk;
	    //if (!cp->sets[i].way_tail)
	    //  cp->sets[i].way_tail = blk;
	    //cp->sets[i].way_three = (cp->sets[i].way_head)->way_next->way_next;
	    
	    // locate next cache block 
	    blk = CACHE_BINDEX(cp, cp->data, bindex);
	    bindex++;
	    
	    // invalidate new cache block 
	    blk->status = 0;
	    blk->tag = 0;
	    blk->addr = 0;
	    blk->ready = 0;
	    blk->last_access = 0;
	    blk->user_data = (usize != 0
			      ? (byte_t *)calloc(usize, sizeof(byte_t)) : NULL);
	    
	    // insert cache block into set hash table 
	    if (cp->hsize)
	      link_htab_ent(cp, &cp->sets[i], blk);
	    
	    // insert into head of way list, order is arbitrary at this point 
	    //blk->way_next = NULL;
	    //blk->way_prev = cp->sets[h3].way_three;
	    cp->sets[i].way_four = blk;
	    //if (cp->sets[i].way_head)
	    //  cp->sets[i].way_head->way_prev = blk;
	    //cp->sets[i].way_head = blk;
	    //if (!cp->sets[i].way_tail)
	    //  cp->sets[i].way_tail = blk;
	    //cp->sets[i].way_four = (cp->sets[i].way_tail);
	  }
	  else if (cp->assoc == 3){
	    cp->sets[i].way_one = cp->sets[i].way_head;
	    cp->sets[i].way_two = (cp->sets[i].way_head)->way_next;
	    cp->sets[i].way_three = (cp->sets[i].way_tail);
	    cp->sets[i].way_four = (cp->sets[i].way_tail);
	  }
	  else if (cp->assoc == 2){
	    cp->sets[i].way_one = cp->sets[i].way_head;
	    cp->sets[i].way_two = (cp->sets[i].way_tail);
	    cp->sets[i].way_three = (cp->sets[i].way_tail);
	    cp->sets[i].way_four = (cp->sets[i].way_tail);
	  }
	  else if (cp->assoc == 1){
	    cp->sets[i].way_one = cp->sets[i].way_head;
	    cp->sets[i].way_two = (cp->sets[i].way_head);
	    cp->sets[i].way_three = (cp->sets[i].way_head);
	    cp->sets[i].way_four = (cp->sets[i].way_head);
	  }
      }
      // locate next cache block 
      /*     if(assoc != 0){
      blk = CACHE_BINDEX(cp, cp->data, bindex);
      bindex++;
      
      // invalidate new cache block 
      blk->status = 0;
      blk->tag = 0;
      blk->ready = 0;
      blk->user_data = (usize != 0
			    ? (byte_t *)calloc(usize, sizeof(byte_t)) : NULL);

      // insert cache block into set hash table 
      if (cp->hsize)
	link_htab_ent(cp, &cp->sets[i], blk);
      
      // insert into head of way list, order is arbitrary at this point 
      blk->way_next = cp->sets[i].way_head;
      blk->way_prev = NULL;
      if (cp->sets[i].way_head)
	cp->sets[i].way_head->way_prev = blk;
      cp->sets[i].way_head = blk;
      if (!cp->sets[i].way_tail)
	cp->sets[i].way_tail = blk;
      cp->sets[i].way_one = cp->sets[i].way_head;
      

      // locate next cache block 
      blk = CACHE_BINDEX(cp, cp->data, bindex);
      bindex++;
      
      // invalidate new cache block 
      blk->status = 0;
      blk->tag = 0;
      blk->ready = 0;
      blk->user_data = (usize != 0
			? (byte_t *)calloc(usize, sizeof(byte_t)) : NULL);
      
      // insert cache block into set hash table 
      if (cp->hsize)
	link_htab_ent(cp, &cp->sets[i], blk);

      // insert into head of way list, order is arbitrary at this point 
      blk->way_next = cp->sets[i].way_head;
      blk->way_prev = NULL;
      if (cp->sets[i].way_head)
	cp->sets[i].way_head->way_prev = blk;
      cp->sets[i].way_head = blk;
      if (!cp->sets[i].way_tail)
	cp->sets[i].way_tail = blk;
      cp->sets[i].way_two = (cp->sets[i].way_head)->way_next;
	  
      // locate next cache block 
      blk = CACHE_BINDEX(cp, cp->data, bindex);
      bindex++;
      
      // invalidate new cache block 
      blk->status = 0;
      blk->tag = 0;
      blk->ready = 0;
      blk->user_data = (usize != 0
			? (byte_t *)calloc(usize, sizeof(byte_t)) : NULL);

      // insert cache block into set hash table 
      if (cp->hsize)
	link_htab_ent(cp, &cp->sets[i], blk);
      
      // insert into head of way list, order is arbitrary at this point 
      blk->way_next = cp->sets[i].way_head;
      blk->way_prev = NULL;
      if (cp->sets[i].way_head)
	cp->sets[i].way_head->way_prev = blk;
      cp->sets[i].way_head = blk;
      if (!cp->sets[i].way_tail)
	cp->sets[i].way_tail = blk;
      cp->sets[i].way_three = (cp->sets[i].way_head)->way_next->way_next;
      
      // locate next cache block 
      blk = CACHE_BINDEX(cp, cp->data, bindex);
      bindex++;
      
      // invalidate new cache block 
      blk->status = 0;
      blk->tag = 0;
      blk->ready = 0;
      blk->user_data = (usize != 0
			? (byte_t *)calloc(usize, sizeof(byte_t)) : NULL);

      // insert cache block into set hash table 
      if (cp->hsize)
	    link_htab_ent(cp, &cp->sets[i], blk);
      
      // insert into head of way list, order is arbitrary at this point 
      blk->way_next = cp->sets[i].way_head;
      blk->way_prev = NULL;
      if (cp->sets[i].way_head)
	cp->sets[i].way_head->way_prev = blk;
      cp->sets[i].way_head = blk;
      if (!cp->sets[i].way_tail)
	cp->sets[i].way_tail = blk;
      cp->sets[i].way_four = (cp->sets[i].way_tail);
      */
    }
  if(!strcmp(cp->name, "ul2")){
      for (i = 0; i<nsets; i++){ 
	(cp->sets[i].way_one)->way_next = cp->sets[i].way_two;
	(cp->sets[i].way_one)->way_prev = NULL;
	(cp->sets[i].way_two)->way_next = cp->sets[i].way_three;
	(cp->sets[i].way_two)->way_prev = cp->sets[i].way_one;
	(cp->sets[i].way_three)->way_next = cp->sets[i].way_four;
	(cp->sets[i].way_three)->way_prev = cp->sets[i].way_two;
	(cp->sets[i].way_four)->way_next = NULL;
	(cp->sets[i].way_four)->way_prev = cp->sets[i].way_three;
	cp->sets[i].way_head = cp->sets[i].way_one;
	cp->sets[i].way_tail = cp->sets[i].way_four;
	
      }
    }
  return cp;
}

/* parse policy */
enum cache_policy			/* replacement policy enum */
cache_char2policy(char c)		/* replacement policy as a char */
{
  switch (c) {
  case 'l': return LRU;
  case 'r': return Random;
  case 'f': return FIFO;
  default: fatal("bogus replacement policy, `%c'", c);
  }
}

/* print cache configuration */
void
cache_config(struct cache_t *cp,	/* cache instance */
	     FILE *stream)		/* output stream */
{
  fprintf(stream,
	  "cache: %s: %d sets, %d byte blocks, %d bytes user data/block\n",
	  cp->name, cp->nsets, cp->bsize, cp->usize);
  fprintf(stream,
	  "cache: %s: %d-way, `%s' replacement policy, write-back\n",
	  cp->name, cp->assoc,
	  cp->policy == LRU ? "LRU"
	  : cp->policy == Random ? "Random"
	  : cp->policy == FIFO ? "FIFO"
	  : (abort(), ""));
}

/* register cache stats */
void
cache_reg_stats(struct cache_t *cp,	/* cache instance */
		struct stat_sdb_t *sdb)	/* stats database */
{
  char buf[512], buf1[512], *name;

  /* get a name for this cache */
  if (!cp->name || !cp->name[0])
    name = "<unknown>";
  else
    name = cp->name;

  sprintf(buf, "%s.accesses", name);
  sprintf(buf1, "%s.hits + %s.misses", name, name);
  stat_reg_formula(sdb, buf, "total number of accesses", buf1, "%12.0f");
  sprintf(buf, "%s.hits", name);
  stat_reg_counter(sdb, buf, "total number of hits", &cp->hits, 0, NULL);
  sprintf(buf, "%s.misses", name);
  stat_reg_counter(sdb, buf, "total number of misses", &cp->misses, 0, NULL);
  sprintf(buf, "%s.replacements", name);
  stat_reg_counter(sdb, buf, "total number of replacements",
		 &cp->replacements, 0, NULL);
  sprintf(buf, "%s.writebacks", name);
  stat_reg_counter(sdb, buf, "total number of writebacks",
		 &cp->writebacks, 0, NULL);
  sprintf(buf, "%s.invalidations", name);
  stat_reg_counter(sdb, buf, "total number of invalidations",
		 &cp->invalidations, 0, NULL);
  sprintf(buf, "%s.miss_rate", name);
  sprintf(buf1, "%s.misses / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "miss rate (i.e., misses/ref)", buf1, NULL);
  sprintf(buf, "%s.repl_rate", name);
  sprintf(buf1, "%s.replacements / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "replacement rate (i.e., repls/ref)", buf1, NULL);
  sprintf(buf, "%s.wb_rate", name);
  sprintf(buf1, "%s.writebacks / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "writeback rate (i.e., wrbks/ref)", buf1, NULL);
  sprintf(buf, "%s.inv_rate", name);
  sprintf(buf1, "%s.invalidations / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "invalidation rate (i.e., invs/ref)", buf1, NULL);
}

/* print cache stats */
void
cache_stats(struct cache_t *cp,		/* cache instance */
	    FILE *stream)		/* output stream */
{
  double sum = (double)(cp->hits + cp->misses);

  fprintf(stream,
	  "cache: %s: %.0f hits %.0f misses %.0f repls %.0f invalidations\n",
	  cp->name, (double)cp->hits, (double)cp->misses,
	  (double)cp->replacements, (double)cp->invalidations);
  fprintf(stream,
	  "cache: %s: miss rate=%f  repl rate=%f  invalidation rate=%f\n",
	  cp->name,
	  (double)cp->misses/sum, (double)(double)cp->replacements/sum,
	  (double)cp->invalidations/sum);
}

// find the least recently used block 
struct node_t * find_repl_node(struct cache_t *cp,
			       struct cache_tree_t *tree0,
			       struct cache_tree_t *tree1,
			       struct cache_tree_t *tree2,
			       struct cache_tree_t *tree3){
  struct node_t *lru, *temp, *tempt, *temp1, *temp2, *temp3;
  tick_t lru_time;
  int tset, tway;
  struct cache_blk_t *tnblk, *tpblk, *tblk;

  if (tree0->tree_head != NULL){
    lru = tree0->tree_head;
    
    lru_time = tree0->tree_head->blk->last_access;
  }
  else if (tree1->tree_head != NULL){
    lru = tree1->tree_head;
    lru_time = tree1->tree_head->blk->last_access;
  }
  else if (tree2->tree_head != NULL){
    lru = tree2->tree_head;
    lru_time = tree2->tree_head->blk->last_access;
  }
  else if (tree3->tree_head != NULL){
    lru = tree3->tree_head;
    lru_time = tree3->tree_head->blk->last_access;
  }
  if ((tree1->tree_head != NULL) && (tree1->tree_head->blk->last_access <= lru_time)){
    lru = tree1->tree_head;
    lru_time = tree1->tree_head->blk->last_access;
  }
  if ((tree2->tree_head != NULL) && (tree2->tree_head->blk->last_access <= lru_time)){
    lru = tree2->tree_head;
    lru_time = tree2->tree_head->blk->last_access;
  } 
  if ((tree3->tree_head != NULL) && (tree3->tree_head->blk->last_access <= lru_time)){
    lru = tree3->tree_head;
    lru_time = tree3->tree_head->blk->last_access;
  }
  if ((tree0->tree_head != NULL) && (tree0->tree_head->blk->last_access <= lru_time)){
    lru = tree0->tree_head;
    lru_time = tree0->tree_head->blk->last_access;
  }
  if (((tree1->tree_head)->one != NULL) && (tree1->tree_head->one->blk->last_access < lru_time)){
    lru = (tree1->tree_head)->one;
    lru_time = tree1->tree_head->one->blk->last_access;
  }
  if (((tree1->tree_head)->two != NULL) && (tree1->tree_head->two->blk->last_access < lru_time)){
    lru = (tree1->tree_head)->two;
    lru_time = tree1->tree_head->two->blk->last_access;
  }
  if (((tree1->tree_head)->three != NULL) && (tree1->tree_head->three->blk->last_access < lru_time)){
    lru = (tree1->tree_head)->three;
    lru_time = tree1->tree_head->three->blk->last_access;
  }
  if((tree1->tree_head->one->one != NULL) && (tree1->tree_head->one->one->blk->last_access < lru_time)){
    lru = tree1->tree_head->one->one;
    lru_time = tree1->tree_head->one->one->blk->last_access;
  }
  if((tree1->tree_head->one->two != NULL) && (tree1->tree_head->one->two->blk->last_access < lru_time)){
    lru = tree1->tree_head->one->two;
    lru_time = tree1->tree_head->one->two->blk->last_access;
  }
  if((tree1->tree_head->one->three != NULL) && (tree1->tree_head->one->three->blk->last_access < lru_time)){
    lru = tree1->tree_head->one->three;
    lru_time = tree1->tree_head->one->three->blk->last_access;
  }
  if((tree1->tree_head->two->one != NULL) && (tree1->tree_head->two->one->blk->last_access < lru_time)){
    lru = tree1->tree_head->two->one;
    lru_time = tree1->tree_head->two->one->blk->last_access;
  }
  if((tree1->tree_head->two->two != NULL) && (tree1->tree_head->two->two->blk->last_access < lru_time)){
    lru = tree1->tree_head->two->two;
    lru_time = tree1->tree_head->two->two->blk->last_access;
  }
  if((tree1->tree_head->two->three != NULL) && (tree1->tree_head->two->three->blk->last_access < lru_time)){
    lru = tree1->tree_head->two->three;
    lru_time = tree1->tree_head->two->three->blk->last_access;
  }
  if((tree1->tree_head->three->one != NULL) && (tree1->tree_head->three->one->blk->last_access < lru_time)){
    lru = tree1->tree_head->three->one;
    lru_time = tree1->tree_head->three->one->blk->last_access;
  }
  if((tree1->tree_head->three->two != NULL) && (tree1->tree_head->three->two->blk->last_access < lru_time)){
    lru = tree1->tree_head->three->two;
    lru_time = tree1->tree_head->three->two->blk->last_access;
  }
  if((tree1->tree_head->three->three != NULL) && (tree1->tree_head->three->three->blk->last_access < lru_time)){
    lru = tree1->tree_head->three->three;
    lru_time = tree1->tree_head->three->three->blk->last_access;
  }
  if (((tree2->tree_head)->one != NULL) && (tree2->tree_head->one->blk->last_access < lru_time)){
    lru = (tree2->tree_head)->one;
    lru_time = tree2->tree_head->one->blk->last_access;
  }
  if (((tree2->tree_head)->two != NULL) && (tree2->tree_head->two->blk->last_access < lru_time)){
    lru = (tree2->tree_head)->two;
    lru_time = tree2->tree_head->two->blk->last_access;
  }
  if (((tree2->tree_head)->three != NULL) && (tree2->tree_head->three->blk->last_access < lru_time)){
    lru = (tree2->tree_head)->three;
    lru_time = tree2->tree_head->three->blk->last_access;
  }
  if((tree2->tree_head->one->one != NULL) && (tree2->tree_head->one->one->blk->last_access < lru_time)){
    lru = tree2->tree_head->one->one;
    lru_time = tree2->tree_head->one->one->blk->last_access;
  }
  if((tree2->tree_head->one->two != NULL) && (tree2->tree_head->one->two->blk->last_access < lru_time)){
    lru = tree2->tree_head->one->two;
    lru_time = tree2->tree_head->one->two->blk->last_access;
  }
  if((tree2->tree_head->one->three != NULL) && (tree2->tree_head->one->three->blk->last_access < lru_time)){
    lru = tree2->tree_head->one->three;
    lru_time = tree2->tree_head->one->three->blk->last_access;
  }
  if((tree2->tree_head->two->one != NULL) && (tree2->tree_head->two->one->blk->last_access < lru_time)){
    lru = tree2->tree_head->two->one;
    lru_time = tree2->tree_head->two->one->blk->last_access;
  }
  if((tree2->tree_head->two->two != NULL) && (tree2->tree_head->two->two->blk->last_access < lru_time)){
    lru = tree2->tree_head->two->two;
    lru_time = tree2->tree_head->two->two->blk->last_access;
  }
  if((tree2->tree_head->two->three != NULL) && (tree2->tree_head->two->three->blk->last_access < lru_time)){
    lru = tree2->tree_head->two->three;
    lru_time = tree2->tree_head->two->three->blk->last_access;
  }
  if((tree2->tree_head->three->one != NULL) && (tree2->tree_head->three->one->blk->last_access < lru_time)){
    lru = tree2->tree_head->three->one;
    lru_time = tree2->tree_head->three->one->blk->last_access;
  }
  if((tree2->tree_head->three->two != NULL) && (tree2->tree_head->three->two->blk->last_access < lru_time)){
    lru = tree2->tree_head->three->two;
    lru_time = tree2->tree_head->three->two->blk->last_access;
  }
  if((tree2->tree_head->three->three != NULL) && (tree2->tree_head->three->three->blk->last_access < lru_time)){
    lru = tree2->tree_head->three->three;
    lru_time = tree2->tree_head->three->three->blk->last_access;
  }
  if (((tree3->tree_head)->one != NULL) && (tree3->tree_head->one->blk->last_access < lru_time)){
    lru = (tree3->tree_head)->one;
    lru_time = tree3->tree_head->one->blk->last_access;
  }
  if (((tree3->tree_head)->two != NULL) && (tree3->tree_head->two->blk->last_access < lru_time)){
    lru = (tree3->tree_head)->two;
    lru_time = tree3->tree_head->two->blk->last_access;
  }
  if (((tree3->tree_head)->three != NULL) && (tree3->tree_head->three->blk->last_access < lru_time)){
    lru = (tree3->tree_head)->three;
    lru_time = tree3->tree_head->three->blk->last_access;
  }
  if((tree3->tree_head->one->one != NULL) && (tree3->tree_head->one->one->blk->last_access < lru_time)){
    lru = tree3->tree_head->one->one;
    lru_time = tree3->tree_head->one->one->blk->last_access;
  }
  if((tree3->tree_head->one->two != NULL) && (tree3->tree_head->one->two->blk->last_access < lru_time)){
    lru = tree3->tree_head->one->two;
    lru_time = tree3->tree_head->one->two->blk->last_access;
  }
  if((tree3->tree_head->one->three != NULL) && (tree3->tree_head->one->three->blk->last_access < lru_time)){
    lru = tree3->tree_head->one->three;
    lru_time = tree3->tree_head->one->three->blk->last_access;
  }
  if((tree3->tree_head->two->one != NULL) && (tree3->tree_head->two->one->blk->last_access < lru_time)){
    lru = tree3->tree_head->two->one;
    lru_time = tree3->tree_head->two->one->blk->last_access;
  }
  if((tree3->tree_head->two->two != NULL) && (tree3->tree_head->two->two->blk->last_access < lru_time)){
    lru = tree3->tree_head->two->two;
    lru_time = tree3->tree_head->two->two->blk->last_access;
  }
  if((tree3->tree_head->two->three != NULL) && (tree3->tree_head->two->three->blk->last_access < lru_time)){
    lru = tree3->tree_head->two->three;
    lru_time = tree3->tree_head->two->three->blk->last_access;
  }
  if((tree3->tree_head->three->one != NULL) && (tree3->tree_head->three->one->blk->last_access < lru_time)){
    lru = tree3->tree_head->three->one;
    lru_time = tree3->tree_head->three->one->blk->last_access;
  }
  if((tree3->tree_head->three->two != NULL) && (tree3->tree_head->three->two->blk->last_access < lru_time)){
    lru = tree3->tree_head->three->two;
    lru_time = tree3->tree_head->three->two->blk->last_access;
  }
  if((tree3->tree_head->three->three != NULL) && (tree3->tree_head->three->three->blk->last_access < lru_time)){
    lru = tree3->tree_head->three->three;
    lru_time = tree3->tree_head->three->three->blk->last_access;
  }
  if (((tree0->tree_head)->one != NULL) && (tree0->tree_head->one->blk->last_access < lru_time)){
    lru = (tree0->tree_head)->one;
    lru_time = tree0->tree_head->one->blk->last_access;
  }
  if (((tree0->tree_head)->two != NULL) && (tree0->tree_head->two->blk->last_access < lru_time)){
    lru = (tree0->tree_head)->two;
    lru_time = tree0->tree_head->two->blk->last_access;
  }
  if (((tree0->tree_head)->three != NULL) && (tree0->tree_head->three->blk->last_access < lru_time)){
    lru = (tree0->tree_head)->three;
    lru_time = tree0->tree_head->three->blk->last_access;
  }
  if((tree0->tree_head->one->one != NULL) && (tree0->tree_head->one->one->blk->last_access < lru_time)){
    lru = tree0->tree_head->one->one;
    lru_time = tree0->tree_head->one->one->blk->last_access;
  }
  if((tree0->tree_head->one->two != NULL) && (tree0->tree_head->one->two->blk->last_access < lru_time)){
    lru = tree0->tree_head->one->two;
    lru_time = tree0->tree_head->one->two->blk->last_access;
  }
  if((tree0->tree_head->one->three != NULL) && (tree0->tree_head->one->three->blk->last_access < lru_time)){
    lru = tree0->tree_head->one->three;
    lru_time = tree0->tree_head->one->three->blk->last_access;
  }
  if((tree0->tree_head->two->one != NULL) && (tree0->tree_head->two->one->blk->last_access < lru_time)){
    lru = tree0->tree_head->two->one;
    lru_time = tree0->tree_head->two->one->blk->last_access;
  }
  if((tree0->tree_head->two->two != NULL) && (tree0->tree_head->two->two->blk->last_access < lru_time)){
    lru = tree0->tree_head->two->two;
    lru_time = tree0->tree_head->two->two->blk->last_access;
  }
  if((tree0->tree_head->two->three != NULL) && (tree0->tree_head->two->three->blk->last_access < lru_time)){
    lru = tree0->tree_head->two->three;
    lru_time = tree0->tree_head->two->three->blk->last_access;
  }
  if((tree0->tree_head->three->one != NULL) && (tree0->tree_head->three->one->blk->last_access < lru_time)){
    lru = tree0->tree_head->three->one;
    lru_time = tree0->tree_head->three->one->blk->last_access;
  }
  if((tree0->tree_head->three->two != NULL) && (tree0->tree_head->three->two->blk->last_access < lru_time)){
    lru = tree0->tree_head->three->two;
    lru_time = tree0->tree_head->three->two->blk->last_access;
  }
  if((tree0->tree_head->three->three != NULL) && (tree0->tree_head->three->three->blk->last_access < lru_time)){
    lru = tree0->tree_head->three->three;
    lru_time = tree0->tree_head->three->three->blk->last_access;
  }
  if (lru == tree0->tree_head){
    lru->set = cp->nsets;
  }
  if (lru == tree1->tree_head){
    lru->set = cp->nsets;
  }
  if (lru == tree2->tree_head){
    lru->set = cp->nsets;
  }
  if (lru == tree3->tree_head){
    lru->set = cp->nsets;
  }
  lru->rset = cp->nsets;
  int i = 1;
  while (lru->parent != NULL){
    temp = lru->parent;
    //printf("Loop %d\n", i);
    //i++;
    if (lru->one == NULL && lru->two == NULL && lru->three == NULL){
      if(temp->way == 1){
	if(lru->way == 1){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_one = lru->blk;
	  //(cp->sets[temp->set].way_one)->way_next = 
	  cp->sets[lru->set].way_one = temp->blk;
	  //lru->blk = cp->sets[temp->set].way_one;
	  (cp->sets[temp->set].way_one)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_one)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_one)->way_next = tnblk;
	  (cp->sets[lru->set].way_one)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 2){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_one = lru->blk;
	  cp->sets[lru->set].way_two = temp->blk;
	  (cp->sets[temp->set].way_one)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_one)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_two)->way_next = tnblk;
	  (cp->sets[lru->set].way_two)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 3){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_one = lru->blk;
	  cp->sets[lru->set].way_three = temp->blk;
	  (cp->sets[temp->set].way_one)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_one)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_three)->way_next = tnblk;
	  (cp->sets[lru->set].way_three)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 4){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_one = lru->blk;
	  cp->sets[lru->set].way_four = temp->blk;
	  (cp->sets[temp->set].way_one)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_one)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_four)->way_next = tnblk;
	  (cp->sets[lru->set].way_four)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
      }
      else if(temp->way == 2){
	if(lru->way == 1){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_two = lru->blk;
	  cp->sets[lru->set].way_one = temp->blk;
	  (cp->sets[temp->set].way_two)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_two)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_one)->way_next = tnblk;
	  (cp->sets[lru->set].way_one)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 2){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_two = lru->blk;
	  cp->sets[lru->set].way_two = temp->blk;
	  (cp->sets[temp->set].way_two)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_two)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_two)->way_next = tnblk;
	  (cp->sets[lru->set].way_two)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 3){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_two = lru->blk;
	  cp->sets[lru->set].way_three = temp->blk;
	  (cp->sets[temp->set].way_two)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_two)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_three)->way_next = tnblk;
	  (cp->sets[lru->set].way_three)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 4){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_two = lru->blk;
	  cp->sets[lru->set].way_four = temp->blk;
	  (cp->sets[temp->set].way_two)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_two)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_four)->way_next = tnblk;
	  (cp->sets[lru->set].way_four)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
      } 
      else if(temp->way == 3){
	if(lru->way == 1){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_three = lru->blk;
	  cp->sets[lru->set].way_one = temp->blk;
	  (cp->sets[temp->set].way_three)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_three)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_one)->way_next = tnblk;
	  (cp->sets[lru->set].way_one)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 2){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_three = lru->blk;
	  cp->sets[lru->set].way_two = temp->blk;
	  (cp->sets[temp->set].way_three)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_three)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_two)->way_next = tnblk;
	  (cp->sets[lru->set].way_two)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 3){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_three = lru->blk;
	  cp->sets[lru->set].way_three = temp->blk;
	  (cp->sets[temp->set].way_three)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_three)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_three)->way_next = tnblk;
	  (cp->sets[lru->set].way_three)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 4){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_three = lru->blk;
	  cp->sets[lru->set].way_four = temp->blk;
	  (cp->sets[temp->set].way_three)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_three)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_four)->way_next = tnblk;
	  (cp->sets[lru->set].way_four)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
      }
      else if(temp->way == 4){
	if(lru->way == 1){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_four = lru->blk;
	  cp->sets[lru->set].way_one = temp->blk;
	  (cp->sets[temp->set].way_four)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_four)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_one)->way_next = tnblk;
	  (cp->sets[lru->set].way_one)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 2){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_four = lru->blk;
	  cp->sets[lru->set].way_two = temp->blk;
	  (cp->sets[temp->set].way_four)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_four)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_two)->way_next = tnblk;
	  (cp->sets[lru->set].way_two)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 3){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_four = lru->blk;
	  cp->sets[lru->set].way_three = temp->blk;
	  (cp->sets[temp->set].way_four)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_four)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_three)->way_next = tnblk;
	  (cp->sets[lru->set].way_three)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 4){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_four = lru->blk;
	  cp->sets[lru->set].way_four = temp->blk;
	  (cp->sets[temp->set].way_four)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_four)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_four)->way_next = tnblk;
	  (cp->sets[lru->set].way_four)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->rset = temp->set;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
      }
      if (temp->one == lru){
	/*tset = lru->set;
	lru->set = temp->set;
	temp->set = tset;
	tblk = lru->blk;
	lru->blk = temp->blk;
	temp->blk = tblk;
	*/
	lru->parent = temp->parent;
	if(temp->parent->one == temp){
	  lru->parent->one = lru;
	}
	else if(temp->parent->two == temp){
	  lru->parent->two = lru;
	}
	else if(temp->parent->three == temp){
	  lru->parent->three = lru;
	}
	lru->one = temp;
	lru->two = temp->two;
	lru->three = temp->three;
	temp->one = NULL;
	temp->two = NULL;
	temp->three = NULL;
	lru->one->parent = lru;
	lru->two->parent = lru;
	lru->three->parent = lru;
	//lru->parent->one = lru;
      }
      else if (temp->two == lru){
	/*tset = lru->set;
	lru->set = temp->set;
	temp->set = tset;
	tblk = lru->blk;
	lru->blk = temp->blk;
	temp->blk = tblk;
	*/
	lru->parent = temp->parent;
	if(temp->parent->one == temp){
	  lru->parent->one = lru;
	}
	else if(temp->parent->two == temp){
	  lru->parent->two = lru;
	}
	else if(temp->parent->three == temp){
	  lru->parent->three = lru;
	}
	lru->two = temp;
	lru->one = temp->one;
	lru->three = temp->three;
	temp->one = NULL;
	temp->two = NULL;
	temp->three = NULL;
	//temp->parent = lru;
	lru->one->parent = lru;
	lru->two->parent = lru;
	lru->three->parent = lru;
	//lru->parent->two = lru;
      }
      else if (temp->three == lru){
	/*tset = lru->set;
	lru->set = temp->set;
	temp->set = tset;
	tblk = lru->blk;
	lru->blk = temp->blk;
	temp->blk = tblk;
	*/
	lru->parent = temp->parent;
	if(temp->parent->one == temp){
	  lru->parent->one = lru;
	}
	else if(temp->parent->two == temp){
	  lru->parent->two = lru;
	}
	else if(temp->parent->three == temp){
	  lru->parent->three = lru;
	}
	lru->three = temp;
	lru->two = temp->two;
	lru->one = temp->one;
	temp->one = NULL;
	temp->two = NULL;
	temp->three = NULL;
	//temp->parent = lru;
	lru->one->parent = lru;
	lru->two->parent = lru;
	lru->three->parent = lru;
	//lru->parent->three = lru;
      }
    }
    else{
      tnblk = lru->blk->way_next;
      tpblk = lru->blk->way_prev;
      if(temp->way == 1){
	if(lru->way == 1){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_one = lru->blk;
	  //(cp->sets[temp->set].way_one)->way_next = 
	  cp->sets[lru->set].way_one = temp->blk;
	  (cp->sets[temp->set].way_one)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_one)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_one)->way_next = tnblk;
	  (cp->sets[lru->set].way_one)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 2){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_one = lru->blk;
	  cp->sets[lru->set].way_two = temp->blk;
	  (cp->sets[temp->set].way_one)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_one)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_two)->way_next = tnblk;
	  (cp->sets[lru->set].way_two)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 3){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_one = lru->blk;
	  cp->sets[lru->set].way_three = temp->blk;
	  (cp->sets[temp->set].way_one)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_one)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_three)->way_next = tnblk;
	  (cp->sets[lru->set].way_three)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 4){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_one = lru->blk;
	  cp->sets[lru->set].way_four = temp->blk;
	  (cp->sets[temp->set].way_one)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_one)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_four)->way_next = tnblk;
	  (cp->sets[lru->set].way_four)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
      }
      else if(temp->way == 2){
	if(lru->way == 1){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_two = lru->blk;
	  cp->sets[lru->set].way_one = temp->blk;
	  (cp->sets[temp->set].way_two)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_two)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_one)->way_next = tnblk;
	  (cp->sets[lru->set].way_one)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 2){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_two = lru->blk;
	  cp->sets[lru->set].way_two = temp->blk;
	  (cp->sets[temp->set].way_two)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_two)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_two)->way_next = tnblk;
	  (cp->sets[lru->set].way_two)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 3){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_two = lru->blk;
	  cp->sets[lru->set].way_three = temp->blk;
	  (cp->sets[temp->set].way_two)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_two)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_three)->way_next = tnblk;
	  (cp->sets[lru->set].way_three)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 4){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_two = lru->blk;
	  cp->sets[lru->set].way_four = temp->blk;
	  (cp->sets[temp->set].way_two)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_two)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_four)->way_next = tnblk;
	  (cp->sets[lru->set].way_four)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
      } 
      else if(temp->way == 3){
	if(lru->way == 1){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_three = lru->blk;
	  cp->sets[lru->set].way_one = temp->blk;
	  (cp->sets[temp->set].way_three)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_three)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_one)->way_next = tnblk;
	  (cp->sets[lru->set].way_one)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 2){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_three = lru->blk;
	  cp->sets[lru->set].way_two = temp->blk;
	  (cp->sets[temp->set].way_three)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_three)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_two)->way_next = tnblk;
	  (cp->sets[lru->set].way_two)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 3){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  cp->sets[temp->set].way_three = lru->blk;
	  cp->sets[lru->set].way_three = temp->blk;
	  (cp->sets[temp->set].way_three)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_three)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_three)->way_next = tnblk;
	  (cp->sets[lru->set].way_three)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 4){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_three = lru->blk;
	  cp->sets[lru->set].way_four = temp->blk;
	  (cp->sets[temp->set].way_three)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_three)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_four)->way_next = tnblk;
	  (cp->sets[lru->set].way_four)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
      }
      else if(temp->way == 4){
	if(lru->way == 1){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_four = lru->blk;
	  cp->sets[lru->set].way_one = temp->blk;
	  (cp->sets[temp->set].way_four)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_four)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_one)->way_next = tnblk;
	  (cp->sets[lru->set].way_one)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 2){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_four = lru->blk;
	  cp->sets[lru->set].way_two = temp->blk;
	  (cp->sets[temp->set].way_four)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_four)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_two)->way_next = tnblk;
	  (cp->sets[lru->set].way_two)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 3){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_four = lru->blk;
	  cp->sets[lru->set].way_three = temp->blk;
	  (cp->sets[temp->set].way_four)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_four)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_three)->way_next = tnblk;
	  (cp->sets[lru->set].way_three)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
	else if(lru->way == 4){
	  //tblk = temp->blk;
	  tset = lru->set;
	  tway = lru->way;
	  tnblk = lru->blk->way_next;
	  tpblk = lru->blk->way_prev;
	  cp->sets[temp->set].way_four = lru->blk;
	  cp->sets[lru->set].way_four = temp->blk;
	  (cp->sets[temp->set].way_four)->way_next = temp->blk->way_next;
	  (cp->sets[temp->set].way_four)->way_prev = temp->blk->way_prev;
	  (cp->sets[lru->set].way_four)->way_next = tnblk;
	  (cp->sets[lru->set].way_four)->way_prev = tpblk;
	  cp->sets[temp->set].way_head = cp->sets[temp->set].way_one;
	  cp->sets[temp->set].way_tail = cp->sets[temp->set].way_four;
	  cp->sets[lru->set].way_head = cp->sets[lru->set].way_one;
	  cp->sets[lru->set].way_tail = cp->sets[lru->set].way_four;
	  
	  //lru->blk = cp->sets[temp->set].way_one;
	  lru->set = temp->set;
	  lru->way = temp->way;
	  temp->set = tset;
	  temp->way = tway;
	  //tblk = lru->blk;
	  //lru->blk = temp->blk;
	  //temp->blk = tblk;
	}
      }
      if (temp->one == lru){
	/*tset = lru->set;
	lru->set = temp->set;
	temp->set = tset;
	tblk = lru->blk;
	lru->blk = temp->blk;
	temp->blk = tblk;
	*/
	lru->parent = temp->parent;
	temp1 = lru->one;
	temp2 = lru->two;
	temp3 = lru->three;
	lru->one = temp;
	lru->two = temp->two;
	lru->three = temp->three;
	temp->one = temp1;
	temp->two = temp2;
	temp->three = temp3;
	temp->one->parent = temp;
	temp->two->parent = temp;
	temp->three->parent = temp;
	//temp->parent = lru;
	lru->one->parent = lru;
	lru->two->parent = lru;
	lru->three->parent = lru;
      }
      else if (temp->two == lru){
	/*tset = lru->set;
	lru->set = temp->set;
	temp->set = tset;
	tblk = lru->blk;
	lru->blk = temp->blk;
	temp->blk = tblk;
	*/
	lru->parent = temp->parent;
	temp1 = lru->one;
	temp2 = lru->two;
	temp3 = lru->three;
	lru->one = temp->one;
	lru->two = temp;
	lru->three = temp->three;
	temp->one = temp1;
	temp->two = temp2;
	temp->three = temp3;
	temp->one->parent = temp;
	temp->two->parent = temp;
	temp->three->parent = temp;
	//temp->parent = lru;
	lru->one->parent = lru;
	lru->two->parent = lru;
	lru->three->parent = lru;
      }
      else if (temp->three == lru){
	/*tset = lru->set;
	lru->set = temp->set;
	temp->set = tset;
	tblk = lru->blk;
	lru->blk = temp->blk;
	temp->blk = tblk;
	*/
	lru->parent = temp->parent;
	temp1 = lru->one;
	temp2 = lru->two;
	temp3 = lru->three;
	lru->one = temp->one;
	lru->two = temp->two;
	lru->three = temp;
	temp->one = temp1;
	temp->two = temp2;
	temp->three = temp3;
	temp->one->parent = temp;
	temp->two->parent = temp;
	temp->three->parent = temp;
	//temp->parent = lru;
	lru->one->parent = lru;
	lru->two->parent = lru;
	lru->three->parent = lru;
      }
      
    }
    if(temp && (tree0->tree_head == temp)){
      tree0->tree_head = lru;
      //return lru;
    }
    else if(temp && (tree1->tree_head == temp)){
      tree1->tree_head = lru;
      //return lru;
    }
    else if(temp && (tree2->tree_head == temp)){
      tree2->tree_head = lru;
      // return lru;
    }
    else if(temp && (tree3->tree_head == temp)){
      tree3->tree_head = lru;
      // return lru;
    }
  }
  
  return lru;
}

static void delTree(struct cache_tree_t *t0, struct cache_tree_t *t1, struct cache_tree_t *t2, struct cache_tree_t *t3){
  if(t0 != NULL){
    if(t0->tree_head != NULL){
      if(t0->tree_head->one != NULL){
	if(t0->tree_head->one->one != NULL)
	  free(t0->tree_head->one->one);
	if(t0->tree_head->one->two != NULL)
	  free(t0->tree_head->one->two);
	if(t0->tree_head->one->three != NULL)
	  free(t0->tree_head->one->three);
	free(t0->tree_head->one);
      }
      if(t0->tree_head->two != NULL){
	if(t0->tree_head->two->one != NULL)
	  free(t0->tree_head->two->one);
	if(t0->tree_head->two->two != NULL)
	  free(t0->tree_head->two->two);
	if(t0->tree_head->two->three != NULL)
	  free(t0->tree_head->two->three);
	free(t0->tree_head->two);
      }
      if(t0->tree_head->three != NULL){
	if(t0->tree_head->three->one != NULL)
	  free(t0->tree_head->three->one);
	if(t0->tree_head->three->two != NULL)
	  free(t0->tree_head->three->two);
	if(t0->tree_head->three->three != NULL)
	  free(t0->tree_head->three->three);
	free(t0->tree_head->three);
      }
      free(t0->tree_head);
    }
    free(t0);
  }
  if(t1 != NULL){
    if(t1->tree_head != NULL){
      if(t1->tree_head->one != NULL){
	if(t1->tree_head->one->one != NULL)
	  free(t1->tree_head->one->one);
	if(t1->tree_head->one->two != NULL)
	  free(t1->tree_head->one->two);
	if(t1->tree_head->one->three != NULL)
	  free(t1->tree_head->one->three);
	free(t1->tree_head->one);
      }
      if(t1->tree_head->two != NULL){
	if(t1->tree_head->two->one != NULL)
	  free(t1->tree_head->two->one);
	if(t1->tree_head->two->two != NULL)
	  free(t1->tree_head->two->two);
	if(t1->tree_head->two->three != NULL)
	  free(t1->tree_head->two->three);
	free(t1->tree_head->two);
      }
      if(t1->tree_head->three != NULL){
	if(t1->tree_head->three->one != NULL)
	  free(t1->tree_head->three->one);
	if(t1->tree_head->three->two != NULL)
	  free(t1->tree_head->three->two);
	if(t1->tree_head->three->three != NULL)
	  free(t1->tree_head->three->three);
	free(t1->tree_head->three);
      }
      free(t1->tree_head);
    }
    free(t1);
  }
  if(t2 != NULL){
    if(t2->tree_head != NULL){
      if(t2->tree_head->one != NULL){
	if(t2->tree_head->one->one != NULL)
	  free(t2->tree_head->one->one);
	if(t2->tree_head->one->two != NULL)
	  free(t2->tree_head->one->two);
	if(t2->tree_head->one->three != NULL)
	  free(t2->tree_head->one->three);
	free(t2->tree_head->one);
      }
      if(t2->tree_head->two != NULL){
	if(t2->tree_head->two->one != NULL)
	  free(t2->tree_head->two->one);
	if(t2->tree_head->two->two != NULL)
	  free(t2->tree_head->two->two);
	if(t2->tree_head->two->three != NULL)
	  free(t2->tree_head->two->three);
	free(t2->tree_head->two);
      }
      if(t2->tree_head->three != NULL){
	if(t2->tree_head->three->one != NULL)
	  free(t2->tree_head->three->one);
	if(t2->tree_head->three->two != NULL)
	  free(t2->tree_head->three->two);
	if(t2->tree_head->three->three != NULL)
	  free(t2->tree_head->three->three);
	free(t2->tree_head->three);
      }
      free(t2->tree_head);
    }
    free(t2);
  }
  if(t3 != NULL){
    if(t3->tree_head != NULL){
      if(t3->tree_head->one != NULL){
	if(t3->tree_head->one->one != NULL)
	  free(t3->tree_head->one->one);
	if(t3->tree_head->one->two != NULL)
	  free(t3->tree_head->one->two);
	if(t3->tree_head->one->three != NULL)
	  free(t3->tree_head->one->three);
	free(t3->tree_head->one);
      }
      if(t3->tree_head->two != NULL){
	if(t3->tree_head->two->one != NULL)
	  free(t3->tree_head->two->one);
	if(t3->tree_head->two->two != NULL)
	  free(t3->tree_head->two->two);
	if(t3->tree_head->two->three != NULL)
	  free(t3->tree_head->two->three);
	free(t3->tree_head->two);
      }
      if(t3->tree_head->three != NULL){
	if(t3->tree_head->three->one != NULL)
	  free(t3->tree_head->three->one);
	if(t3->tree_head->three->two != NULL)
	  free(t3->tree_head->three->two);
	if(t3->tree_head->three->three != NULL)
	  free(t3->tree_head->three->three);
	free(t3->tree_head->three);
      }
      free(t3->tree_head);
    }
    free(t3);
  }
  return;
}
  

/* access a cache, perform a CMD operation on cache CP at address ADDR,
   places NBYTES of data at *P, returns latency of operation if initiated
   at NOW, places pointer to block user data in *UDATA, *P is untouched if
   cache blocks are not allocated (!CP->BALLOC), UDATA should be NULL if no
   user data is attached to blocks */
unsigned int				/* latency of access in cycles */
cache_access(struct cache_t *cp,	/* cache to access */
	     enum mem_cmd cmd,		/* access type, Read or Write */
	     md_addr_t addr,		/* address of access */
	     void *vp,			/* ptr to buffer for input/output */
	     int nbytes,		/* number of bytes to access */
	     tick_t now,		/* time of access */
	     byte_t **udata,		/* for return of user data ptr */
	     md_addr_t *repl_addr)	/* for address of replaced block */
{
  byte_t *p = vp;
  md_addr_t tag = CACHE_TAG(cp, addr);
  md_addr_t set = CACHE_SET(cp, addr);
  md_addr_t bofs = CACHE_BLK(cp, addr);
  md_addr_t ha, ta, taa;
  struct cache_blk_t *blk, *repl, *temp, *w0, *w1, *w2, *w3, *w, *w00, *w01, *w02, *w03, *w10, *w11, *w12, *w13, *w20, *w21, *w22, *w23, *w30, *w31, *w32, *w33 ;
  int lat = 0;
  int rep_lat = 0;
  struct cache_tree_t *repl_cand0, *repl_cand1, *repl_cand2, *repl_cand3;
  struct node_t *repl_node;
  //  md_addr_t *temp_addr;
  int hset0, hset1, hset2, hset3, hrepl, h0, h1, h2, h3, h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33;
  //  int i=0;
  //int j=0;

  /* default replacement address */
  if (repl_addr)
    *repl_addr = 0;

  /* check alignments */
  if ((nbytes & (nbytes-1)) != 0 || (addr & (nbytes-1)) != 0)
    fatal("cache: access error: bad size or alignment, addr 0x%08x", addr);

  /* access must fit in cache block */
  /* FIXME:
     ((addr + (nbytes - 1)) > ((addr & ~cp->blk_mask) + (cp->bsize - 1))) */
  if ((addr + nbytes) > ((addr & ~cp->blk_mask) + cp->bsize))
    fatal("cache: access error: access spans block, addr 0x%08x", addr);

  /* permissions are checked on cache misses */
  
  // check for a fast hit: access to same block 
  if (CACHE_TAGSET(cp, addr) == cp->last_tagset)
    {
      // hit in the same block 
      blk = cp->last_blk;
      //blk->addr = addr;
      goto cache_fast_hit;
    }
  if (strcmp(cp->name, "ul2") != 0){  
    if (cp->hsize)
      {
	// higly-associativity cache, access through the per-set hash tables 
	int hindex = CACHE_HASH(cp, tag);
	
	for (blk=cp->sets[set].hash[hindex];
	     blk;
	     blk=blk->hash_next)
	  {
	    if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	      //blk->addr = addr;
	      goto cache_hit;
	  }
      }
    else
      {
	// low-associativity cache, linear search the way list
	for (blk=cp->sets[set].way_head;
	     blk;
	     blk=blk->way_next)
	  {
	    if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	      //blk->addr = addr;
	      goto cache_hit;
	  }
      }
  }
  else if (!strcmp(cp->name, "ul2")){
    //ta = CACHE_BADDR(cp, addr);
    ha = CACHE_HASH1(cp, addr);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH2(cp, addr);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, addr);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, addr);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    h0 = hset0;
    h1 = hset1;
    h2 = hset2;
    h3 = hset3;
    w0 = cp->sets[h0].way_one;
    w1 = cp->sets[h1].way_two;
    w2 = cp->sets[h2].way_three;
    w3 = cp->sets[h3].way_four;
   /*
    hset0 = set;
    hset1 = set;
    hset2 = set;
    hset3 = set;*/
    blk = cp->sets[hset0].way_one;
    if ((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //blk->addr = addr;
      goto cache_hit;
    }
    ha = CACHE_HASH2(cp, addr);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //blk->addr = addr;
      goto cache_hit;
    }
    ha = CACHE_HASH3(cp, addr);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset2].way_three;
    if ((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //blk->addr = addr;
      goto cache_hit;
    }
    ha = CACHE_HASH4(cp, addr);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset3].way_four;
    if ((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //blk->addr = addr;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w0->tag, h0);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    //h00 = h0;
    h01 = hset1;
    h02 = hset2;
    h03 = hset3;
    //w00 = cp->sets[h0].way_one;
    w01 = cp->sets[hset1].way_two;
    w02 = cp->sets[hset2].way_three;
    w03 = cp->sets[hset3].way_four;
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w1->tag, h1);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    //h00 = h0;
    h10 = hset0;
    h12 = hset2;
    h13 = hset3;
    //w00 = cp->sets[h0].way_one;
    w10 = cp->sets[hset0].way_one;
    w12 = cp->sets[hset2].way_three;
    w13 = cp->sets[hset3].way_four;
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += 2*cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += 2*cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += 2*cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w2->tag, h2);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    //h00 = h0;
    h20 = hset0;
    h21 = hset1;
    h23 = hset3;
    //w00 = cp->sets[h0].way_one;
    w20 = cp->sets[hset0].way_one;
    w21 = cp->sets[hset1].way_two;
    w23 = cp->sets[hset3].way_four;
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += 3*cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += 3*cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += 3*cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w3->tag, h3);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    //h00 = h0;
    h30 = hset0;
    h31 = hset1;
    h32 = hset2;
    //w00 = cp->sets[h0].way_one;
    w30 = cp->sets[hset0].way_one;
    w31 = cp->sets[hset1].way_two;
    w32 = cp->sets[hset2].way_three;
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += 4*cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += 4*cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += 4*cp->hit_latency;
      goto cache_hit;
    }


    ta = CACHE_MK_BADDR(cp, w01->tag, h01);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w02->tag, h02);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w03->tag, h03);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w10->tag, h10);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w12->tag, h12);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w13->tag, h13);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w20->tag, h20);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w21->tag, h21);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w23->tag, h23);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w30->tag, h30);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w31->tag, h31);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH3(cp, ta);
    hset2 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset2].way_three;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    ta = CACHE_MK_BADDR(cp, w32->tag, h32);
    ha = CACHE_HASH1(cp, ta);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH2(cp, ta);
    hset1 = CACHE_SET(cp,ha)%(cp->nsets);
    ha = CACHE_HASH4(cp, ta);
    hset3 = CACHE_SET(cp,ha)%(cp->nsets);
    blk = cp->sets[hset0].way_one;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //      rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset1].way_two;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      // rep_lat += cp->hit_latency;
      goto cache_hit;
    }
    blk = cp->sets[hset3].way_four;
    if((blk->tag == tag && (blk->status & CACHE_BLK_VALID))){
      //rep_lat += cp->hit_latency;
      goto cache_hit;
    }
  }
  /* cache block not found */
  
  /* **MISS** */
  cp->misses++;

  /* select the appropriate block to replace, and re-link this entry to
     the appropriate place in the way list */
  switch (cp->policy) {
  case LRU:
  case FIFO:// Code modification
    if(strcmp(cp->name,"ul2") != 0){
      repl = cp->sets[set].way_tail;
      update_way_list(&cp->sets[set], repl, Head); 
      hrepl = set;
    }
    break;
  case Random:
    {
      int bindex = myrand() & (cp->assoc - 1);
      repl = CACHE_BINDEX(cp, cp->sets[set].blks, bindex);
    }
    break;
  default:
    panic("bogus replacement policy");
  }

  /*Insert code to walk replacement candidates here*/
  if(!strcmp(cp->name,"ul2")){
    repl_cand0 = malloc(sizeof(*repl_cand0));
    repl_cand1 = malloc(sizeof(*repl_cand1));
    repl_cand2 = malloc(sizeof(*repl_cand2));
    repl_cand3 = malloc(sizeof(*repl_cand3));
    //First tree
    //    ta = CACHE_BADDR(cp, addr);
    ha = CACHE_HASH1(cp, addr);
    hset0 = CACHE_SET(cp,ha)%(cp->nsets);
    temp = cp->sets[hset0].way_one;
    if (temp != NULL){
      repl_cand0->tree_head = malloc(sizeof(*(repl_cand0->tree_head)));
      //repl_cand0->tree_head = realloc(repl_cand0->tree_head, sizeof(*(repl_cand0->tree_head)));
      repl_cand0->tree_head->blk = temp;
      //repl_cand0.tree_head = temp;
      repl_cand0->tree_head->parent = NULL;
      repl_cand0->tree_head->one = NULL;
      repl_cand0->tree_head->two = NULL;
      repl_cand0->tree_head->three = NULL;
      repl_cand0->tree_head->set = hset0;
      repl_cand0->tree_head->way = 1;
      ta = CACHE_MK_BADDR(cp, temp->tag, hset0);
      ha = CACHE_HASH1(cp, ta);
      hset0 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH2(cp, ta);
      hset1 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH3(cp, ta);
      hset2 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH4(cp, ta);
      hset3 = CACHE_SET(cp,ha)%(cp->nsets);
      
      if((cp->sets[hset1].way_two != NULL)){
	temp = (cp->sets[hset1].way_two);
	repl_cand0->tree_head->one = malloc(sizeof(*(repl_cand0->tree_head->one)));
	//repl_cand0->tree_head->one = realloc(repl_cand0->tree_head->one, sizeof(*(repl_cand0->tree_head->one)));
	repl_cand0->tree_head->one->blk = temp;
	//(repl_cand0.tree_head)->one = temp;
	repl_cand0->tree_head->one->parent = repl_cand0->tree_head;
	repl_cand0->tree_head->one->one = NULL;
	repl_cand0->tree_head->one->two = NULL;
	repl_cand0->tree_head->one->three = NULL;
	repl_cand0->tree_head->one->set = hset1;
	repl_cand0->tree_head->one->way = 2;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset1);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if((cp->sets[h0].way_one != NULL)){
	  temp = (cp->sets[h0].way_one);
	  repl_cand0->tree_head->one->one = malloc(sizeof(*(repl_cand0->tree_head->one->one)));
	  //repl_cand0->tree_head->one = realloc(repl_cand0->tree_head->one, sizeof(*(repl_cand0->tree_head->one)));
	  repl_cand0->tree_head->one->one->blk = temp;
	  //(repl_cand0.tree_head)->one = temp;
	  repl_cand0->tree_head->one->one->parent = repl_cand0->tree_head->one;
	  repl_cand0->tree_head->one->one->one = NULL;
	  repl_cand0->tree_head->one->one->two = NULL;
	  repl_cand0->tree_head->one->one->three = NULL;
	  repl_cand0->tree_head->one->one->set = h0;
	  repl_cand0->tree_head->one->one->way = 1;
	}
	else {
	  //repl = cp->sets[hset1].way_two;
	  //hrepl = hset1;
	  //goto miss_handler;
	}
	if((cp->sets[h2].way_three != NULL)){
	  temp = (cp->sets[h2].way_three);
	  repl_cand0->tree_head->one->two = malloc(sizeof(*(repl_cand0->tree_head->one->two)));
	  //repl_cand0->tree_head->two = realloc(repl_cand0->tree_head->two, sizeof(*(repl_cand0->tree_head->two)));
	  repl_cand0->tree_head->one->two->blk = temp;
	  //(repl_cand0.tree_head)->two = temp;
	  repl_cand0->tree_head->one->two->parent = repl_cand0->tree_head->one;
	  repl_cand0->tree_head->one->two->one = NULL;
	  repl_cand0->tree_head->one->two->two = NULL;
	  repl_cand0->tree_head->one->two->three = NULL;
	  repl_cand0->tree_head->one->two->set = h2;
	  repl_cand0->tree_head->one->two->way = 3;
	}
	else {
	  //repl = cp->sets[hset2].way_three;
	  //hrepl = hset2;
	  //goto miss_handler;
	}
	if ((cp->sets[h3].way_four != NULL)){
	  temp = (cp->sets[h3].way_four);
	  repl_cand0->tree_head->one->three = malloc(sizeof(*(repl_cand0->tree_head->one->three)));
	  //repl_cand0->tree_head->three = realloc(repl_cand0->tree_head->three, sizeof(*(repl_cand0->tree_head->three)));
	  repl_cand0->tree_head->one->three->blk = temp;
	  //(repl_cand0.tree_head)->three = temp;
	  repl_cand0->tree_head->one->three->parent = repl_cand0->tree_head->one;
	  repl_cand0->tree_head->one->three->one = NULL;
	  repl_cand0->tree_head->one->three->two = NULL;
	  repl_cand0->tree_head->one->three->three = NULL;
	  repl_cand0->tree_head->one->three->set = h3;
	  repl_cand0->tree_head->one->three->way = 4;
	}
	else {
	  //	repl = cp->sets[hset3].way_four;
	  //hrepl = hset3;
	  //goto miss_handler;
	}
      }
      else {
	//repl = cp->sets[hset1].way_two;
	//hrepl = hset1;
	//goto miss_handler;
      }
      if((cp->sets[hset2].way_three != NULL)){
	temp = (cp->sets[hset2].way_three);
	repl_cand0->tree_head->two = malloc(sizeof(*(repl_cand0->tree_head->two)));
	//repl_cand0->tree_head->two = realloc(repl_cand0->tree_head->two, sizeof(*(repl_cand0->tree_head->two)));
	repl_cand0->tree_head->two->blk = temp;
	//(repl_cand0.tree_head)->two = temp;
	repl_cand0->tree_head->two->parent = repl_cand0->tree_head;
	repl_cand0->tree_head->two->one = NULL;
	repl_cand0->tree_head->two->two = NULL;
	repl_cand0->tree_head->two->three = NULL;
	repl_cand0->tree_head->two->set = hset2;
	repl_cand0->tree_head->two->way = 3;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset2);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if((cp->sets[h0].way_one != NULL)){
	  temp = (cp->sets[h0].way_one);
	  repl_cand0->tree_head->two->one = malloc(sizeof(*(repl_cand0->tree_head->two->one)));
	  //repl_cand0->tree_head->one = realloc(repl_cand0->tree_head->one, sizeof(*(repl_cand0->tree_head->one)));
	  repl_cand0->tree_head->two->one->blk = temp;
	  //(repl_cand0.tree_head)->one = temp;
	  repl_cand0->tree_head->two->one->parent = repl_cand0->tree_head->two;
	  repl_cand0->tree_head->two->one->one = NULL;
	  repl_cand0->tree_head->two->one->two = NULL;
	  repl_cand0->tree_head->two->one->three = NULL;
	  repl_cand0->tree_head->two->one->set = h0;
	  repl_cand0->tree_head->two->one->way = 1;
	}
	else {
	  //repl = cp->sets[hset1].way_two;
	  //hrepl = hset1;
	  //goto miss_handler;
	}
	if((cp->sets[h1].way_two != NULL)){
	  temp = (cp->sets[h1].way_two);
	  repl_cand0->tree_head->two->two = malloc(sizeof(*(repl_cand0->tree_head->two->two)));
	  //repl_cand0->tree_head->two = realloc(repl_cand0->tree_head->two, sizeof(*(repl_cand0->tree_head->two)));
	  repl_cand0->tree_head->two->two->blk = temp;
	  //(repl_cand0.tree_head)->two = temp;
	  repl_cand0->tree_head->two->two->parent = repl_cand0->tree_head->two;
	  repl_cand0->tree_head->two->two->one = NULL;
	  repl_cand0->tree_head->two->two->two = NULL;
	  repl_cand0->tree_head->two->two->three = NULL;
	  repl_cand0->tree_head->two->two->set = h1;
	  repl_cand0->tree_head->two->two->way = 2;
	}
	else {
	  //repl = cp->sets[hset2].way_three;
	  //hrepl = hset2;
	  //goto miss_handler;
	}
	if ((cp->sets[h3].way_four != NULL)){
	  temp = (cp->sets[h3].way_four);
	  repl_cand0->tree_head->two->three = malloc(sizeof(*(repl_cand0->tree_head->two->three)));
	  //repl_cand0->tree_head->three = realloc(repl_cand0->tree_head->three, sizeof(*(repl_cand0->tree_head->three)));
	  repl_cand0->tree_head->two->three->blk = temp;
	  //(repl_cand0.tree_head)->three = temp;
	  repl_cand0->tree_head->two->three->parent = repl_cand0->tree_head->two;
	  repl_cand0->tree_head->two->three->one = NULL;
	  repl_cand0->tree_head->two->three->two = NULL;
	  repl_cand0->tree_head->two->three->three = NULL;
	  repl_cand0->tree_head->two->three->set = h3;
	  repl_cand0->tree_head->two->three->way = 4;
	}
	else {
	  //	repl = cp->sets[hset3].way_four;
	  //hrepl = hset3;
	  //goto miss_handler;
	}
      }
      else {
	//repl = cp->sets[hset2].way_three;
	//hrepl = hset2;
	//goto miss_handler;
      }
      if ((cp->sets[hset3].way_four != NULL)){
	temp = (cp->sets[hset3].way_four);
	repl_cand0->tree_head->three = malloc(sizeof(*(repl_cand0->tree_head->three)));
	//repl_cand0->tree_head->three = realloc(repl_cand0->tree_head->three, sizeof(*(repl_cand0->tree_head->three)));
	repl_cand0->tree_head->three->blk = temp;
	//(repl_cand0.tree_head)->three = temp;
	repl_cand0->tree_head->three->parent = repl_cand0->tree_head;
	repl_cand0->tree_head->three->one = NULL;
	repl_cand0->tree_head->three->two = NULL;
	repl_cand0->tree_head->three->three = NULL;
	repl_cand0->tree_head->three->set = hset3;
	repl_cand0->tree_head->three->way = 4;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset3);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if((cp->sets[h0].way_one != NULL)){
	  temp = (cp->sets[h0].way_one);
	  repl_cand0->tree_head->three->one = malloc(sizeof(*(repl_cand0->tree_head->three->one)));
	  //repl_cand0->tree_head->one = realloc(repl_cand0->tree_head->one, sizeof(*(repl_cand0->tree_head->one)));
	  repl_cand0->tree_head->three->one->blk = temp;
	  //(repl_cand0.tree_head)->one = temp;
	  repl_cand0->tree_head->three->one->parent = repl_cand0->tree_head->three;
	  repl_cand0->tree_head->three->one->one = NULL;
	  repl_cand0->tree_head->three->one->two = NULL;
	  repl_cand0->tree_head->three->one->three = NULL;
	  repl_cand0->tree_head->three->one->set = h0;
	  repl_cand0->tree_head->three->one->way = 1;
	}
	else {
	  //repl = cp->sets[hset1].way_two;
	  //hrepl = hset1;
	  //goto miss_handler;
	}
	if((cp->sets[h1].way_two != NULL)){
	  temp = (cp->sets[h1].way_two);
	  repl_cand0->tree_head->three->two = malloc(sizeof(*(repl_cand0->tree_head->three->two)));
	  //repl_cand0->tree_head->two = realloc(repl_cand0->tree_head->two, sizeof(*(repl_cand0->tree_head->two)));
	  repl_cand0->tree_head->three->two->blk = temp;
	  //(repl_cand0.tree_head)->two = temp;
	  repl_cand0->tree_head->three->two->parent = repl_cand0->tree_head->three;
	  repl_cand0->tree_head->three->two->one = NULL;
	  repl_cand0->tree_head->three->two->two = NULL;
	  repl_cand0->tree_head->three->two->three = NULL;
	  repl_cand0->tree_head->three->two->set = h1;
	  repl_cand0->tree_head->three->two->way = 2;
	}
	else {
	  //repl = cp->sets[hset2].way_three;
	  //hrepl = hset2;
	  //goto miss_handler;
	}
	if ((cp->sets[h2].way_three != NULL)){
	  temp = (cp->sets[h2].way_three);
	  repl_cand0->tree_head->three->three = malloc(sizeof(*(repl_cand0->tree_head->three->three)));
	  //repl_cand0->tree_head->three = realloc(repl_cand0->tree_head->three, sizeof(*(repl_cand0->tree_head->three)));
	  repl_cand0->tree_head->three->three->blk = temp;
	  //(repl_cand0.tree_head)->three = temp;
	  repl_cand0->tree_head->three->three->parent = repl_cand0->tree_head->three;
	  repl_cand0->tree_head->three->three->one = NULL;
	  repl_cand0->tree_head->three->three->two = NULL;
	  repl_cand0->tree_head->three->three->three = NULL;
	  repl_cand0->tree_head->three->three->set = h2;
	  repl_cand0->tree_head->three->three->way = 3;
	}
	else {
	  //	repl = cp->sets[hset3].way_four;
	  //hrepl = hset3;
	  //goto miss_handler;
	}
      }
      else {
	//	repl = cp->sets[hset3].way_four;
	//hrepl = hset3;
	//goto miss_handler;
      }
    }
    else {
      //repl = cp->sets[hset0].way_one;
      //hrepl = hset0;
      //goto miss_handler;
    }

    //Second tree
    //    ta = CACHE_BADDR(cp, addr);
    ha = CACHE_HASH2(cp, addr);
    hset1 = CACHE_SET(cp, ha)%(cp->nsets);

    if((cp->sets[hset1].way_two != NULL)){
      temp = cp->sets[hset1].way_two;
      repl_cand1->tree_head = malloc(sizeof(*(repl_cand1->tree_head)));
      //repl_cand1->tree_head = realloc(repl_cand1->tree_head, sizeof(*(repl_cand1->tree_head)));
      repl_cand1->tree_head->blk = temp;
      //(repl_cand1.tree_head) = temp;
      repl_cand1->tree_head->parent = NULL;
      repl_cand1->tree_head->one = NULL;
      repl_cand1->tree_head->two = NULL;
      repl_cand1->tree_head->three = NULL;
      repl_cand1->tree_head->set = hset1;
      repl_cand1->tree_head->way = 2;
      /*hset0 = CACHE_HASH1(cp, hset1);
	hset1 = CACHE_HASH2(cp, hset1);
	hset2 = CACHE_HASH3(cp, hset1);
	hset3 = CACHE_HASH4(cp, hset1);*/
      ta = CACHE_MK_BADDR(cp, temp->tag, hset1);
      ha = CACHE_HASH1(cp, ta);
      hset0 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH2(cp, ta);
      hset1 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH3(cp, ta);
      hset2 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH4(cp, ta);
      hset3 = CACHE_SET(cp,ha)%(cp->nsets);

      if(cp->sets[hset0].way_one != NULL){
	temp = (cp->sets[hset0].way_one);
	repl_cand1->tree_head->one = malloc(sizeof(*(repl_cand1->tree_head->one)));
	//repl_cand1->tree_head->one = realloc(repl_cand1->tree_head->one, sizeof(*(repl_cand1->tree_head->one)));
	repl_cand1->tree_head->one->blk = temp;
	//(repl_cand1.tree_head)->one = temp;
	repl_cand1->tree_head->one->parent = repl_cand1->tree_head;
	repl_cand1->tree_head->one->one = NULL;
	repl_cand1->tree_head->one->two = NULL;
	repl_cand1->tree_head->one->three = NULL;
	repl_cand1->tree_head->one->set = hset0;
	repl_cand1->tree_head->one->way = 1;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset0);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if(cp->sets[h1].way_two != NULL){
	  temp = (cp->sets[h1].way_two);
	  repl_cand1->tree_head->one->one = malloc(sizeof(*(repl_cand1->tree_head->one->one)));
	  //repl_cand1->tree_head->one = realloc(repl_cand1->tree_head->one, sizeof(*(repl_cand1->tree_head->one)));
	  repl_cand1->tree_head->one->one->blk = temp;
	  //(repl_cand1.tree_head)->one = temp;
	  repl_cand1->tree_head->one->one->parent = repl_cand1->tree_head->one;
	  repl_cand1->tree_head->one->one->one = NULL;
	  repl_cand1->tree_head->one->one->two = NULL;
	  repl_cand1->tree_head->one->one->three = NULL;
	  repl_cand1->tree_head->one->one->set = h1;
	  repl_cand1->tree_head->one->one->way = 2;
	}
	else {
	  //repl = cp->sets[hset0].way_one;
	  //hrepl = hset0;
	  //goto miss_handler;
	}
	if((cp->sets[h2].way_three != NULL)){
	  temp = (cp->sets[h2].way_three);
	  repl_cand1->tree_head->one->two = malloc(sizeof(*(repl_cand1->tree_head->one->two)));
	  //repl_cand1->tree_head->two = realloc(repl_cand1->tree_head->two, sizeof(*(repl_cand1->tree_head->two)));
	  repl_cand1->tree_head->one->two->blk = temp;
	  //(repl_cand1.tree_head)->two = temp;
	  repl_cand1->tree_head->one->two->parent = repl_cand1->tree_head->one;
	  repl_cand1->tree_head->one->two->one = NULL;
	  repl_cand1->tree_head->one->two->two = NULL;
	  repl_cand1->tree_head->one->two->three = NULL;
	  repl_cand1->tree_head->one->two->set = h2;
	  repl_cand1->tree_head->one->two->way = 3;
	}
	else {
	  //repl = cp->sets[hset2].way_three;
	  //hrepl = hset2;
	  //goto miss_handler;
	}
	if ((cp->sets[h3].way_four != NULL)){
	  temp = (cp->sets[h3].way_four);
	  repl_cand1->tree_head->one->three = malloc(sizeof(*(repl_cand1->tree_head->one->three)));
	  //repl_cand1->tree_head->three = realloc(repl_cand1->tree_head->three, sizeof(*(repl_cand1->tree_head->three)));
	  repl_cand1->tree_head->one->three->blk = temp;
	  //(repl_cand1.tree_head)->three = temp;
	  repl_cand1->tree_head->one->three->parent = repl_cand1->tree_head->one;
	  repl_cand1->tree_head->one->three->one = NULL;
	  repl_cand1->tree_head->one->three->two = NULL;
	  repl_cand1->tree_head->one->three->three = NULL;
	  repl_cand1->tree_head->one->three->set = h3;
	  repl_cand1->tree_head->one->three->way = 4;
	}
	else {
	  //	repl = cp->sets[hset3].way_four;
	  //	hrepl = hset3;
	  //goto miss_handler;
	}
      }
      else {
	//repl = cp->sets[hset0].way_one;
	//hrepl = hset0;
	//goto miss_handler;
      }
      if((cp->sets[hset2].way_three != NULL)){
	temp = (cp->sets[hset2].way_three);
	repl_cand1->tree_head->two = malloc(sizeof(*(repl_cand1->tree_head->two)));
	//repl_cand1->tree_head->two = realloc(repl_cand1->tree_head->two, sizeof(*(repl_cand1->tree_head->two)));
	repl_cand1->tree_head->two->blk = temp;
	//(repl_cand1.tree_head)->two = temp;
	repl_cand1->tree_head->two->parent = repl_cand1->tree_head;
	repl_cand1->tree_head->two->one = NULL;
	repl_cand1->tree_head->two->two = NULL;
	repl_cand1->tree_head->two->three = NULL;
	repl_cand1->tree_head->two->set = hset2;
	repl_cand1->tree_head->two->way = 3;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset2);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if(cp->sets[h0].way_one != NULL){
	  temp = (cp->sets[h0].way_one);
	  repl_cand1->tree_head->two->one = malloc(sizeof(*(repl_cand1->tree_head->two->one)));
	  //repl_cand1->tree_head->one = realloc(repl_cand1->tree_head->one, sizeof(*(repl_cand1->tree_head->one)));
	  repl_cand1->tree_head->two->one->blk = temp;
	  //(repl_cand1.tree_head)->one = temp;
	  repl_cand1->tree_head->two->one->parent = repl_cand1->tree_head->two;
	  repl_cand1->tree_head->two->one->one = NULL;
	  repl_cand1->tree_head->two->one->two = NULL;
	  repl_cand1->tree_head->two->one->three = NULL;
	  repl_cand1->tree_head->two->one->set = h0;
	  repl_cand1->tree_head->two->one->way = 1;
	}
	else {
	  //repl = cp->sets[hset0].way_one;
	  //hrepl = hset0;
	  //goto miss_handler;
	}
	if((cp->sets[h1].way_two != NULL)){
	  temp = (cp->sets[h1].way_two);
	  repl_cand1->tree_head->two->two = malloc(sizeof(*(repl_cand1->tree_head->two->two)));
	  //repl_cand1->tree_head->two = realloc(repl_cand1->tree_head->two, sizeof(*(repl_cand1->tree_head->two)));
	  repl_cand1->tree_head->two->two->blk = temp;
	  //(repl_cand1.tree_head)->two = temp;
	  repl_cand1->tree_head->two->two->parent = repl_cand1->tree_head->two;
	  repl_cand1->tree_head->two->two->one = NULL;
	  repl_cand1->tree_head->two->two->two = NULL;
	  repl_cand1->tree_head->two->two->three = NULL;
	  repl_cand1->tree_head->two->two->set = h1;
	  repl_cand1->tree_head->two->two->way = 2;
	}
	else {
	  //repl = cp->sets[hset2].way_three;
	  //hrepl = hset2;
	  //goto miss_handler;
	}
	if ((cp->sets[h3].way_four != NULL)){
	  temp = (cp->sets[h3].way_four);
	  repl_cand1->tree_head->two->three = malloc(sizeof(*(repl_cand1->tree_head->two->three)));
	  //repl_cand1->tree_head->three = realloc(repl_cand1->tree_head->three, sizeof(*(repl_cand1->tree_head->three)));
	  repl_cand1->tree_head->two->three->blk = temp;
	  //(repl_cand1.tree_head)->three = temp;
	  repl_cand1->tree_head->two->three->parent = repl_cand1->tree_head->two;
	  repl_cand1->tree_head->two->three->one = NULL;
	  repl_cand1->tree_head->two->three->two = NULL;
	  repl_cand1->tree_head->two->three->three = NULL;
	  repl_cand1->tree_head->two->three->set = h3;
	  repl_cand1->tree_head->two->three->way = 4;
	}
	else {
	  //	repl = cp->sets[hset3].way_four;
	  //	hrepl = hset3;
	  //goto miss_handler;
	}
      }
      else {
	//repl = cp->sets[hset2].way_three;
	//hrepl = hset2;
	//goto miss_handler;
      }
      if ((cp->sets[hset3].way_four != NULL)){
	temp = (cp->sets[hset3].way_four);
	repl_cand1->tree_head->three = malloc(sizeof(*(repl_cand1->tree_head->three)));
	//repl_cand1->tree_head->three = realloc(repl_cand1->tree_head->three, sizeof(*(repl_cand1->tree_head->three)));
	repl_cand1->tree_head->three->blk = temp;
	//(repl_cand1.tree_head)->three = temp;
	repl_cand1->tree_head->three->parent = repl_cand1->tree_head;
	repl_cand1->tree_head->three->one = NULL;
	repl_cand1->tree_head->three->two = NULL;
	repl_cand1->tree_head->three->three = NULL;
	repl_cand1->tree_head->three->set = hset3;
	repl_cand1->tree_head->three->way = 4;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset3);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if(cp->sets[h0].way_one != NULL){
	  temp = (cp->sets[h0].way_one);
	  repl_cand1->tree_head->three->one = malloc(sizeof(*(repl_cand1->tree_head->three->one)));
	  //repl_cand1->tree_head->one = realloc(repl_cand1->tree_head->one, sizeof(*(repl_cand1->tree_head->one)));
	  repl_cand1->tree_head->three->one->blk = temp;
	  //(repl_cand1.tree_head)->one = temp;
	  repl_cand1->tree_head->three->one->parent = repl_cand1->tree_head->three;
	  repl_cand1->tree_head->three->one->one = NULL;
	  repl_cand1->tree_head->three->one->two = NULL;
	  repl_cand1->tree_head->three->one->three = NULL;
	  repl_cand1->tree_head->three->one->set = h0;
	  repl_cand1->tree_head->three->one->way = 1;
	}
	else {
	  //repl = cp->sets[hset0].way_one;
	  //hrepl = hset0;
	  //goto miss_handler;
	}
	if((cp->sets[h1].way_two != NULL)){
	  temp = (cp->sets[h1].way_two);
	  repl_cand1->tree_head->three->two = malloc(sizeof(*(repl_cand1->tree_head->three->two)));
	  //repl_cand1->tree_head->two = realloc(repl_cand1->tree_head->two, sizeof(*(repl_cand1->tree_head->two)));
	  repl_cand1->tree_head->three->two->blk = temp;
	  //(repl_cand1.tree_head)->two = temp;
	  repl_cand1->tree_head->three->two->parent = repl_cand1->tree_head->three;
	  repl_cand1->tree_head->three->two->one = NULL;
	  repl_cand1->tree_head->three->two->two = NULL;
	  repl_cand1->tree_head->three->two->three = NULL;
	  repl_cand1->tree_head->three->two->set = h1;
	  repl_cand1->tree_head->three->two->way = 2;
	}
	else {
	  //repl = cp->sets[hset2].way_three;
	  //hrepl = hset2;
	  //goto miss_handler;
	}
	if ((cp->sets[h2].way_three != NULL)){
	  temp = (cp->sets[h2].way_three);
	  repl_cand1->tree_head->three->three = malloc(sizeof(*(repl_cand1->tree_head->three->three)));
	  //repl_cand1->tree_head->three = realloc(repl_cand1->tree_head->three, sizeof(*(repl_cand1->tree_head->three)));
	  repl_cand1->tree_head->three->three->blk = temp;
	  //(repl_cand1.tree_head)->three = temp;
	  repl_cand1->tree_head->three->three->parent = repl_cand1->tree_head->three;
	  repl_cand1->tree_head->three->three->one = NULL;
	  repl_cand1->tree_head->three->three->two = NULL;
	  repl_cand1->tree_head->three->three->three = NULL;
	  repl_cand1->tree_head->three->three->set = h2;
	  repl_cand1->tree_head->three->three->way = 3;
	}
	else {
	  //	repl = cp->sets[hset3].way_four;
	  //	hrepl = hset3;
	  //goto miss_handler;
	}
      }
      else {
	//	repl = cp->sets[hset3].way_four;
	//	hrepl = hset3;
	//goto miss_handler;
      }
    }
    else {
      // repl = cp->sets[hset1].way_two;
      // hrepl = hset1;
      // goto miss_handler;
    }
    
    //Third tree
    //    ta = CACHE_BADDR(cp, addr);
    ha = CACHE_HASH3(cp, addr);
    hset2 = CACHE_SET(cp, ha)%(cp->nsets);

    if((cp->sets[hset2].way_three != NULL)){
      temp = (cp->sets[hset2].way_three);
      repl_cand2->tree_head = malloc(sizeof(*(repl_cand2->tree_head)));
      //repl_cand2->tree_head = realloc(repl_cand2->tree_head, sizeof(*(repl_cand2->tree_head)));
      repl_cand2->tree_head->blk = temp;
      //(repl_cand2.tree_head) = temp;
      repl_cand2->tree_head->parent = NULL;
      repl_cand2->tree_head->one = NULL;
      repl_cand2->tree_head->two = NULL;
      repl_cand2->tree_head->three = NULL;
      repl_cand2->tree_head->set = hset2;
      repl_cand2->tree_head->way = 3;
      /*hset0 = CACHE_HASH1(cp, hset2);
	hset1 = CACHE_HASH2(cp, hset2);
	hset2 = CACHE_HASH3(cp, hset2);
	hset3 = CACHE_HASH4(cp, hset2);
      */
      ta = CACHE_MK_BADDR(cp, temp->tag, hset2);
      ha = CACHE_HASH1(cp, ta);
      hset0 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH2(cp, ta);
      hset1 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH3(cp, ta);
      hset2 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH4(cp, ta);
      hset3 = CACHE_SET(cp,ha)%(cp->nsets);

      if((cp->sets[hset0].way_one != NULL)){
	temp = (cp->sets[hset0].way_one);
	repl_cand2->tree_head->one = malloc(sizeof(*(repl_cand2->tree_head->one)));
	//repl_cand2->tree_head->one = realloc(repl_cand2->tree_head->one, sizeof(*(repl_cand2->tree_head->one)));
	repl_cand2->tree_head->one->blk = temp;
	//(repl_cand2.tree_head)->one = temp;
	repl_cand2->tree_head->one->parent = repl_cand2->tree_head;
	repl_cand2->tree_head->one->one = NULL;
	repl_cand2->tree_head->one->two = NULL;
	repl_cand2->tree_head->one->three = NULL;
	repl_cand2->tree_head->one->set = hset0;
	repl_cand2->tree_head->one->way = 1;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset0);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if((cp->sets[h1].way_two != NULL)){
	  temp = (cp->sets[h1].way_two);
	  repl_cand2->tree_head->one->one = malloc(sizeof(*(repl_cand2->tree_head->one->one)));
	  //repl_cand2->tree_head->one = realloc(repl_cand2->tree_head->one, sizeof(*(repl_cand2->tree_head->one)));
	  repl_cand2->tree_head->one->one->blk = temp;
	  //(repl_cand2.tree_head)->one = temp;
	  repl_cand2->tree_head->one->one->parent = repl_cand2->tree_head->one;
	  repl_cand2->tree_head->one->one->one = NULL;
	  repl_cand2->tree_head->one->one->two = NULL;
	  repl_cand2->tree_head->one->one->three = NULL;
	  repl_cand2->tree_head->one->one->set = h1;
	  repl_cand2->tree_head->one->one->way = 2;
	}
	else {
	  //repl = cp->sets[hset0].way_one;
	  //hrepl = hset0;
	  //goto miss_handler;
	} 
	if((cp->sets[h2].way_three != NULL)){
	  temp = (cp->sets[h2].way_three);
	  repl_cand2->tree_head->one->two = malloc(sizeof(*(repl_cand2->tree_head->one->two)));
	  //repl_cand2->tree_head->two = realloc(repl_cand2->tree_head->two, sizeof(*(repl_cand2->tree_head->two)));
	  repl_cand2->tree_head->one->two->blk = temp;
	  //(repl_cand2.tree_head)->two = temp;
	  repl_cand2->tree_head->one->two->parent = repl_cand2->tree_head->one;
	  repl_cand2->tree_head->one->two->one = NULL;
	  repl_cand2->tree_head->one->two->two = NULL;
	  repl_cand2->tree_head->one->two->three = NULL;
	  repl_cand2->tree_head->one->two->set = h2;
	  repl_cand2->tree_head->one->two->way = 3;
	}
	else {
	  //repl = cp->sets[hset1].way_two;
	  //hrepl = hset1;
	  //goto miss_handler;
	}
	if ((cp->sets[h3].way_four != NULL)){
	  temp = (cp->sets[h3].way_four);
	  repl_cand2->tree_head->one->three = malloc(sizeof(*(repl_cand2->tree_head->one->three)));
	  //repl_cand2->tree_head->three = realloc(repl_cand2->tree_head->three, sizeof(*(repl_cand2->tree_head->three)));
	  repl_cand2->tree_head->one->three->blk = temp;
	  //(repl_cand2.tree_head)->three = temp;
	  repl_cand2->tree_head->one->three->parent = repl_cand2->tree_head->one;
	  repl_cand2->tree_head->one->three->one = NULL;
	  repl_cand2->tree_head->one->three->two = NULL;
	  repl_cand2->tree_head->one->three->three = NULL;
	  repl_cand2->tree_head->one->three->set = h3;
	  repl_cand2->tree_head->one->three->way = 4;
	}
	else {
	  //repl = cp->sets[hset3].way_four;
	  //hrepl = hset3;
	  //goto miss_handler;
	}
      }
      else {
	//repl = cp->sets[hset0].way_one;
	//hrepl = hset0;
	//goto miss_handler;
      } 
      if((cp->sets[hset1].way_two != NULL)){
	temp = (cp->sets[hset1].way_two);
	repl_cand2->tree_head->two = malloc(sizeof(*(repl_cand2->tree_head->two)));
	//repl_cand2->tree_head->two = realloc(repl_cand2->tree_head->two, sizeof(*(repl_cand2->tree_head->two)));
	repl_cand2->tree_head->two->blk = temp;
	//(repl_cand2.tree_head)->two = temp;
	repl_cand2->tree_head->two->parent = repl_cand2->tree_head;
	repl_cand2->tree_head->two->one = NULL;
	repl_cand2->tree_head->two->two = NULL;
	repl_cand2->tree_head->two->three = NULL;
	repl_cand2->tree_head->two->set = hset1;
	repl_cand2->tree_head->two->way = 2;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset1);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if((cp->sets[h0].way_one != NULL)){
	  temp = (cp->sets[h0].way_one);
	  repl_cand2->tree_head->two->one = malloc(sizeof(*(repl_cand2->tree_head->two->one)));
	  //repl_cand2->tree_head->one = realloc(repl_cand2->tree_head->one, sizeof(*(repl_cand2->tree_head->one)));
	  repl_cand2->tree_head->two->one->blk = temp;
	  //(repl_cand2.tree_head)->one = temp;
	  repl_cand2->tree_head->two->one->parent = repl_cand2->tree_head->two;
	  repl_cand2->tree_head->two->one->one = NULL;
	  repl_cand2->tree_head->two->one->two = NULL;
	  repl_cand2->tree_head->two->one->three = NULL;
	  repl_cand2->tree_head->two->one->set = h0;
	  repl_cand2->tree_head->two->one->way = 1;
	}
	else {
	  //repl = cp->sets[hset0].way_one;
	  //hrepl = hset0;
	  //goto miss_handler;
	} 
	if((cp->sets[h2].way_three != NULL)){
	  temp = (cp->sets[h2].way_three);
	  repl_cand2->tree_head->two->two = malloc(sizeof(*(repl_cand2->tree_head->two->two)));
	  //repl_cand2->tree_head->two = realloc(repl_cand2->tree_head->two, sizeof(*(repl_cand2->tree_head->two)));
	  repl_cand2->tree_head->two->two->blk = temp;
	  //(repl_cand2.tree_head)->two = temp;
	  repl_cand2->tree_head->two->two->parent = repl_cand2->tree_head->two;
	  repl_cand2->tree_head->two->two->one = NULL;
	  repl_cand2->tree_head->two->two->two = NULL;
	  repl_cand2->tree_head->two->two->three = NULL;
	  repl_cand2->tree_head->two->two->set = h2;
	  repl_cand2->tree_head->two->two->way = 3;
	}
	else {
	  //repl = cp->sets[hset1].way_two;
	  //hrepl = hset1;
	  //goto miss_handler;
	}
	if ((cp->sets[h3].way_four != NULL)){
	  temp = (cp->sets[h3].way_four);
	  repl_cand2->tree_head->two->three = malloc(sizeof(*(repl_cand2->tree_head->two->three)));
	  //repl_cand2->tree_head->three = realloc(repl_cand2->tree_head->three, sizeof(*(repl_cand2->tree_head->three)));
	  repl_cand2->tree_head->two->three->blk = temp;
	  //(repl_cand2.tree_head)->three = temp;
	  repl_cand2->tree_head->two->three->parent = repl_cand2->tree_head->two;
	  repl_cand2->tree_head->two->three->one = NULL;
	  repl_cand2->tree_head->two->three->two = NULL;
	  repl_cand2->tree_head->two->three->three = NULL;
	  repl_cand2->tree_head->two->three->set = h3;
	  repl_cand2->tree_head->two->three->way = 4;
	}
	else {
	  //repl = cp->sets[hset3].way_four;
	  //hrepl = hset3;
	  //goto miss_handler;
	}
      }
      else {
	//repl = cp->sets[hset1].way_two;
	//hrepl = hset1;
	//goto miss_handler;
      }
      if ((cp->sets[hset3].way_four != NULL)){
	temp = (cp->sets[hset3].way_four);
	repl_cand2->tree_head->three = malloc(sizeof(*(repl_cand2->tree_head->three)));
	//repl_cand2->tree_head->three = realloc(repl_cand2->tree_head->three, sizeof(*(repl_cand2->tree_head->three)));
	repl_cand2->tree_head->three->blk = temp;
	//(repl_cand2.tree_head)->three = temp;
	repl_cand2->tree_head->three->parent = repl_cand2->tree_head;
	repl_cand2->tree_head->three->one = NULL;
	repl_cand2->tree_head->three->two = NULL;
	repl_cand2->tree_head->three->three = NULL;
	repl_cand2->tree_head->three->set = hset3;
	repl_cand2->tree_head->three->way = 4;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset3);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if((cp->sets[h0].way_one != NULL)){
	  temp = (cp->sets[h0].way_one);
	  repl_cand2->tree_head->three->one = malloc(sizeof(*(repl_cand2->tree_head->three->one)));
	  //repl_cand2->tree_head->one = realloc(repl_cand2->tree_head->one, sizeof(*(repl_cand2->tree_head->one)));
	  repl_cand2->tree_head->three->one->blk = temp;
	  //(repl_cand2.tree_head)->one = temp;
	  repl_cand2->tree_head->three->one->parent = repl_cand2->tree_head->three;
	  repl_cand2->tree_head->three->one->one = NULL;
	  repl_cand2->tree_head->three->one->two = NULL;
	  repl_cand2->tree_head->three->one->three = NULL;
	  repl_cand2->tree_head->three->one->set = h0;
	  repl_cand2->tree_head->three->one->way = 1;
	}
	else {
	  //repl = cp->sets[hset0].way_one;
	  //hrepl = hset0;
	  //goto miss_handler;
	} 
	if((cp->sets[h1].way_two != NULL)){
	  temp = (cp->sets[h1].way_two);
	  repl_cand2->tree_head->three->two = malloc(sizeof(*(repl_cand2->tree_head->three->two)));
	  //repl_cand2->tree_head->two = realloc(repl_cand2->tree_head->two, sizeof(*(repl_cand2->tree_head->two)));
	  repl_cand2->tree_head->three->two->blk = temp;
	  //(repl_cand2.tree_head)->two = temp;
	  repl_cand2->tree_head->three->two->parent = repl_cand2->tree_head->three;
	  repl_cand2->tree_head->three->two->one = NULL;
	  repl_cand2->tree_head->three->two->two = NULL;
	  repl_cand2->tree_head->three->two->three = NULL;
	  repl_cand2->tree_head->three->two->set = h1;
	  repl_cand2->tree_head->three->two->way = 2;
	}
	else {
	  //repl = cp->sets[hset1].way_two;
	  //hrepl = hset1;
	  //goto miss_handler;
	}
	if ((cp->sets[h2].way_three != NULL)){
	  temp = (cp->sets[h2].way_three);
	  repl_cand2->tree_head->three->three = malloc(sizeof(*(repl_cand2->tree_head->three->three)));
	  //repl_cand2->tree_head->three = realloc(repl_cand2->tree_head->three, sizeof(*(repl_cand2->tree_head->three)));
	  repl_cand2->tree_head->three->three->blk = temp;
	  //(repl_cand2.tree_head)->three = temp;
	  repl_cand2->tree_head->three->three->parent = repl_cand2->tree_head->three;
	  repl_cand2->tree_head->three->three->one = NULL;
	  repl_cand2->tree_head->three->three->two = NULL;
	  repl_cand2->tree_head->three->three->three = NULL;
	  repl_cand2->tree_head->three->three->set = h2;
	  repl_cand2->tree_head->three->three->way = 3;
	}
	else {
	  //repl = cp->sets[hset3].way_four;
	  //hrepl = hset3;
	  //goto miss_handler;
	}
      }
      else {
	//repl = cp->sets[hset3].way_four;
	//hrepl = hset3;
	//goto miss_handler;
      }
    }
    else {
      //repl = cp->sets[hset2].way_three;
      //hrepl = hset2;
      //goto miss_handler;
    }
    
    //Fourth tree
    //    ta = CACHE_BADDR(cp, addr);
    ha = CACHE_HASH4(cp, addr);
    hset3 = CACHE_SET(cp, ha)%(cp->nsets);
    if ((cp->sets[hset3].way_four != NULL)){
      temp = cp->sets[hset3].way_four;
      repl_cand3->tree_head = malloc(sizeof(*(repl_cand3->tree_head)));
      //repl_cand3->tree_head = realloc(repl_cand3->tree_head, sizeof(*(repl_cand3->tree_head)));
      repl_cand3->tree_head->blk = temp;
      //(repl_cand3.tree_head) = temp;
      repl_cand3->tree_head->parent = NULL;
      repl_cand3->tree_head->one = NULL;
      repl_cand3->tree_head->two = NULL;
      repl_cand3->tree_head->three = NULL;
      repl_cand3->tree_head->set = hset3;
      repl_cand3->tree_head->way = 4;
      /*hset0 = CACHE_HASH1(cp, hset3);
	hset1 = CACHE_HASH2(cp, hset3);
	hset2 = CACHE_HASH3(cp, hset3);
	hset3 = CACHE_HASH4(cp, hset3);*/
      ta = CACHE_MK_BADDR(cp, temp->tag, hset3);
      ha = CACHE_HASH1(cp, ta);
      hset0 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH2(cp, ta);
      hset1 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH3(cp, ta);
      hset2 = CACHE_SET(cp,ha)%(cp->nsets);
      ha = CACHE_HASH4(cp, ta);
      hset3 = CACHE_SET(cp,ha)%(cp->nsets);
      if((cp->sets[hset0].way_one != NULL)){
	temp = (cp->sets[hset0].way_one);
	repl_cand3->tree_head->one = malloc(sizeof(*(repl_cand3->tree_head->one)));
	//repl_cand3->tree_head->one = realloc(repl_cand3->tree_head->one, sizeof(*(repl_cand3->tree_head->one)));
	repl_cand3->tree_head->one->blk = temp;
	//(repl_cand3.tree_head)->one = temp;
	repl_cand3->tree_head->one->parent = repl_cand3->tree_head;
	repl_cand3->tree_head->one->one = NULL;
	repl_cand3->tree_head->one->two = NULL;
	repl_cand3->tree_head->one->three = NULL;
	repl_cand3->tree_head->one->set = hset0;
	repl_cand3->tree_head->one->way = 1;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset0);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if((cp->sets[h1].way_two != NULL)){
	  temp = (cp->sets[h1].way_two);
	  repl_cand3->tree_head->one->one = malloc(sizeof(*(repl_cand3->tree_head->one->one)));
	  //repl_cand3->tree_head->one = realloc(repl_cand3->tree_head->one, sizeof(*(repl_cand3->tree_head->one)));
	  repl_cand3->tree_head->one->one->blk = temp;
	  //(repl_cand3.tree_head)->one = temp;
	  repl_cand3->tree_head->one->one->parent = repl_cand3->tree_head->one;
	  repl_cand3->tree_head->one->one->one = NULL;
	  repl_cand3->tree_head->one->one->two = NULL;
	  repl_cand3->tree_head->one->one->three = NULL;
	  repl_cand3->tree_head->one->one->set = h1;
	  repl_cand3->tree_head->one->one->way = 2;
	}
	else {
	  //repl = cp->sets[hset0].way_one;
	  //hrepl = hset0;
	  //goto miss_handler;
	}
	if((cp->sets[h2].way_three != NULL)){
	  temp = (cp->sets[h2].way_three);
	  repl_cand3->tree_head->one->two = malloc(sizeof(*(repl_cand3->tree_head->one->two)));
	  //repl_cand3->tree_head->two = realloc(repl_cand3->tree_head->two, sizeof(*(repl_cand3->tree_head->two)));
	  repl_cand3->tree_head->one->two->blk = temp;
	  //(repl_cand3.tree_head)->two = temp;
	  repl_cand3->tree_head->one->two->parent = repl_cand3->tree_head->one;
	  repl_cand3->tree_head->one->two->one = NULL;
	  repl_cand3->tree_head->one->two->two = NULL;
	  repl_cand3->tree_head->one->two->three = NULL;
	  repl_cand3->tree_head->one->two->set = h2;
	  repl_cand3->tree_head->one->two->way = 3;
	}
	else {
	  //repl = cp->sets[hset1].way_two;
	  //hrepl = hset1;
	  //goto miss_handler;
	}
	if((cp->sets[h3].way_four != NULL)){
	  temp = (cp->sets[h3].way_four);
	  repl_cand3->tree_head->one->three = malloc(sizeof(*(repl_cand3->tree_head->one->three)));
	  //repl_cand3->tree_head->three = realloc(repl_cand3->tree_head->three, sizeof(*(repl_cand3->tree_head->three)));
	  repl_cand3->tree_head->one->three->blk = temp;
	  //(repl_cand3.tree_head)->three = temp;
	  repl_cand3->tree_head->one->three->parent = repl_cand3->tree_head->one;
	  repl_cand3->tree_head->one->three->one = NULL;
	  repl_cand3->tree_head->one->three->two = NULL;
	  repl_cand3->tree_head->one->three->three = NULL;
	  repl_cand3->tree_head->one->three->set = h3;
	  repl_cand3->tree_head->one->three->way = 4;
	}
	else {
	  //repl = cp->sets[hset2].way_three;
	  //hrepl = hset2;
	  //goto miss_handler;
	}
      }
      else {
	//repl = cp->sets[hset0].way_one;
	//hrepl = hset0;
	//goto miss_handler;
      }
      if((cp->sets[hset1].way_two != NULL)){
	temp = (cp->sets[hset1].way_two);
	repl_cand3->tree_head->two = malloc(sizeof(*(repl_cand3->tree_head->two)));
	//repl_cand3->tree_head->two = realloc(repl_cand3->tree_head->two, sizeof(*(repl_cand3->tree_head->two)));
	repl_cand3->tree_head->two->blk = temp;
	//(repl_cand3.tree_head)->two = temp;
	repl_cand3->tree_head->two->parent = repl_cand3->tree_head;
	repl_cand3->tree_head->two->one = NULL;
	repl_cand3->tree_head->two->two = NULL;
	repl_cand3->tree_head->two->three = NULL;
	repl_cand3->tree_head->two->set = hset1;
	repl_cand3->tree_head->two->way = 2;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset1);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if((cp->sets[h0].way_one != NULL)){
	  temp = (cp->sets[h0].way_one);
	  repl_cand3->tree_head->two->one = malloc(sizeof(*(repl_cand3->tree_head->two->one)));
	  //repl_cand3->tree_head->one = realloc(repl_cand3->tree_head->one, sizeof(*(repl_cand3->tree_head->one)));
	  repl_cand3->tree_head->two->one->blk = temp;
	  //(repl_cand3.tree_head)->one = temp;
	  repl_cand3->tree_head->two->one->parent = repl_cand3->tree_head->two;
	  repl_cand3->tree_head->two->one->one = NULL;
	  repl_cand3->tree_head->two->one->two = NULL;
	  repl_cand3->tree_head->two->one->three = NULL;
	  repl_cand3->tree_head->two->one->set = h0;
	  repl_cand3->tree_head->two->one->way = 1;
	}
	else {
	  //repl = cp->sets[hset0].way_one;
	  //hrepl = hset0;
	  //goto miss_handler;
	}
	if((cp->sets[h2].way_three != NULL)){
	  temp = (cp->sets[h2].way_three);
	  repl_cand3->tree_head->two->two = malloc(sizeof(*(repl_cand3->tree_head->two->two)));
	  //repl_cand3->tree_head->two = realloc(repl_cand3->tree_head->two, sizeof(*(repl_cand3->tree_head->two)));
	  repl_cand3->tree_head->two->two->blk = temp;
	  //(repl_cand3.tree_head)->two = temp;
	  repl_cand3->tree_head->two->two->parent = repl_cand3->tree_head->two;
	  repl_cand3->tree_head->two->two->one = NULL;
	  repl_cand3->tree_head->two->two->two = NULL;
	  repl_cand3->tree_head->two->two->three = NULL;
	  repl_cand3->tree_head->two->two->set = h2;
	  repl_cand3->tree_head->two->two->way = 3;
	}
	else {
	  //repl = cp->sets[hset1].way_two;
	  //hrepl = hset1;
	  //goto miss_handler;
	}
	if((cp->sets[h3].way_four != NULL)){
	  temp = (cp->sets[h3].way_four);
	  repl_cand3->tree_head->two->three = malloc(sizeof(*(repl_cand3->tree_head->two->three)));
	  //repl_cand3->tree_head->three = realloc(repl_cand3->tree_head->three, sizeof(*(repl_cand3->tree_head->three)));
	  repl_cand3->tree_head->two->three->blk = temp;
	  //(repl_cand3.tree_head)->three = temp;
	  repl_cand3->tree_head->two->three->parent = repl_cand3->tree_head->two;
	  repl_cand3->tree_head->two->three->one = NULL;
	  repl_cand3->tree_head->two->three->two = NULL;
	  repl_cand3->tree_head->two->three->three = NULL;
	  repl_cand3->tree_head->two->three->set = h3;
	  repl_cand3->tree_head->two->three->way = 4;
	}
	else {
	  //repl = cp->sets[hset2].way_three;
	  //hrepl = hset2;
	  //goto miss_handler;
	}
      }
      else {
	//repl = cp->sets[hset1].way_two;
	//hrepl = hset1;
	//goto miss_handler;
      }
      if((cp->sets[hset2].way_three != NULL)){
	temp = (cp->sets[hset2].way_three);
	repl_cand3->tree_head->three = malloc(sizeof(*(repl_cand3->tree_head->three)));
	//repl_cand3->tree_head->three = realloc(repl_cand3->tree_head->three, sizeof(*(repl_cand3->tree_head->three)));
	repl_cand3->tree_head->three->blk = temp;
	//(repl_cand3.tree_head)->three = temp;
	repl_cand3->tree_head->three->parent = repl_cand3->tree_head;
	repl_cand3->tree_head->three->one = NULL;
	repl_cand3->tree_head->three->two = NULL;
	repl_cand3->tree_head->three->three = NULL;
	repl_cand3->tree_head->three->set = hset2;
	repl_cand3->tree_head->three->way = 3;
	taa = CACHE_MK_BADDR(cp, temp->tag, hset2);
	ha = CACHE_HASH1(cp, taa);
	h0 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH2(cp, taa);
	h1 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH3(cp, taa);
	h2 = CACHE_SET(cp,ha)%(cp->nsets);
	ha = CACHE_HASH4(cp, taa);
	h3 = CACHE_SET(cp,ha)%(cp->nsets);
	if((cp->sets[h0].way_one != NULL)){
	  temp = (cp->sets[h0].way_one);
	  repl_cand3->tree_head->three->one = malloc(sizeof(*(repl_cand3->tree_head->three->one)));
	  //repl_cand3->tree_head->one = realloc(repl_cand3->tree_head->one, sizeof(*(repl_cand3->tree_head->one)));
	  repl_cand3->tree_head->three->one->blk = temp;
	  //(repl_cand3.tree_head)->one = temp;
	  repl_cand3->tree_head->three->one->parent = repl_cand3->tree_head->three;
	  repl_cand3->tree_head->three->one->one = NULL;
	  repl_cand3->tree_head->three->one->two = NULL;
	  repl_cand3->tree_head->three->one->three = NULL;
	  repl_cand3->tree_head->three->one->set = h0;
	  repl_cand3->tree_head->three->one->way = 1;
	}
	else {
	  //repl = cp->sets[hset0].way_one;
	  //hrepl = hset0;
	  //goto miss_handler;
	}
	if((cp->sets[h1].way_two != NULL)){
	  temp = (cp->sets[h1].way_two);
	  repl_cand3->tree_head->three->two = malloc(sizeof(*(repl_cand3->tree_head->three->two)));
	  //repl_cand3->tree_head->two = realloc(repl_cand3->tree_head->two, sizeof(*(repl_cand3->tree_head->two)));
	  repl_cand3->tree_head->three->two->blk = temp;
	  //(repl_cand3.tree_head)->two = temp;
	  repl_cand3->tree_head->three->two->parent = repl_cand3->tree_head->three;
	  repl_cand3->tree_head->three->two->one = NULL;
	  repl_cand3->tree_head->three->two->two = NULL;
	  repl_cand3->tree_head->three->two->three = NULL;
	  repl_cand3->tree_head->three->two->set = h1;
	  repl_cand3->tree_head->three->two->way = 2;
	}
	else {
	  //repl = cp->sets[hset1].way_two;
	  //hrepl = hset1;
	  //goto miss_handler;
	}
	if((cp->sets[h3].way_four != NULL)){
	  temp = (cp->sets[h3].way_four);
	  repl_cand3->tree_head->three->three = malloc(sizeof(*(repl_cand3->tree_head->three->three)));
	  //repl_cand3->tree_head->three = realloc(repl_cand3->tree_head->three, sizeof(*(repl_cand3->tree_head->three)));
	  repl_cand3->tree_head->three->three->blk = temp;
	  //(repl_cand3.tree_head)->three = temp;
	  repl_cand3->tree_head->three->three->parent = repl_cand3->tree_head->three;
	  repl_cand3->tree_head->three->three->one = NULL;
	  repl_cand3->tree_head->three->three->two = NULL;
	  repl_cand3->tree_head->three->three->three = NULL;
	  repl_cand3->tree_head->three->three->set = h3;
	  repl_cand3->tree_head->three->three->way = 4;
	}
	else {
	  //repl = cp->sets[hset2].way_three;
	  //hrepl = hset2;
	  //goto miss_handler;
	}
      }
      else {
	//repl = cp->sets[hset2].way_three;
	//hrepl = hset2;
	//goto miss_handler;
      }
    }
    else {
      //repl = cp->sets[hset3].way_four;
      //hrepl = hset3;
      //goto miss_handler;
    }
    
    repl_node = find_repl_node (cp, repl_cand0, repl_cand1, repl_cand2, repl_cand3);
    repl  = repl_node->blk;     
    if(repl_node->rset < cp->nsets){
      hrepl = repl_node->rset;
    }
    else
      hrepl = repl_node->set;
    if(hrepl >= cp->nsets){
      hrepl = set;
    }
    rep_lat += (12*(2)+1);
  }
  miss_handler:
  
  /* remove this block from the hash bucket chain, if hash exists */
  if (cp->hsize)
    unlink_htab_ent(cp, &cp->sets[set], repl);

  /* blow away the last block to hit */
  cp->last_tagset = 0;
  cp->last_blk = NULL;

  /* write back replaced block data */
  if (repl->status & CACHE_BLK_VALID)
    {
      cp->replacements++;

      if (repl_addr)
	*repl_addr = CACHE_MK_BADDR(cp, repl->tag, repl->set);
	//*repl_addr = CACHE_BADDR(cp, addr);

      /* don't replace the block until outstanding misses are satisfied */
      lat += BOUND_POS(repl->ready - now);
 
      /* stall until the bus to next level of memory is available */
      lat += BOUND_POS(cp->bus_free - (now + lat));
 
      /* track bus resource usage */
      cp->bus_free = MAX(cp->bus_free, (now + lat)) + 1;
      
      //if ((repl->tag == 0) && repl->addr == 0)
      //repl->addr = CACHE_MK_BADDR(cp, repl->tag, hrepl);
      
      if (repl->status & CACHE_BLK_DIRTY)
	{
	  /* write back the cache block */
	  cp->writebacks++;
	  lat += cp->blk_access_fn(Write, /*CACHE_BADDR(cp, repl->addr)*/CACHE_MK_BADDR(cp, repl->tag, repl->set),
				   cp->bsize, repl, now+lat);
	}
    }

  /* update block tags */
  repl->tag = tag;
  repl->status = CACHE_BLK_VALID;	/* dirty bit set on update */
  
  /* read data block */
  lat += cp->blk_access_fn(Read, CACHE_BADDR(cp, addr), cp->bsize,
			   repl, now+lat);

  //code modification
  /* copy data out of cache block */
  if (cp->balloc)
    {
      CACHE_BCOPY(cmd, repl, bofs, p, nbytes);
    }
  repl->set = set;
  repl->addr = addr;
  /* update dirty status */
  if (cmd == Write)
    repl->status |= CACHE_BLK_DIRTY;

  /* get user block data, if requested and it exists */
  if (udata)
    *udata = repl->user_data;

  /* update block status */
  repl->ready = now+lat;
  repl->last_access = now+lat+rep_lat;
  cp->last_tagset = CACHE_TAGSET(cp, addr);
  cp->last_blk = repl;

  /* link this entry back into the hash table */
  if (cp->hsize)
    link_htab_ent(cp, &cp->sets[set], repl);

  /* return latency of the operation */
  //  delTree(&repl_cand0, &repl_cand1, &repl_cand2, &repl_cand3);
  if(!strcmp(cp->name,"ul2"))
    delTree(repl_cand0, repl_cand1, repl_cand2, repl_cand3);
  return (lat+rep_lat);


 cache_hit: /* slow hit handler */
  
  /* **HIT** */
  cp->hits++;

  // copy data out of cache block, if block exists 
  if (cp->balloc)
    {
      CACHE_BCOPY(cmd, blk, bofs, p, nbytes);
    }

  /* update dirty status */
  if (cmd == Write)
    blk->status |= CACHE_BLK_DIRTY;
 
  //code modification
  lat = (int) MAX(cp->hit_latency, (blk->ready - now));
  blk->last_access = now+lat+rep_lat;

  // Code modification
  // if LRU replacement and this is not the first element of list, reorder 
  if (strcmp(cp->name,"ul2") != 0){
    if (blk->way_prev && cp->policy == LRU)
      {
	// move this block to head of the way (MRU) list 
	update_way_list(&cp->sets[set], blk, Head);
      }
  }
  // tag is unchanged, so hash links (if they exist) are still valid

  // record the last block to hit 
  cp->last_tagset = CACHE_TAGSET(cp, addr);
  cp->last_blk = blk;

  // get user block data, if requested and it exists
  if (udata)
    *udata = blk->user_data;

  // return first cycle data is available to access
  return ((int) MAX(cp->hit_latency, (blk->ready - now)) + rep_lat);

 cache_fast_hit: /* fast hit handler */
  
  /* **FAST HIT** */
  cp->hits++;

  /* copy data out of cache block, if block exists */
  if (cp->balloc)
    {
      CACHE_BCOPY(cmd, blk, bofs, p, nbytes);
    }

  lat = (int) MAX(cp->hit_latency, (blk->ready - now));
  blk->last_access = now+lat+rep_lat;
  /* update dirty status */
  if (cmd == Write)
    blk->status |= CACHE_BLK_DIRTY;

  /* this block hit last, no change in the way list */

  /* tag is unchanged, so hash links (if they exist) are still valid */

  /* get user block data, if requested and it exists */
  if (udata)
    *udata = blk->user_data;

  /* record the last block to hit */
  //cp->last_tagset = CACHE_TAGSET(cp, addr);
  //  cp->last_blk = blk;

  /* return first cycle data is available to access */
  return ((int) MAX(cp->hit_latency, (blk->ready - now)) + rep_lat);
}

/* return non-zero if block containing address ADDR is contained in cache
   CP, this interface is used primarily for debugging and asserting cache
   invariants */
int					/* non-zero if access would hit */
cache_probe(struct cache_t *cp,		/* cache instance to probe */
	    md_addr_t addr)		/* address of block to probe */
{
  md_addr_t tag = CACHE_TAG(cp, addr);
  md_addr_t set = CACHE_SET(cp, addr);
  struct cache_blk_t *blk;

  /* permissions are checked on cache misses */

  if (cp->hsize)
  {
    /* higly-associativity cache, access through the per-set hash tables */
    int hindex = CACHE_HASH(cp, tag);
    
    for (blk=cp->sets[set].hash[hindex];
	 blk;
	 blk=blk->hash_next)
    {	
      if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	  return TRUE;
    }
  }
  else
  {
    /* low-associativity cache, linear search the way list */
    for (blk=cp->sets[set].way_head;
	 blk;
	 blk=blk->way_next)
    {
      if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	  return TRUE;
    }
  }
  
  /* cache block not found */
  return FALSE;
}

/* flush the entire cache, returns latency of the operation */
unsigned int				/* latency of the flush operation */
cache_flush(struct cache_t *cp,		/* cache instance to flush */
	    tick_t now)			/* time of cache flush */
{
  int i, lat = cp->hit_latency; /* min latency to probe cache */
  struct cache_blk_t *blk;

  /* blow away the last block to hit */
  cp->last_tagset = 0;
  cp->last_blk = NULL;

  /* no way list updates required because all blocks are being invalidated */
  for (i=0; i<cp->nsets; i++)
    {
      for (blk=cp->sets[i].way_head; blk; blk=blk->way_next)
	{
	  if (blk->status & CACHE_BLK_VALID)
	    {
	      cp->invalidations++;
	      blk->status &= ~CACHE_BLK_VALID;

	      if (blk->status & CACHE_BLK_DIRTY)
		{
		  /* write back the invalidated block */
          	  cp->writebacks++;
		  lat += cp->blk_access_fn(Write,
					   CACHE_MK_BADDR(cp, blk->tag, i),
					   cp->bsize, blk, now+lat);
		}
	    }
	}
    }

  /* return latency of the flush operation */
  return lat;
}

/* flush the block containing ADDR from the cache CP, returns the latency of
   the block flush operation */
unsigned int				/* latency of flush operation */
cache_flush_addr(struct cache_t *cp,	/* cache instance to flush */
		 md_addr_t addr,	/* address of block to flush */
		 tick_t now)		/* time of cache flush */
{
  md_addr_t tag = CACHE_TAG(cp, addr);
  md_addr_t set = CACHE_SET(cp, addr);
  struct cache_blk_t *blk;
  int lat = cp->hit_latency; /* min latency to probe cache */

  if (cp->hsize)
    {
      /* higly-associativity cache, access through the per-set hash tables */
      int hindex = CACHE_HASH(cp, tag);

      for (blk=cp->sets[set].hash[hindex];
	   blk;
	   blk=blk->hash_next)
	{
	  if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	    break;
	}
    }
  else
    {
      /* low-associativity cache, linear search the way list */
      for (blk=cp->sets[set].way_head;
	   blk;
	   blk=blk->way_next)
	{
	  if (blk->tag == tag && (blk->status & CACHE_BLK_VALID))
	    break;
	}
    }

  if (blk)
    {
      cp->invalidations++;
      blk->status &= ~CACHE_BLK_VALID;

      /* blow away the last block to hit */
      cp->last_tagset = 0;
      cp->last_blk = NULL;

      if (blk->status & CACHE_BLK_DIRTY)
	{
	  /* write back the invalidated block */
          cp->writebacks++;
	  lat += cp->blk_access_fn(Write,
				   CACHE_MK_BADDR(cp, blk->tag, set),
				   cp->bsize, blk, now+lat);
	}
      /* move this block to tail of the way (LRU) list */
      update_way_list(&cp->sets[set], blk, Tail);
    }

  /* return latency of the operation */
  return lat;
}
