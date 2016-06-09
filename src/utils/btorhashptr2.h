/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOR_PTR2_HASH_H_INCLUDED
#define BTOR_PTR2_HASH_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include "utils/btorhash.h"
#include "utils/btormem.h"

struct BtorPtrHashTable2
{
  BtorMemMgr *mm;
  size_t count;
  size_t size;
  void **keys;
  uint8_t *hop_info; /* displacement information */
  BtorHashTableData *data;
  size_t *next;
  size_t *prev;

  size_t first;
  size_t last;

  BtorHashPtr hash;
  BtorCmpPtr cmp;
};

typedef struct BtorPtrHashTable2 BtorPtrHashTable2;

typedef void *(*BtorCloneKeyPtr2) (BtorMemMgr *mm,
                                   const void *map,
                                   const void *key);

/* Create new int32_t hash table. */
BtorPtrHashTable2 *btor_new_ptr_hash_table2 (BtorMemMgr *,
                                             BtorHashPtr,
                                             BtorCmpPtr);

/* Free int32_t hash table. */
void btor_delete_ptr_hash_table2 (BtorPtrHashTable2 *);

/* Returns the size of the BtorPtrHashTable2 in Byte. */
size_t btor_size_ptr_hash_table2 (BtorPtrHashTable2 *);

/* Add 'key' to the hash table and return the position at which 'key' is
 * stored in the keys array. */
size_t btor_add_ptr_hash_table2 (BtorPtrHashTable2 *, void *key);

/* Check whether 'key' is in the hash table. */
bool btor_contains_ptr_hash_table2 (BtorPtrHashTable2 *, void *key);

/* Remove 'key' from the hash table and return the position at which 'key'
 * was stored in the keys array. */
size_t btor_remove_ptr_hash_table2 (BtorPtrHashTable2 *, void *key);

/* Returns the position at which 'key' is stored in the keys array. It returns
 * 'size' of the hash table if 'key' could not be found. */
// TODO (ma): remove
size_t btor_get_pos_ptr_hash_table2 (BtorPtrHashTable2 *, void *key);

/* If 'ckey' is NULL the keys will be copied */
BtorPtrHashTable2 *btor_clone_ptr_hash_table2 (BtorMemMgr *mm,
                                               BtorPtrHashTable2 *table,
                                               BtorCloneKeyPtr2 ckey,
                                               const void *key_map);

/* map functions */

BtorPtrHashTable2 *btor_new_ptr_hash_map2 (BtorMemMgr *,
                                           BtorHashPtr,
                                           BtorCmpPtr);

bool btor_contains_ptr_hash_map2 (BtorPtrHashTable2 *, void *key);

void btor_remove_ptr_hash_map2 (BtorPtrHashTable2 *,
                                void *key,
                                BtorHashTableData *stored_data);

BtorHashTableData *btor_add_ptr_hash_map2 (BtorPtrHashTable2 *, void *key);
BtorHashTableData *btor_get_ptr_hash_map2 (BtorPtrHashTable2 *, void *key);

void btor_delete_ptr_hash_map2 (BtorPtrHashTable2 *);

size_t btor_size_ptr_hash_map2 (BtorPtrHashTable2 *);

/* If 'key' and/or 'cdata' is NULL the keys/data will be copied. */
BtorPtrHashTable2 *btor_clone_ptr_hash_map2 (BtorMemMgr *mm,
                                             BtorPtrHashTable2 *table,
                                             BtorCloneKeyPtr2 ckey,
                                             BtorCloneHashTableData cdata,
                                             const void *key_map,
                                             const void *data_map);

#endif