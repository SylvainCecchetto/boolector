/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORBVPROP_H_INCLUDED
#define BTORBVPROP_H_INCLUDED

#include "btorbv.h"

struct BtorBvDomain
{
  BtorBitVector *lo;
  BtorBitVector *hi;
};

typedef struct BtorBvDomain BtorBvDomain;

/* Create new bit-vector domain of width 'width' with low 0 and high ~0. */
BtorBvDomain *btor_bvprop_new_init (BtorMemMgr *mm, uint32_t width);

/* Create new bit-vector domain with low 'lo' and high 'hi'.
 * Creates copies of lo and hi. */
BtorBvDomain *btor_bvprop_new (BtorMemMgr *mm,
                               const BtorBitVector *lo,
                               const BtorBitVector *hi);

/* Delete bit-vector domain. */
void btor_bvprop_free (BtorMemMgr *mm, BtorBvDomain *d);

/* Check whether bit-vector domain is valid, i.e., ~lo | hi == ones. */
bool btor_bvprop_is_valid (BtorMemMgr *mm, const BtorBvDomain *d);

/* Check whether bit-vector domain is fixed, i.e., lo == hi */
bool btor_bvprop_is_fixed (BtorMemMgr *mm, const BtorBvDomain *d);

/* Propagate domains 'd_x', 'd_y', and 'd_z' of z = (x = y).  */
bool btor_bvprop_eq (BtorMemMgr *mm,
                     BtorBvDomain *d_x,
                     BtorBvDomain *d_y,
                     BtorBvDomain *d_z,
                     BtorBvDomain **res_d_x,
                     BtorBvDomain **res_d_y,
                     BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = ~x. */
bool btor_bvprop_not (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = x << n where n is const. */
bool btor_bvprop_sll_const (BtorMemMgr *mm,
                            BtorBvDomain *d_x,
                            BtorBvDomain *d_z,
                            BtorBitVector *n,
                            BtorBvDomain **res_d_x,
                            BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = x >> n where n is const. */
bool btor_bvprop_srl_const (BtorMemMgr *mm,
                            BtorBvDomain *d_x,
                            BtorBvDomain *d_z,
                            BtorBitVector *n,
                            BtorBvDomain **res_d_x,
                            BtorBvDomain **res_d_z);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x & y. */
bool btor_bvprop_and (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_y,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_y,
                      BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = x << y where y is not const.
 * Note: bw(y) = log_2 bw(y). */
bool btor_bvprop_sll (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_y,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_y,
                      BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = x >> y where y is not const.
 * Note: bw(y) = log_2 bw(y). */
bool btor_bvprop_srl (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_y,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_y,
                      BtorBvDomain **res_d_z);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x | y. */
bool btor_bvprop_or (BtorMemMgr *mm,
                     BtorBvDomain *d_x,
                     BtorBvDomain *d_y,
                     BtorBvDomain *d_z,
                     BtorBvDomain **res_d_x,
                     BtorBvDomain **res_d_y,
                     BtorBvDomain **res_d_z);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x | y. */
bool btor_bvprop_xor (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_y,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_y,
                      BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = x[upper:lower]. */
bool btor_bvprop_slice (BtorMemMgr *mm,
                        BtorBvDomain *d_x,
                        BtorBvDomain *d_z,
                        uint32_t upper,
                        uint32_t lower,
                        BtorBvDomain **res_d_x,
                        BtorBvDomain **res_d_z);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x o y. */
bool btor_bvprop_concat (BtorMemMgr *mm,
                         BtorBvDomain *d_x,
                         BtorBvDomain *d_y,
                         BtorBvDomain *d_z,
                         BtorBvDomain **res_d_y,
                         BtorBvDomain **res_d_x,
                         BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = sext(x, n). */
bool btor_bvprop_sext (BtorMemMgr *mm,
                       BtorBvDomain *d_x,
                       BtorBvDomain *d_z,
                       BtorBvDomain **res_d_x,
                       BtorBvDomain **res_d_z);

/* Propagate domains 'd_c', 'd_x', 'd_y' and 'd_z' of z = ite(c, x, y). */
bool btor_bvprop_ite (BtorMemMgr *mm,
                      BtorBvDomain *d_c,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_y,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_c,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_y,
                      BtorBvDomain **res_d_z);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x + y. */
bool btor_bvprop_add (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_y,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_y,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_z);

/**
 * Propagate domains 'd_x', 'd_y' and 'd_z' of z = x + y where + does not
 * overflow.
 */
bool btor_bvprop_add_aux (BtorMemMgr *mm,
                          BtorBvDomain *d_x,
                          BtorBvDomain *d_y,
                          BtorBvDomain *d_z,
                          BtorBvDomain **res_d_x,
                          BtorBvDomain **res_d_y,
                          BtorBvDomain **res_d_z,
                          bool no_overflows);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x * y. */
bool btor_bvprop_mul (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_y,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_y,
                      BtorBvDomain **res_d_z);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x * y where * does not
 * overflow. */
bool btor_bvprop_mul_aux (BtorMemMgr *mm,
                          BtorBvDomain *d_x,
                          BtorBvDomain *d_y,
                          BtorBvDomain *d_z,
                          BtorBvDomain **res_d_x,
                          BtorBvDomain **res_d_y,
                          BtorBvDomain **res_d_z,
                          bool no_overflows);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x < y (unsigned lt). */
bool btor_bvprop_ult (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_y,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_y,
                      BtorBvDomain **res_d_z);

// TODO:
// propagators:
//
// z = x udiv y
// z = x urem y
#endif
