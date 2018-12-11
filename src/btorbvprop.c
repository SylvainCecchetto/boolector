/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 *
 *  Bit-vector operator propagators based on [1] and [2].
 *
 *  [1] Wenxi Wang, Harald SøndergaardPeter J. Stuckey:
 *      A Bit-Vector Solver with Word-Level Propagation
 *  [2] L. Michel, P. Van Hentenryck:
 *      Constraint Satisfaction over Bit-Vectors
 */

#include "btorbvprop.h"

#include <stdio.h>
#include "utils/btorutil.h"

#if 1
static void
print_domain (BtorMemMgr *g_mm, BtorBvDomain *d, bool print_short)
{
  if (print_short)
  {
    char *lo   = btor_bv_to_char (g_mm, d->lo);
    char *hi   = btor_bv_to_char (g_mm, d->hi);
    size_t len = strlen (lo);
    for (size_t i = 0; i < len; i++)
    {
      if (lo[i] != hi[i])
      {
        if (lo[i] == '0' && hi[i] == '1')
        {
          lo[i] = 'x';
        }
        else
        {
          assert (lo[i] == '1' && hi[i] == '0');
          lo[i] = '?';
        }
      }
    }
    printf ("%s\n", lo);
    btor_mem_freestr (g_mm, hi);
    btor_mem_freestr (g_mm, lo);
  }
  else
  {
    char *s = btor_bv_to_char (g_mm, d->lo);
    printf ("lo: %s, ", s);
    btor_mem_freestr (g_mm, s);
    s = btor_bv_to_char (g_mm, d->hi);
    printf ("hi: %s\n", s);
    btor_mem_freestr (g_mm, s);
  }
}
#endif

BTOR_DECLARE_STACK (BtorBvDomainPtr, BtorBvDomain *);

static BtorBvDomain *
new_domain (BtorMemMgr *mm)
{
  BtorBvDomain *res;
  BTOR_CNEW (mm, res);
  return res;
}

static BtorBvDomain *
new_invalid_domain (BtorMemMgr *mm, uint32_t width)
{
  BtorBvDomain *res = new_domain (mm);
  res->lo           = btor_bv_ones (mm, width);
  res->hi           = btor_bv_zero (mm, width);
  return res;
}

BtorBvDomain *
btor_bvprop_new_init (BtorMemMgr *mm, uint32_t width)
{
  assert (mm);
  BtorBvDomain *res = new_domain (mm);
  res->lo           = btor_bv_zero (mm, width);
  res->hi           = btor_bv_ones (mm, width);
  return res;
}

BtorBvDomain *
btor_bvprop_new (BtorMemMgr *mm,
                 const BtorBitVector *lo,
                 const BtorBitVector *hi)
{
  assert (mm);
  assert (lo);
  assert (hi);
  assert (lo->width == hi->width);

  BtorBvDomain *res = new_domain (mm);
  res->lo           = btor_bv_copy (mm, lo);
  res->hi           = btor_bv_copy (mm, hi);
  return res;
}

void
btor_bvprop_free (BtorMemMgr *mm, BtorBvDomain *d)
{
  assert (mm);
  assert (d);

  if (d->lo) { btor_bv_free (mm, d->lo); }
  if (d->hi) { btor_bv_free (mm, d->hi); }
  BTOR_DELETE (mm, d);
}

bool
btor_bvprop_is_valid (BtorMemMgr *mm, const BtorBvDomain *d)
{
  BtorBitVector *not_lo       = btor_bv_not (mm, d->lo);
  BtorBitVector *not_lo_or_hi = btor_bv_or (mm, not_lo, d->hi);
  bool res                    = btor_bv_is_ones (not_lo_or_hi);
  btor_bv_free (mm, not_lo);
  btor_bv_free (mm, not_lo_or_hi);
  return res;
}

bool
btor_bvprop_is_fixed (BtorMemMgr *mm, const BtorBvDomain *d)
{
  BtorBitVector *equal = btor_bv_eq (mm, d->lo, d->hi);
  bool res             = btor_bv_is_true (equal);
  btor_bv_free (mm, equal);
  return res;
}

static bool
made_progress (BtorBvDomain *d_x,
               BtorBvDomain *d_y,
               BtorBvDomain *d_z,
               BtorBvDomain *d_c,
               BtorBvDomain *res_d_x,
               BtorBvDomain *res_d_y,
               BtorBvDomain *res_d_z,
               BtorBvDomain *res_d_c)
{
  assert (d_x);
  assert (d_z);
  assert (res_d_x);
  assert (res_d_z);
  assert (!d_y || res_d_y);

  if (btor_bv_compare (d_x->lo, res_d_x->lo)) return true;
  if (btor_bv_compare (d_x->hi, res_d_x->hi)) return true;
  if (d_y && btor_bv_compare (d_y->lo, res_d_y->lo)) return true;
  if (d_y && btor_bv_compare (d_y->hi, res_d_y->hi)) return true;
  if (btor_bv_compare (d_z->lo, res_d_z->lo)) return true;
  if (btor_bv_compare (d_z->hi, res_d_z->hi)) return true;
  if (d_c && btor_bv_compare (d_c->lo, res_d_c->lo)) return true;
  if (d_c && btor_bv_compare (d_c->hi, res_d_c->hi)) return true;
  return false;
}

bool
btor_bvprop_eq (BtorMemMgr *mm,
                BtorBvDomain *d_x,
                BtorBvDomain *d_y,
                BtorBvDomain *d_z,
                BtorBvDomain **res_d_x,
                BtorBvDomain **res_d_y,
                BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_y);
  assert (btor_bvprop_is_valid (mm, d_y));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (d_x->lo->width == d_y->lo->width);
  assert (d_x->hi->width == d_y->hi->width);
  assert (d_z->lo->width == 1);
  assert (d_z->hi->width == 1);

  bool valid = true;
  BtorBvDomain *tmp;
  BtorBitVector *sext_lo_z, *not_hi_y, *not_hi_x;
  BtorBitVector *lo_z_and_lo_y, *lo_z_and_hi_y, *not_and;
  sext_lo_z = btor_bv_sext (mm, d_z->lo, d_x->lo->width - 1);
  not_hi_y  = btor_bv_not (mm, d_y->hi);
  not_hi_x  = btor_bv_not (mm, d_x->hi);

  /* lo_x = lo_x | (sext(lo_z,n) & lo_y)
   * hi_x = hi_x & ~(sext(hi_z,n) & ~hi_y)
   */
  tmp           = new_domain (mm);
  lo_z_and_lo_y = btor_bv_and (mm, sext_lo_z, d_y->lo);
  tmp->lo       = btor_bv_or (mm, d_x->lo, lo_z_and_lo_y);

  lo_z_and_hi_y = btor_bv_and (mm, sext_lo_z, not_hi_y);
  not_and       = btor_bv_not (mm, lo_z_and_hi_y);
  tmp->hi       = btor_bv_and (mm, d_x->hi, not_and);

  btor_bv_free (mm, lo_z_and_lo_y);
  btor_bv_free (mm, lo_z_and_hi_y);
  btor_bv_free (mm, not_and);

  valid = valid & btor_bvprop_is_valid (mm, tmp);
  if (res_d_x)
  {
    *res_d_x = tmp;
  }
  else
  {
    btor_bvprop_free (mm, tmp);
  }

  /* lo_y = lo_y | (sext(lo_z,n) & lo_x)
   * hi_y = hi_y & ~(sext(hi_z,n) & ~hi_x)
   */
  if (valid)
  {
    BtorBitVector *lo_z_and_lo_x, *lo_z_and_hi_x;
    tmp           = new_domain (mm);
    lo_z_and_lo_x = btor_bv_and (mm, sext_lo_z, d_x->lo);
    tmp->lo       = btor_bv_or (mm, d_y->lo, lo_z_and_lo_x);

    lo_z_and_hi_x = btor_bv_and (mm, sext_lo_z, not_hi_x);
    not_and       = btor_bv_not (mm, lo_z_and_hi_x);
    tmp->hi       = btor_bv_and (mm, d_y->hi, not_and);

    btor_bv_free (mm, lo_z_and_lo_x);
    btor_bv_free (mm, lo_z_and_hi_x);
    btor_bv_free (mm, not_and);

    valid = valid & btor_bvprop_is_valid (mm, tmp);
  }
  else
  {
    tmp = btor_bvprop_new (mm, d_y->lo, d_y->hi);
  }
  if (res_d_y)
  {
    *res_d_y = tmp;
  }
  else
  {
    btor_bvprop_free (mm, tmp);
  }

  /* lo_z = lo_z | redand((lo_x & lo_y) | (~hi_x & ~hi_y))
   * hi_z = hi_z & ~redand((lo_x & ~hi_y) | (~hi_x & lo_y))
   */
  if (valid)
  {
    BtorBitVector *lo_x_and_lo_y, *hi_x_and_hi_y, * or, *redand;
    tmp           = new_domain (mm);
    lo_x_and_lo_y = btor_bv_and (mm, d_x->lo, d_y->lo);
    hi_x_and_hi_y = btor_bv_and (mm, not_hi_x, not_hi_y);
    or            = btor_bv_or (mm, lo_x_and_lo_y, hi_x_and_hi_y);
    redand        = btor_bv_redand (mm, or);
    tmp->lo       = btor_bv_or (mm, d_z->lo, redand);

    btor_bv_free (mm, lo_x_and_lo_y);
    btor_bv_free (mm, hi_x_and_hi_y);
    btor_bv_free (mm, or);
    btor_bv_free (mm, redand);

    BtorBitVector *lo_x_and_hi_y, *hi_x_and_lo_y, *not_redand;
    lo_x_and_hi_y = btor_bv_and (mm, d_x->lo, not_hi_y);
    hi_x_and_lo_y = btor_bv_and (mm, not_hi_x, d_y->lo);
    or            = btor_bv_or (mm, lo_x_and_hi_y, hi_x_and_lo_y);
    redand        = btor_bv_redand (mm, or);
    not_redand    = btor_bv_not (mm, redand);
    tmp->hi       = btor_bv_and (mm, d_z->hi, not_redand);

    btor_bv_free (mm, lo_x_and_hi_y);
    btor_bv_free (mm, hi_x_and_lo_y);
    btor_bv_free (mm, or);
    btor_bv_free (mm, redand);
    btor_bv_free (mm, not_redand);

    valid = valid & btor_bvprop_is_valid (mm, tmp);
  }
  else
  {
    tmp = btor_bvprop_new (mm, d_z->lo, d_z->hi);
  }
  if (res_d_z)
  {
    *res_d_z = tmp;
  }
  else
  {
    btor_bvprop_free (mm, tmp);
  }

  btor_bv_free (mm, sext_lo_z);
  btor_bv_free (mm, not_hi_x);
  btor_bv_free (mm, not_hi_y);

  return valid;
}

bool
btor_bvprop_not (BtorMemMgr *mm,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));

  /**
   * lo_x' = lo_x | ~hi_z
   * hi_x' = hi_x & ~hi_z
   */
  BtorBitVector *not_hi = btor_bv_not (mm, d_z->hi);
  BtorBitVector *not_lo = btor_bv_not (mm, d_z->lo);
  *res_d_x              = new_domain (mm);
  (*res_d_x)->lo        = btor_bv_or (mm, d_x->lo, not_hi);
  (*res_d_x)->hi        = btor_bv_and (mm, d_x->hi, not_lo);
  btor_bv_free (mm, not_hi);
  btor_bv_free (mm, not_lo);

  /**
   * lo_z' = lo_z | ~hi_x
   * hi_z' = hi_z & ~hi_x
   */
  not_hi         = btor_bv_not (mm, d_x->hi);
  not_lo         = btor_bv_not (mm, d_x->lo);
  *res_d_z       = new_domain (mm);
  (*res_d_z)->lo = btor_bv_or (mm, d_z->lo, not_hi);
  (*res_d_z)->hi = btor_bv_and (mm, d_z->hi, not_lo);
  btor_bv_free (mm, not_hi);
  btor_bv_free (mm, not_lo);

  return btor_bvprop_is_valid (mm, *res_d_x)
         && btor_bvprop_is_valid (mm, *res_d_z);
}

static bool
bvprop_shift_const_aux (BtorMemMgr *mm,
                        BtorBvDomain *d_x,
                        BtorBvDomain *d_z,
                        BtorBitVector *n,
                        BtorBvDomain **res_d_x,
                        BtorBvDomain **res_d_z,
                        bool is_srl)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (n);
  assert (res_d_x);
  assert (res_d_z);

  uint32_t w, wn;
  BtorBitVector *mask1, *ones_wn, *zero_wn, *ones_w_wn, *zero_w_wn;
  BtorBitVector *tmp0, *tmp1;

  w = d_z->hi->width;
  assert (w == d_z->lo->width);
  assert (w == d_x->hi->width);
  assert (w == d_x->lo->width);
#ifndef NDEBUG
  BtorBitVector *uint32maxbv = btor_bv_ones (mm, 32);
  assert (btor_bv_compare (n, uint32maxbv) <= 0);
  btor_bv_free (mm, uint32maxbv);
#endif
  wn = (uint32_t) btor_bv_to_uint64 (n);

  /**
   * SLL: mask1 = 1_[wn]   :: 0_[w-wn]
   * SRL: mask1 = 0_[w-wn] :: 1_[wn]
   */
  if (wn == 0)
  {
    mask1 = btor_bv_zero (mm, w);
  }
  else if (w == wn)
  {
    mask1 = btor_bv_ones (mm, w);
  }
  else
  {
    zero_wn   = btor_bv_zero (mm, wn);
    zero_w_wn = btor_bv_zero (mm, w - wn);
    ones_wn   = btor_bv_ones (mm, wn);
    ones_w_wn = btor_bv_ones (mm, w - wn);

    mask1 = is_srl ? btor_bv_concat (mm, zero_w_wn, ones_wn)
                   : btor_bv_concat (mm, ones_wn, zero_w_wn);
    btor_bv_free (mm, zero_wn);
    btor_bv_free (mm, zero_w_wn);
    btor_bv_free (mm, ones_wn);
    btor_bv_free (mm, ones_w_wn);
  }

  *res_d_x = new_domain (mm);
  *res_d_z = new_domain (mm);

  /**
   * SLL: lo_x' = lo_x | (lo_z >> n)
   * SRL: lo_x' = lo_x | (lo_z << n)
   */
  tmp0 = is_srl ? btor_bv_sll (mm, d_z->lo, n) : btor_bv_srl (mm, d_z->lo, n);
  (*res_d_x)->lo = btor_bv_or (mm, d_x->lo, tmp0);
  btor_bv_free (mm, tmp0);

  /**
   * SLL: hi_x' = ((hi_z >> n) | mask1) & hi_x
   * SRL: hi_x' = ((hi_z << n) | mask1) & hi_x
   */
  tmp0 = is_srl ? btor_bv_sll (mm, d_z->hi, n) : btor_bv_srl (mm, d_z->hi, n);
  tmp1 = btor_bv_or (mm, tmp0, mask1);
  (*res_d_x)->hi = btor_bv_and (mm, tmp1, d_x->hi);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /**
   * SLL: lo_z' = ((low_x << n) | lo_z)
   * SRL: lo_z' = ((low_x >> n) | lo_z)
   *
   * Note: Propagator in [1] is incorrect!
   * (was:
   *   SLL: lo_z' = ((low_x << n) | lo_z) & mask2
   *   SRL: lo_z' = ((low_x >> n) | lo_z) & mask2
   *  with:
   *   SLL: mask2 = 1_[w-wn] :: 0_[wn]
   *   SRL: mask2 = 0_[wn]   :: 1_[w-wn]
   *  )
   */
  tmp0 = is_srl ? btor_bv_srl (mm, d_x->lo, n) : btor_bv_sll (mm, d_x->lo, n);
  (*res_d_z)->lo = btor_bv_or (mm, tmp0, d_z->lo);
  btor_bv_free (mm, tmp0);

  /**
   * SLL: hi_z' = (hi_x << n) & hi_z
   * SRL: hi_z' = (hi_x >> n) & hi_z
   */
  tmp0 = is_srl ? btor_bv_srl (mm, d_x->hi, n) : btor_bv_sll (mm, d_x->hi, n);
  (*res_d_z)->hi = btor_bv_and (mm, tmp0, d_z->hi);
  btor_bv_free (mm, tmp0);

  btor_bv_free (mm, mask1);

  return btor_bvprop_is_valid (mm, *res_d_x)
         && btor_bvprop_is_valid (mm, *res_d_z);
}

bool
btor_bvprop_sll_const (BtorMemMgr *mm,
                       BtorBvDomain *d_x,
                       BtorBvDomain *d_z,
                       BtorBitVector *n,
                       BtorBvDomain **res_d_x,
                       BtorBvDomain **res_d_z)
{
  return bvprop_shift_const_aux (mm, d_x, d_z, n, res_d_x, res_d_z, false);
}

bool
btor_bvprop_srl_const (BtorMemMgr *mm,
                       BtorBvDomain *d_x,
                       BtorBvDomain *d_z,
                       BtorBitVector *n,
                       BtorBvDomain **res_d_x,
                       BtorBvDomain **res_d_z)
{
  return bvprop_shift_const_aux (mm, d_x, d_z, n, res_d_x, res_d_z, true);
}

bool
bvprop_shift_aux (BtorMemMgr *mm,
                  BtorBvDomain *d_x,
                  BtorBvDomain *d_y,
                  BtorBvDomain *d_z,
                  BtorBvDomain **res_d_x,
                  BtorBvDomain **res_d_y,
                  BtorBvDomain **res_d_z,
                  bool is_srl)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_y);
  assert (btor_util_is_power_of_2 (d_y->lo->width));
  assert (btor_util_log_2 (d_x->lo->width) == d_y->lo->width);
  assert (btor_bvprop_is_valid (mm, d_y));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (res_d_x);
  assert (res_d_y);
  assert (res_d_z);

  /* z_[bw] = x_[bw] << y_[log_2 bw]
   *
   * SLL:
   *   prev_z = x
   *   for i = 0 to log2_bw - 1:
   *     shift = 1 << i
   *     cur_z = ite (y[i:i], prev_z << shift, prev_z)
   *     prev_z = cur_z
   *
   * SRL:
   *   prev_z = x
   *   for i = 0 to log2_bw - 1:
   *     shift = 1 << i
   *     cur_z = ite (y[i:i], prev_z >> shift, prev_z)
   *     prev_z = cur_z
   */

  uint32_t i, n, bw, log2_bw;
  bool res, progress;
  BtorBitVector *bv;
  BtorBvDomain *d, *tmp_x, *tmp_y, *tmp_z;
  BtorBvDomainPtrStack d_c_stack, d_shift_stack, d_ite_stack;
  BtorBvDomain **tmp_c, **tmp_shift, **tmp_ite, **tmp_z_prev;
  BtorBvDomain *tmp_res_c;
  BtorBitVectorPtrStack shift_stack;

  res = true;

  bw = d_x->lo->width;
  assert (bw == d_x->hi->width);
  assert (bw == d_z->lo->width);
  assert (bw == d_z->hi->width);
  log2_bw = btor_util_log_2 (bw);
  assert (log2_bw == d_y->hi->width);
  assert (log2_bw == d_y->lo->width);

  BTOR_INIT_STACK (mm, d_c_stack);
  BTOR_INIT_STACK (mm, d_shift_stack);
  BTOR_INIT_STACK (mm, d_ite_stack);
  BTOR_INIT_STACK (mm, shift_stack);

  for (i = 0; i < log2_bw; i++)
  {
    /* slice y into log_2(bw) ite conditions */
    d     = new_domain (mm);
    d->lo = btor_bv_slice (mm, d_y->lo, i, i);
    d->hi = btor_bv_slice (mm, d_y->hi, i, i);
    BTOR_PUSH_STACK (d_c_stack, d);
    /* log_2(bw) shift propagators */
    d = btor_bvprop_new_init (mm, bw);
    BTOR_PUSH_STACK (d_shift_stack, d);
    /* log_2(bw) ite propagators */
    if (i == log2_bw - 1)
      d = btor_bvprop_new (mm, d_z->lo, d_z->hi);
    else
      d = btor_bvprop_new_init (mm, bw);
    BTOR_PUSH_STACK (d_ite_stack, d);
    /* shift width */
    bv = btor_bv_uint64_to_bv (mm, 1 << i, log2_bw);
    BTOR_PUSH_STACK (shift_stack, bv);
  }

  assert (BTOR_COUNT_STACK (d_c_stack) == log2_bw);
  assert (BTOR_COUNT_STACK (d_shift_stack) == log2_bw);
  assert (BTOR_COUNT_STACK (d_ite_stack) == log2_bw);
  assert (BTOR_COUNT_STACK (shift_stack) == log2_bw);

  tmp_x = btor_bvprop_new (mm, d_x->lo, d_x->hi);
  tmp_y = btor_bvprop_new (mm, d_y->lo, d_y->hi);
  tmp_z = btor_bvprop_new (mm, d_z->lo, d_z->hi);

  do
  {
    progress = false;

    for (i = 0; i < log2_bw; i++)
    {
      /**
       * SLL:
       *   prev_z = x
       *   for i = 0 to log2_bw - 1:
       *     cur_z = ite (y[i:i], prev_z << shift, prev_z)
       *     prev_z = cur_z
       *
       * SRL:
       *   prev_z = x
       *   for i = 0 to log2_bw - 1:
       *     cur_z = ite (y[i:i], prev_z << shift, prev_z)
       *     prev_z = cur_z
       */

      /* shift = 1 << i */
      bv = BTOR_PEEK_STACK (shift_stack, i);

      tmp_shift  = &d_shift_stack.start[i];
      tmp_z_prev = i ? &d_ite_stack.start[i - 1] : &tmp_x;
      /**
       * SLL: prev_z << shift
       * SRL: prev_z >> shift
       */
      if (is_srl)
      {
        if (!btor_bvprop_srl_const (
                mm, *tmp_z_prev, *tmp_shift, bv, res_d_x, res_d_z))
        {
          res = false;
          btor_bvprop_free (mm, *res_d_x);
          btor_bvprop_free (mm, *res_d_z);
          goto DONE;
        }
      }
      else
      {
        if (!btor_bvprop_sll_const (
                mm, *tmp_z_prev, *tmp_shift, bv, res_d_x, res_d_z))
        {
          res = false;
          btor_bvprop_free (mm, *res_d_x);
          btor_bvprop_free (mm, *res_d_z);
          goto DONE;
        }
      }
      assert (btor_bvprop_is_valid (mm, *res_d_x));
      assert (btor_bvprop_is_valid (mm, *res_d_z));
      if (!progress)
      {
        progress = made_progress (
            *tmp_z_prev, 0, *tmp_shift, 0, *res_d_x, 0, *res_d_z, 0);
      }
      btor_bvprop_free (mm, *tmp_z_prev);
      btor_bvprop_free (mm, *tmp_shift);
      *tmp_z_prev = *res_d_x;
      *tmp_shift  = *res_d_z;

      /**
       * SLL: ite (y[i:i], z << (1 << i), x)
       * SRL: ite (y[i:i], z >> (1 << i), x)
       */
      tmp_c   = &d_c_stack.start[i];
      tmp_ite = &d_ite_stack.start[i];
      if (!btor_bvprop_ite (mm,
                            *tmp_c,
                            *tmp_shift,
                            *tmp_z_prev,
                            *tmp_ite,
                            &tmp_res_c,
                            res_d_x,
                            res_d_y,
                            res_d_z))
      {
        res = false;
        btor_bvprop_free (mm, tmp_res_c);
        btor_bvprop_free (mm, *res_d_x);
        btor_bvprop_free (mm, *res_d_y);
        btor_bvprop_free (mm, *res_d_z);
        goto DONE;
      }
      assert (btor_bvprop_is_valid (mm, *res_d_x));
      assert (btor_bvprop_is_valid (mm, *res_d_y));
      assert (btor_bvprop_is_valid (mm, *res_d_z));
      assert (btor_bvprop_is_valid (mm, tmp_res_c));
      if (!progress)
      {
        progress = made_progress (*tmp_shift,
                                  *tmp_z_prev,
                                  *tmp_ite,
                                  *tmp_c,
                                  *res_d_x,
                                  *res_d_y,
                                  *res_d_z,
                                  tmp_res_c);
      }
      btor_bvprop_free (mm, *tmp_shift);
      btor_bvprop_free (mm, *tmp_z_prev);
      btor_bvprop_free (mm, *tmp_c);
      btor_bvprop_free (mm, *tmp_ite);
      *tmp_shift  = *res_d_x;
      *tmp_z_prev = *res_d_y;
      *tmp_ite    = *res_d_z;
      *tmp_c      = tmp_res_c;
    }
  } while (progress);

  /* Collect y bits into the result for d_y. */
  for (i = 0; i < log2_bw; i++)
  {
    d = BTOR_PEEK_STACK (d_c_stack, i);
    assert (d->lo->width == 1);
    assert (d->hi->width == 1);
    btor_bv_set_bit (tmp_y->lo, i, btor_bv_get_bit (d->lo, 0));
    btor_bv_set_bit (tmp_y->hi, i, btor_bv_get_bit (d->hi, 0));
  }

  /* Result for d_z. */
  btor_bvprop_free (mm, tmp_z);
  tmp_z     = new_domain (mm);
  tmp_z->lo = btor_bv_copy (mm, d_ite_stack.start[log2_bw - 1]->lo);
  tmp_z->hi = btor_bv_copy (mm, d_ite_stack.start[log2_bw - 1]->hi);
  assert (btor_bvprop_is_valid (mm, tmp_x));
  assert (btor_bvprop_is_valid (mm, tmp_y));
  assert (btor_bvprop_is_valid (mm, tmp_z));
DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  for (i = 0, n = BTOR_COUNT_STACK (d_c_stack); i < n; i++)
  {
    assert (!BTOR_EMPTY_STACK (d_c_stack));
    assert (!BTOR_EMPTY_STACK (d_shift_stack));
    assert (!BTOR_EMPTY_STACK (d_ite_stack));
    assert (!BTOR_EMPTY_STACK (shift_stack));
    btor_bvprop_free (mm, BTOR_POP_STACK (d_c_stack));
    btor_bvprop_free (mm, BTOR_POP_STACK (d_shift_stack));
    btor_bvprop_free (mm, BTOR_POP_STACK (d_ite_stack));
    btor_bv_free (mm, BTOR_POP_STACK (shift_stack));
  }
  BTOR_RELEASE_STACK (d_c_stack);
  BTOR_RELEASE_STACK (d_shift_stack);
  BTOR_RELEASE_STACK (d_ite_stack);
  BTOR_RELEASE_STACK (shift_stack);

  return res;
}

bool
btor_bvprop_sll (BtorMemMgr *mm,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_y,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_y,
                 BtorBvDomain **res_d_z)
{
  return bvprop_shift_aux (mm, d_x, d_y, d_z, res_d_x, res_d_y, res_d_z, false);
}

bool
btor_bvprop_srl (BtorMemMgr *mm,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_y,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_y,
                 BtorBvDomain **res_d_z)
{
  return bvprop_shift_aux (mm, d_x, d_y, d_z, res_d_x, res_d_y, res_d_z, true);
}

bool
btor_bvprop_and (BtorMemMgr *mm,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_y,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_y,
                 BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_y);
  assert (btor_bvprop_is_valid (mm, d_y));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (res_d_x);
  assert (res_d_y);
  assert (res_d_z);

  BtorBitVector *tmp0, *tmp1;

  *res_d_x = new_domain (mm);
  *res_d_y = new_domain (mm);
  *res_d_z = new_domain (mm);

  /* lo_x' = lo_x | lo_z */
  (*res_d_x)->lo = btor_bv_or (mm, d_x->lo, d_z->lo);

  /* hi_x' = hi_x & ~(~hi_z & lo_y) */
  tmp0 = btor_bv_not (mm, d_z->hi);
  tmp1 = btor_bv_and (mm, tmp0, d_y->lo);
  btor_bv_free (mm, tmp0);
  tmp0 = btor_bv_not (mm, tmp1);
  btor_bv_free (mm, tmp1);
  (*res_d_x)->hi = btor_bv_and (mm, d_x->hi, tmp0);
  btor_bv_free (mm, tmp0);

  /* lo_y' = lo_y | lo_z */
  (*res_d_y)->lo = btor_bv_or (mm, d_y->lo, d_z->lo);

  /* hi_y' = hi_y | ~(~hi_z & lo_x) */
  tmp0 = btor_bv_not (mm, d_z->hi);
  tmp1 = btor_bv_and (mm, tmp0, d_x->lo);
  btor_bv_free (mm, tmp0);
  tmp0 = btor_bv_not (mm, tmp1);
  btor_bv_free (mm, tmp1);
  (*res_d_y)->hi = btor_bv_and (mm, d_y->hi, tmp0);
  btor_bv_free (mm, tmp0);

  /* lo_z' = lo_z | (lo_x & lo_y) */
  tmp0           = btor_bv_and (mm, d_x->lo, d_y->lo);
  (*res_d_z)->lo = btor_bv_or (mm, d_z->lo, tmp0);
  btor_bv_free (mm, tmp0);

  /* hi_z' = hi_z & hi_x & hi_y */
  tmp0           = btor_bv_and (mm, d_x->hi, d_y->hi);
  (*res_d_z)->hi = btor_bv_and (mm, d_z->hi, tmp0);
  btor_bv_free (mm, tmp0);

  return btor_bvprop_is_valid (mm, *res_d_x)
         && btor_bvprop_is_valid (mm, *res_d_y)
         && btor_bvprop_is_valid (mm, *res_d_z);
}

bool
btor_bvprop_or (BtorMemMgr *mm,
                BtorBvDomain *d_x,
                BtorBvDomain *d_y,
                BtorBvDomain *d_z,
                BtorBvDomain **res_d_x,
                BtorBvDomain **res_d_y,
                BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_y);
  assert (btor_bvprop_is_valid (mm, d_y));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (res_d_x);
  assert (res_d_y);
  assert (res_d_z);

  BtorBitVector *tmp0, *tmp1;

  *res_d_x = new_domain (mm);
  *res_d_y = new_domain (mm);
  *res_d_z = new_domain (mm);

  /* lo_x' = lo_x | (~hi_y & lo_z) */
  tmp0           = btor_bv_not (mm, d_y->hi);
  tmp1           = btor_bv_and (mm, tmp0, d_z->lo);
  (*res_d_x)->lo = btor_bv_or (mm, d_x->lo, tmp1);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_x' = hi_x & hi_z */
  (*res_d_x)->hi = btor_bv_and (mm, d_x->hi, d_z->hi);

  /* lo_y' = lo_y | (~hi_x & lo_z) */
  tmp0           = btor_bv_not (mm, d_x->hi);
  tmp1           = btor_bv_and (mm, tmp0, d_z->lo);
  (*res_d_y)->lo = btor_bv_or (mm, d_y->lo, tmp1);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_y' = hi_y & hi_z */
  (*res_d_y)->hi = btor_bv_and (mm, d_y->hi, d_z->hi);

  /* lo_z' = lo_z | lo_x | lo_y */
  tmp0           = btor_bv_or (mm, d_z->lo, d_x->lo);
  (*res_d_z)->lo = btor_bv_or (mm, tmp0, d_y->lo);
  btor_bv_free (mm, tmp0);

  /* hi_z' = hi_z & (hi_x | hi_y) */
  tmp0           = btor_bv_or (mm, d_x->hi, d_y->hi);
  (*res_d_z)->hi = btor_bv_and (mm, d_z->hi, tmp0);
  btor_bv_free (mm, tmp0);

  return btor_bvprop_is_valid (mm, *res_d_x)
         && btor_bvprop_is_valid (mm, *res_d_y)
         && btor_bvprop_is_valid (mm, *res_d_z);
}

bool
btor_bvprop_xor (BtorMemMgr *mm,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_y,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_y,
                 BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_y);
  assert (btor_bvprop_is_valid (mm, d_y));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (res_d_x);
  assert (res_d_y);
  assert (res_d_z);

  BtorBitVector *tmp0, *tmp1, *tmp2;
  BtorBitVector *not_hi_z, *not_hi_y, *not_hi_x;

  *res_d_x = new_domain (mm);
  *res_d_y = new_domain (mm);
  *res_d_z = new_domain (mm);

  not_hi_z = btor_bv_not (mm, d_z->hi);
  not_hi_y = btor_bv_not (mm, d_y->hi);
  not_hi_x = btor_bv_not (mm, d_x->hi);

  /* lo_x' = lo_x | (~hi_z & lo_y) | (lo_z & ~hi_y) */
  tmp0 = btor_bv_and (mm, not_hi_z, d_y->lo);
  tmp1 = btor_bv_or (mm, d_x->lo, tmp0);
  btor_bv_free (mm, tmp0);
  tmp0           = btor_bv_and (mm, not_hi_y, d_z->lo);
  (*res_d_x)->lo = btor_bv_or (mm, tmp0, tmp1);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_x' = hi_x & (hi_z | hi_y) & (~(lo_y & lo_z)) */
  tmp0 = btor_bv_or (mm, d_z->hi, d_y->hi);
  tmp1 = btor_bv_and (mm, d_x->hi, tmp0);
  btor_bv_free (mm, tmp0);
  tmp0           = btor_bv_and (mm, d_y->lo, d_z->lo);
  tmp2           = btor_bv_not (mm, tmp0);
  (*res_d_x)->hi = btor_bv_and (mm, tmp1, tmp2);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);
  btor_bv_free (mm, tmp2);

  /* lo_y' = lo_y | (~hi_z & lo_x) | (lo_z & ~hi_x) */
  tmp0 = btor_bv_and (mm, not_hi_z, d_x->lo);
  tmp1 = btor_bv_or (mm, tmp0, d_y->lo);
  btor_bv_free (mm, tmp0);
  tmp0           = btor_bv_and (mm, d_z->lo, not_hi_x);
  (*res_d_y)->lo = btor_bv_or (mm, tmp0, tmp1);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_y' = hi_y & (hi_z | hi_x) & (~(lo_x & lo_z)) */
  tmp0 = btor_bv_or (mm, d_z->hi, d_x->hi);
  tmp1 = btor_bv_and (mm, d_y->hi, tmp0);
  btor_bv_free (mm, tmp0);
  tmp0           = btor_bv_and (mm, d_x->lo, d_z->lo);
  tmp2           = btor_bv_not (mm, tmp0);
  (*res_d_y)->hi = btor_bv_and (mm, tmp1, tmp2);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);
  btor_bv_free (mm, tmp2);

  /* lo_z' = lo_z | (~hi_x & lo_y) | (lo_x & ~hi_y) */
  tmp0 = btor_bv_and (mm, not_hi_x, d_y->lo);
  tmp1 = btor_bv_or (mm, d_z->lo, tmp0);
  btor_bv_free (mm, tmp0);
  tmp0           = btor_bv_and (mm, d_x->lo, not_hi_y);
  (*res_d_z)->lo = btor_bv_or (mm, tmp0, tmp1);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_z' = hi_z & (hi_x | hi_y) & (~(lo_x & lo_y)) */
  tmp0 = btor_bv_or (mm, d_x->hi, d_y->hi);
  tmp1 = btor_bv_and (mm, d_z->hi, tmp0);
  btor_bv_free (mm, tmp0);
  tmp0           = btor_bv_and (mm, d_x->lo, d_y->lo);
  tmp2           = btor_bv_not (mm, tmp0);
  (*res_d_z)->hi = btor_bv_and (mm, tmp1, tmp2);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);
  btor_bv_free (mm, tmp2);
  btor_bv_free (mm, not_hi_x);
  btor_bv_free (mm, not_hi_y);
  btor_bv_free (mm, not_hi_z);
  return btor_bvprop_is_valid (mm, *res_d_x)
         && btor_bvprop_is_valid (mm, *res_d_y)
         && btor_bvprop_is_valid (mm, *res_d_z);
}

bool
btor_bvprop_slice (BtorMemMgr *mm,
                   BtorBvDomain *d_x,
                   BtorBvDomain *d_z,
                   uint32_t upper,
                   uint32_t lower,
                   BtorBvDomain **res_d_x,
                   BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (upper >= lower);
  assert (upper < d_x->lo->width);
  assert (upper - lower + 1 == d_z->lo->width);

  /* Apply equality propagator on sliced 'x' domain.
   *
   * lo_x' = lo_x[wx-1:upper+1] o lo_x[upper:lower] | lo_z o lo_x[lower - 1:0]
   * hi_x' = hi_x[wx-1:upper+1] o hi_x[upper:lower] & hi_z o hi_x[lower - 1:0]
   *
   * Note: We don't use the propagator described in [1] since it changes the
   *       don't care bits of 'd_x'.
   */

  BtorBvDomain *sliced_x = new_domain (mm);
  sliced_x->lo           = btor_bv_slice (mm, d_x->lo, upper, lower);
  sliced_x->hi           = btor_bv_slice (mm, d_x->hi, upper, lower);

  BtorBitVector *one = btor_bv_one (mm, 1);
  BtorBvDomain *d_eq = btor_bvprop_new (mm, one, one);
  btor_bv_free (mm, one);

  bool valid =  btor_bvprop_eq (mm, sliced_x, d_z, d_eq, res_d_z, 0, 0);
  btor_bvprop_free (mm, d_eq);
  btor_bvprop_free (mm, sliced_x);

  if (!valid)
  {
    *res_d_x = new_invalid_domain (mm, d_x->lo->width);
    return false;
  }

  uint32_t wx = d_x->lo->width;

  *res_d_x = new_domain (mm);

  BtorBitVector *lo_x = btor_bv_copy (mm, (*res_d_z)->lo);
  BtorBitVector *hi_x = btor_bv_copy (mm, (*res_d_z)->hi);
  BtorBitVector *tmp;
  if (lower > 0)
  {
    BtorBitVector *lower_lo_x = btor_bv_slice (mm, d_x->lo, lower - 1, 0);
    BtorBitVector *lower_hi_x = btor_bv_slice (mm, d_x->hi, lower - 1, 0);
    tmp                       = btor_bv_concat (mm, lo_x, lower_lo_x);
    btor_bv_free (mm, lo_x);
    lo_x = tmp;
    tmp  = btor_bv_concat (mm, hi_x, lower_hi_x);
    btor_bv_free (mm, hi_x);
    hi_x = tmp;
    btor_bv_free (mm, lower_lo_x);
    btor_bv_free (mm, lower_hi_x);
  }

  if (upper < wx - 1)
  {
    BtorBitVector *upper_lo_x = btor_bv_slice (mm, d_x->lo, wx - 1, upper + 1);
    BtorBitVector *upper_hi_x = btor_bv_slice (mm, d_x->hi, wx - 1, upper + 1);
    tmp                       = btor_bv_concat (mm, upper_lo_x, lo_x);
    btor_bv_free (mm, lo_x);
    lo_x = tmp;
    tmp  = btor_bv_concat (mm, upper_hi_x, hi_x);
    btor_bv_free (mm, hi_x);
    hi_x = tmp;
    btor_bv_free (mm, upper_lo_x);
    btor_bv_free (mm, upper_hi_x);
  }

  assert (lo_x->width == wx);
  assert (hi_x->width == wx);
  (*res_d_x)->lo = lo_x;
  (*res_d_x)->hi = hi_x;
  return btor_bvprop_is_valid (mm, *res_d_x)
         && btor_bvprop_is_valid (mm, *res_d_z);
}

bool
btor_bvprop_concat (BtorMemMgr *mm,
                    BtorBvDomain *d_x,
                    BtorBvDomain *d_y,
                    BtorBvDomain *d_z,
                    BtorBvDomain **res_d_x,
                    BtorBvDomain **res_d_y,
                    BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_y);
  assert (btor_bvprop_is_valid (mm, d_y));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (res_d_x);
  assert (res_d_y);
  assert (res_d_z);

  bool res;
  uint32_t wy, wz;

  wy = d_y->hi->width;
  assert (wy == d_y->lo->width);
  wz = d_z->hi->width;
  assert (wz == d_z->lo->width);

#if 0
  /* These are the propagators as proposed in [1]. */

  uint32_t wx;
  BtorBitVector *mask, *zero, *ones, *tmp0, *tmp1;
  BtorBitVector *lo_x, *hi_x, *lo_y, *hi_y;

  wx = d_x->hi->width;
  assert (wx == d_x->lo->width);

  lo_x = btor_bv_uext (mm, d_x->lo, wz - wx);
  hi_x = btor_bv_uext (mm, d_x->hi, wz - wx);
  lo_y = btor_bv_uext (mm, d_y->lo, wz - wy);
  hi_y = btor_bv_uext (mm, d_y->hi, wz - wy);

  zero = btor_bv_zero (mm, wz - wy);
  ones = btor_bv_ones (mm, wy);
  mask = btor_bv_concat (mm, zero, ones);

  *res_d_x = new_domain (mm);
  *res_d_y = new_domain (mm);
  *res_d_z = new_domain (mm);

  /* lo_z' = lo_z | ((lo_x << wy) | lo_y) */
  tmp0           = btor_bv_sll_uint32 (mm, lo_x, wy);
  tmp1           = btor_bv_or (mm, tmp0, lo_y);
  (*res_d_z)->lo = btor_bv_or (mm, d_z->lo, tmp1);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_z' = hi_z & ((hi_x << wy) | hi_y) */
  tmp0           = btor_bv_sll_uint32 (mm, hi_x, wy);
  tmp1           = btor_bv_or (mm, tmp0, hi_y);
  (*res_d_z)->hi = btor_bv_and (mm, d_z->hi, tmp1);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* lo_x' = lo_x | (lo_z >> wy) */
  tmp0           = btor_bv_srl_uint32 (mm, d_z->lo, wy);
  tmp1           = btor_bv_or (mm, lo_x, tmp0);
  (*res_d_x)->lo = btor_bv_slice (mm, tmp1, wx - 1, 0);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_x' = hi_x & (hi_z >> wy) */
  tmp0           = btor_bv_srl_uint32 (mm, d_z->hi, wy);
  tmp1           = btor_bv_and (mm, hi_x, tmp0);
  (*res_d_x)->hi = btor_bv_slice (mm, tmp1, wx - 1, 0);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* lo_y' = lo_y | (lo_z & mask */
  tmp0           = btor_bv_and (mm, d_z->lo, mask);
  tmp1           = btor_bv_or (mm, lo_y, tmp0);
  (*res_d_y)->lo = btor_bv_slice (mm, tmp1, wy - 1, 0);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_y' = hi_y & (hi_z & mask) */
  tmp0           = btor_bv_and (mm, d_z->hi, mask);
  tmp1           = btor_bv_and (mm, hi_y, tmp0);
  (*res_d_y)->hi = btor_bv_slice (mm, tmp1, wy - 1, 0);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  btor_bv_free (mm, lo_x);
  btor_bv_free (mm, hi_x);
  btor_bv_free (mm, lo_y);
  btor_bv_free (mm, hi_y);

  btor_bv_free (mm, zero);
  btor_bv_free (mm, ones);
  btor_bv_free (mm, mask);
  res = btor_bvprop_is_valid (mm, *res_d_x)
        && btor_bvprop_is_valid (mm, *res_d_y)
        && btor_bvprop_is_valid (mm, *res_d_z);
#else
  /* These propagators are decompositional (simpler). */

  BtorBitVector *lo_zx, *lo_zy, *hi_zx, *hi_zy;
  BtorBvDomain *d_zx, *d_zy;

  /* z = zx o zy */
  lo_zx = btor_bv_slice (mm, d_z->lo, wz - 1, wy);
  hi_zx = btor_bv_slice (mm, d_z->hi, wz - 1, wy);
  lo_zy = btor_bv_slice (mm, d_z->lo, wy - 1, 0);
  hi_zy = btor_bv_slice (mm, d_z->hi, wy - 1, 0);
  d_zx  = btor_bvprop_new (mm, lo_zx, hi_zx);
  d_zy  = btor_bvprop_new (mm, lo_zy, hi_zy);

  *res_d_z = new_domain (mm);

  BtorBitVector *one = btor_bv_one (mm, 1);
  BtorBvDomain *d_eq = btor_bvprop_new (mm, one, one);
  btor_bv_free (mm, one);

  /* res_z = prop(d_zx = d_x) o prop(d_zy o d_y) */
  if (!btor_bvprop_eq (mm, d_zx, d_x, d_eq, res_d_x, 0, 0))
  {
    res = false;
    goto DONE;
  }
  if (!btor_bvprop_eq (mm, d_zy, d_y, d_eq, res_d_y, 0, 0))
  {
    res = false;
    goto DONE;
  }

  (*res_d_z)->lo = btor_bv_concat (mm, (*res_d_x)->lo, (*res_d_y)->lo);
  (*res_d_z)->hi = btor_bv_concat (mm, (*res_d_x)->hi, (*res_d_y)->hi);

  res = btor_bvprop_is_valid (mm, *res_d_x)
        && btor_bvprop_is_valid (mm, *res_d_y)
        && btor_bvprop_is_valid (mm, *res_d_z);
DONE:
  btor_bv_free (mm, lo_zx);
  btor_bv_free (mm, lo_zy);
  btor_bv_free (mm, hi_zx);
  btor_bv_free (mm, hi_zy);
  btor_bvprop_free (mm, d_zx);
  btor_bvprop_free (mm, d_zy);
  btor_bvprop_free (mm, d_eq);
#endif
  return res;
}

bool
btor_bvprop_sext (BtorMemMgr *mm,
                  BtorBvDomain *d_x,
                  BtorBvDomain *d_z,
                  BtorBvDomain **res_d_x,
                  BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (res_d_x);
  assert (res_d_z);

  uint32_t wx, wn, wz, lo_x_lsb, hi_x_lsb;
  BtorBitVector *tmp0, *tmp1, *tmp2;
  BtorBitVector *slice_lo_z_hi, *slice_hi_z_hi;
  BtorBitVector *redor, *redand, *x_or_z, *x_and_z;

  *res_d_x = new_domain (mm);
  *res_d_z = new_domain (mm);

  wx = d_x->hi->width;
  assert (wx == d_x->lo->width);
  wz = d_z->hi->width;
  assert (wz == d_z->lo->width);
  wn = wz - wx;
  assert (wn);

  lo_x_lsb = btor_bv_get_bit (d_x->lo, wx - 1);
  hi_x_lsb = btor_bv_get_bit (d_x->hi, wx - 1);

  /* Note: The propagators for x and z from [1] are incorrect!
   * E.g. for x = 1 and z = 001 we expect an invalid result, but these
   * propagators produce x' = 1 and z' = 111. */

  if (wx > 1)
  {
    tmp0   = btor_bv_slice (mm, d_x->lo, wx - 2, 0);
    tmp1   = btor_bv_slice (mm, d_z->lo, wx - 2, 0);
    x_or_z = btor_bv_or (mm, tmp0, tmp1);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);

    tmp0    = btor_bv_slice (mm, d_x->hi, wx - 2, 0);
    tmp1    = btor_bv_slice (mm, d_z->hi, wx - 2, 0);
    x_and_z = btor_bv_and (mm, tmp0, tmp1);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);
  }
  slice_lo_z_hi =
      wx > 1 ? btor_bv_slice (mm, d_z->lo, wz - 1, wx - 1) : d_z->lo;
  slice_hi_z_hi =
      wx > 1 ? btor_bv_slice (mm, d_z->hi, wz - 1, wx - 1) : d_z->hi;

  redor  = btor_bv_redor (mm, slice_lo_z_hi);
  redand = btor_bv_redand (mm, slice_hi_z_hi);

  /**
   * lo_x' = (lo_x[wx-1:wx-1] | redor (lo_z[wz-1:wx-1]))
   *         :: (lo_x[wx-2:0] | lo_z[wx-2:0])
   */
  tmp1 = btor_bv_slice (mm, d_x->lo, wx - 1, wx - 1);
  tmp0 = btor_bv_or (mm, tmp1, redor);
  btor_bv_free (mm, tmp1);
  if (wx > 1)
  {
    (*res_d_x)->lo = btor_bv_concat (mm, tmp0, x_or_z);
    btor_bv_free (mm, tmp0);
  }
  else
  {
    (*res_d_x)->lo = tmp0;
  }

  /**
   * hi_x' = (hi_x[wx-1:wx-1] & redand (hi_z[wz-1:wx-1]))
   *         :: (hi_x[wx-2:0] & hi_z[wx-2:0])
   */
  tmp1 = btor_bv_slice (mm, d_x->hi, wx - 1, wx - 1);
  tmp0 = btor_bv_and (mm, tmp1, redand);
  btor_bv_free (mm, tmp1);
  if (wx > 1)
  {
    (*res_d_x)->hi = btor_bv_concat (mm, tmp0, x_and_z);
    btor_bv_free (mm, tmp0);
  }
  else
  {
    (*res_d_x)->hi = tmp0;
  }

  /**
   * lo_z' = (lo_z[wz-1:wx-1]
   *          | sext(redor (lo_z[wz-1:wx-1]), wn)
   *          | sext(lo_x[wx-1:wx-1], wn))
   *         :: (lo_z[wx-2:0] | lo_x[wx-2:0])
   */
  tmp0 = lo_x_lsb ? btor_bv_ones (mm, wn + 1) : btor_bv_zero (mm, wn + 1);
  tmp1 = btor_bv_or (mm, slice_lo_z_hi, tmp0);
  btor_bv_free (mm, tmp0);
  tmp2 = btor_bv_sext (mm, redor, wn);
  tmp0 = btor_bv_or (mm, tmp1, tmp2);
  btor_bv_free (mm, tmp1);
  btor_bv_free (mm, tmp2);
  if (wx > 1)
  {
    (*res_d_z)->lo = btor_bv_concat (mm, tmp0, x_or_z);
    btor_bv_free (mm, tmp0);
  }
  else
  {
    (*res_d_z)->lo = tmp0;
  }

  /**
   * hi_z' = (hi_z[[wz-1:wx-1]
   *          & sext(redand (lo_z[wz-1:wx-1]), wn)
   *          & sext(hi_x[wx-1:wx-1], wn))
   *         :: (hi_z[wx-2:0] & hi_x[wx-2:0])
   */
  tmp0 = hi_x_lsb ? btor_bv_ones (mm, wn + 1) : btor_bv_zero (mm, wn + 1);
  tmp1 = btor_bv_and (mm, slice_hi_z_hi, tmp0);
  btor_bv_free (mm, tmp0);
  tmp2 = btor_bv_sext (mm, redand, wn);
  tmp0 = btor_bv_and (mm, tmp1, tmp2);
  btor_bv_free (mm, tmp1);
  btor_bv_free (mm, tmp2);
  if (wx > 1)
  {
    (*res_d_z)->hi = btor_bv_concat (mm, tmp0, x_and_z);
    btor_bv_free (mm, tmp0);
  }
  else
  {
    (*res_d_z)->hi = tmp0;
  }

  if (wx > 1)
  {
    btor_bv_free (mm, x_or_z);
    btor_bv_free (mm, x_and_z);
    btor_bv_free (mm, slice_lo_z_hi);
    btor_bv_free (mm, slice_hi_z_hi);
  }
  btor_bv_free (mm, redor);
  btor_bv_free (mm, redand);

#if 0
  /* These are the propagators from [1] which are incorrect!
   * E.g. for x = 1 and z = 001 we expect an invalid result, but these
   * propagators produce x' = 1 and z' = 111. */

  uint32_t i, lo_z_bit, hi_z_bit;
  BtorBvDomain *tmp_x = btor_bvprop_new (mm, d_x->lo, d_x->hi);

  /**
   * lo_x' = lo_x | (lo_z & mask1) with mask1 = 0_[wn] :: ~0_[wx]
   * simplifies to
   * lo_x' = lo_x | lo_z[wx-1:0]
   */
  slice = btor_bv_slice (mm, d_z->lo, wx-1, 0);
  (*res_tmp_x)->lo = btor_bv_or (mm, tmp_x->lo, slice);
  btor_bv_free (mm, slice);

  /**
   * hi_x' = hi_x & (hi_z & mask1)
   * simplifies to
   * hi_x' = hi_x & hi_z[wx-1:0]
   */
  slice = btor_bv_slice (mm, d_z->hi, wx-1, 0);
  (*res_tmp_x)->hi = btor_bv_and (mm, tmp_x->hi, slice);
  btor_bv_free (mm, slice);

  if (!lo_x_lsb && !hi_x_lsb)     /* sign bit 0 */
  {
SEXT_SIGN_0:
    /**
     * lo_z' = (lo_x | mask2) | lo_z with mask2 = 0_[wx+wn]
     * simplifies to
     * lo_x' = uext(lo_x, wn) | lo_z
     */
    tmp0 = btor_bv_uext(mm, tmp_x->lo, wn);
    (*res_d_z)->lo = btor_bv_or (mm, d_z->lo, tmp0);
    btor_bv_free (mm, tmp0);

    /**
     * hi_z' = (hi_x | mask2) & hi_z
     * simplifies to
     * hi_z' = uext(hi_x, wn) & hi_z
     */
    tmp0 = btor_bv_uext(mm, tmp_x->hi, wn);
    (*res_d_z)->hi = btor_bv_and (mm, d_z->hi, tmp0);
    btor_bv_free (mm, tmp0);
  }
  else if (lo_x_lsb && hi_x_lsb)  /* sign bit 1 */
  {
SEXT_SIGN_1:
    tmp0 = btor_bv_ones (mm, wn);
    /**
     * lo_z' = lo_x | mask2 with mask2 = ~0_[wn] :: 0_[wx]
     * simplifies to
     * lo_z' = ~0_[wn] :: lo_x
     */
    (*res_d_z)->lo = btor_bv_concat (mm, tmp0, tmp_x->lo);
    /**
     * hi_z' = hi_x | mask2
     * simplifies to
     * hi_z' = ~0_[wn] :: hi_x
     */
    (*res_d_z)->hi = btor_bv_concat (mm, tmp0, tmp_x->hi);
    btor_bv_free (mm, tmp0);
  }
  else                            /* sign bit x */
  {
    assert (!lo_x_lsb && hi_x_lsb);

    for (i = wz - 1; i >= wx - 1; i--)
    {
      lo_z_bit = btor_bv_get_bit (d_z->lo, i);
      hi_z_bit = btor_bv_get_bit (d_z->hi, i);
      /* if exists z_i = 0 with i >= wx - 1 apply rule for zero sign bit */
      if (!lo_z_bit && !hi_z_bit)
      {
        btor_bv_set_bit (tmp_x->lo, wx - 1, 0);
        goto SEXT_SIGN_0;
      }
      /* if exists z_i = 1 with i >= wx - 1 apply rule for one sign bit */
      if (lo_z_bit && hi_z_bit)
      {
        btor_bv_set_bit (tmp_x->lo, wx - 1, 1);
        goto SEXT_SIGN_1;
      }
    }
    /**
     * lo_z' = lo_z | (lo_x | mask3) with mask3 = 0_[wz]
     * simplifies to
     * lo_x' = lo_z | uext(lo_x, wn)
     */
    tmp0 = btor_bv_uext (mm, tmp_x->lo, wn);
    (*res_d_x)->lo = btor_bv_or (mm, d_z->lo, tmp0);
    btor_bv_free (mm, tmp0);

    /**
     * hi_z' = hi_z & (hi_x | mask2) with mask2 = ~0_[wn] :: 0_[wx]
     * simplifies to
     * hi_z' = hi_z & (~0_[wn] :: hi_x)
     */
    tmp0 = btor_bv_ones (mm, wn);
    tmp1 = btor_bv_concat (mm, tmp0, tmp_x->hi);
    (*res_d_x)->lo = btor_bv_and (mm, d_z->hi, tmp1);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);
  }
  btor_bvprop_free (mm, tmp_x);
#endif
  return btor_bvprop_is_valid (mm, *res_d_x)
         && btor_bvprop_is_valid (mm, *res_d_z);
}

bool
btor_bvprop_ite (BtorMemMgr *mm,
                 BtorBvDomain *d_c,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_y,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_c,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_y,
                 BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_c);
  assert (btor_bvprop_is_valid (mm, d_c));
  assert (d_c->lo->width == 1);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_y);
  assert (btor_bvprop_is_valid (mm, d_y));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (res_d_c);
  assert (res_d_x);
  assert (res_d_y);
  assert (res_d_z);

  bool res;
  uint32_t bw;
  bool progress, c_is_fixed;
  BtorBvDomain *tmp_bvc, *res_tmp_bvc, *tmp_x, *tmp_y, *tmp_z, *tmp_c;
  BtorBitVector *not_hi_x, *not_lo_x, *not_hi_y, *not_hi_z, *not_hi_bvc;
  BtorBitVector *ones, *zero, *tmp0, *tmp1, *tmp2;

  res = true;

  bw = d_x->lo->width;
  assert (bw == d_x->hi->width);
  assert (bw == d_y->lo->width);
  assert (bw == d_y->hi->width);
  assert (bw == d_z->lo->width);
  assert (bw == d_z->hi->width);

  ones = btor_bv_ones (mm, bw);
  zero = btor_bv_zero (mm, bw);

  if (btor_bvprop_is_fixed (mm, d_c))
  {
    c_is_fixed = true;
    if (btor_bv_get_bit (d_c->lo, 0) == 0)
    {
      tmp_bvc = btor_bvprop_new (mm, zero, zero);
    }
    else
    {
      assert (btor_bv_get_bit (d_c->lo, 0) == 1);
      tmp_bvc = btor_bvprop_new (mm, ones, ones);
    }
  }
  else
  {
    c_is_fixed = false;
    tmp_bvc    = btor_bvprop_new_init (mm, bw);
  }

  tmp_x = btor_bvprop_new (mm, d_x->lo, d_x->hi);
  tmp_y = btor_bvprop_new (mm, d_y->lo, d_y->hi);
  tmp_z = btor_bvprop_new (mm, d_z->lo, d_z->hi);
  tmp_c = btor_bvprop_new (mm, d_c->lo, d_c->hi);

  not_hi_x   = 0;
  not_lo_x   = 0;
  not_hi_y   = 0;
  not_hi_z   = 0;
  not_hi_bvc = 0;

  do
  {
    progress = false;

    res_tmp_bvc = new_domain (mm);
    *res_d_x    = new_domain (mm);
    *res_d_y    = new_domain (mm);
    *res_d_z    = new_domain (mm);

    if (not_hi_x) btor_bv_free (mm, not_hi_x);
    if (not_lo_x) btor_bv_free (mm, not_lo_x);
    if (not_hi_y) btor_bv_free (mm, not_hi_y);
    if (not_hi_z) btor_bv_free (mm, not_hi_z);
    if (not_hi_bvc) btor_bv_free (mm, not_hi_bvc);

    not_hi_x   = btor_bv_not (mm, tmp_x->hi);
    not_lo_x   = btor_bv_not (mm, tmp_x->lo);
    not_hi_y   = btor_bv_not (mm, tmp_y->hi);
    not_hi_z   = btor_bv_not (mm, tmp_z->hi);
    not_hi_bvc = btor_bv_not (mm, tmp_bvc->hi);

    /* lo_bvc' = lo_bvc | (lo_z & (~hi_y)) | ((~hi_z) & lo_y) */
    tmp0            = btor_bv_and (mm, not_hi_z, tmp_y->lo);
    tmp1            = btor_bv_and (mm, tmp_z->lo, not_hi_y);
    tmp2            = btor_bv_or (mm, tmp0, tmp1);
    res_tmp_bvc->lo = btor_bv_or (mm, tmp_bvc->lo, tmp2);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);
    btor_bv_free (mm, tmp2);

    /* hi_bvc' = hi_bvc & (~lo_z | hi_x) & (hi_z | (~lo_x)) */
    tmp0 = btor_bv_or (mm, tmp_z->hi, not_lo_x);
    tmp1 = btor_bv_not (mm, tmp_z->lo);
    tmp2 = btor_bv_or (mm, tmp1, tmp_x->hi);
    btor_bv_free (mm, tmp1);
    tmp1            = btor_bv_and (mm, tmp0, tmp2);
    res_tmp_bvc->hi = btor_bv_and (mm, tmp_bvc->hi, tmp1);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);
    btor_bv_free (mm, tmp2);

    /* lo_x' = lo_x | (lo_z & (lo_bvc | (~hi_y))) */
    tmp0           = btor_bv_or (mm, tmp_bvc->lo, not_hi_y);
    tmp1           = btor_bv_and (mm, tmp_z->lo, tmp0);
    (*res_d_x)->lo = btor_bv_or (mm, tmp_x->lo, tmp1);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);

    /* hi_x' = hi_x & (~((~hi_z) & (lo_bvc | lo_y))) */
    tmp0           = btor_bv_or (mm, tmp_bvc->lo, tmp_y->lo);
    tmp1           = btor_bv_and (mm, not_hi_z, tmp0);
    tmp2           = btor_bv_not (mm, tmp1);
    (*res_d_x)->hi = btor_bv_and (mm, tmp_x->hi, tmp2);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);
    btor_bv_free (mm, tmp2);

    /* lo_y' = lo_y | (lo_z & ((~hi_bvc) | (~hi_x))) */
    tmp0           = btor_bv_or (mm, not_hi_bvc, not_hi_x);
    tmp1           = btor_bv_and (mm, tmp_z->lo, tmp0);
    (*res_d_y)->lo = btor_bv_or (mm, tmp_y->lo, tmp1);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);

    /* hi_y' = hi_y & (hi_z | (hi_bvc & ~lo_x)) */
    tmp0           = btor_bv_and (mm, tmp_bvc->hi, not_lo_x);
    tmp1           = btor_bv_or (mm, tmp_z->hi, tmp0);
    (*res_d_y)->hi = btor_bv_and (mm, tmp_y->hi, tmp1);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);

    /* lo_z' = lo_z | (lo_bvc & lo_x) | ((~hi_bvc) & lo_y) | (lo_x & lo_y) */
    tmp0 = btor_bv_and (mm, tmp_x->lo, tmp_y->lo);
    tmp1 = btor_bv_and (mm, not_hi_bvc, tmp_y->lo);
    tmp2 = btor_bv_or (mm, tmp0, tmp1);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);
    tmp0           = btor_bv_and (mm, tmp_bvc->lo, tmp_x->lo);
    tmp1           = btor_bv_or (mm, tmp0, tmp2);
    (*res_d_z)->lo = btor_bv_or (mm, tmp_z->lo, tmp1);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);
    btor_bv_free (mm, tmp2);

    /* hi_z' = hi_z & (~lo_bvc | hi_x) & (hi_bvc | hi_y) & (hi_x | hi_y) */
    tmp0 = btor_bv_or (mm, tmp_x->hi, tmp_y->hi);
    tmp1 = btor_bv_or (mm, tmp_bvc->hi, tmp_y->hi);
    tmp2 = btor_bv_and (mm, tmp0, tmp1);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);
    tmp0 = btor_bv_not (mm, tmp_bvc->lo);
    tmp1 = btor_bv_or (mm, tmp0, tmp_x->hi);
    btor_bv_free (mm, tmp0);
    tmp0           = btor_bv_and (mm, tmp1, tmp2);
    (*res_d_z)->hi = btor_bv_and (mm, tmp_z->hi, tmp0);
    btor_bv_free (mm, tmp0);
    btor_bv_free (mm, tmp1);
    btor_bv_free (mm, tmp2);

    if (!btor_bvprop_is_valid (mm, res_tmp_bvc)
        || !btor_bvprop_is_valid (mm, *res_d_x)
        || !btor_bvprop_is_valid (mm, *res_d_y)
        || !btor_bvprop_is_valid (mm, *res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, tmp_x);
      btor_bvprop_free (mm, tmp_y);
      btor_bvprop_free (mm, tmp_z);
      btor_bvprop_free (mm, res_tmp_bvc);
      tmp_x = *res_d_x;
      tmp_y = *res_d_y;
      tmp_z = *res_d_z;
      goto DONE;
    }

    if (bw > 1 && !progress)
    {
      progress = made_progress (tmp_x,
                                tmp_y,
                                tmp_z,
                                tmp_bvc,
                                *res_d_x,
                                *res_d_y,
                                *res_d_z,
                                res_tmp_bvc);
    }

    btor_bvprop_free (mm, tmp_x);
    btor_bvprop_free (mm, tmp_y);
    btor_bvprop_free (mm, tmp_z);
    btor_bvprop_free (mm, tmp_bvc);
    tmp_x   = *res_d_x;
    tmp_y   = *res_d_y;
    tmp_z   = *res_d_z;
    tmp_bvc = res_tmp_bvc;

    if (bw > 1 && !c_is_fixed && progress)
    {
      if (!btor_bvprop_sext (mm, tmp_c, tmp_bvc, res_d_c, &res_tmp_bvc))
      {
        res = false;
        btor_bvprop_free (mm, tmp_c);
        tmp_c = *res_d_c;
        btor_bvprop_free (mm, res_tmp_bvc);
        goto DONE;
      }
      btor_bvprop_free (mm, tmp_c);
      btor_bvprop_free (mm, tmp_bvc);
      tmp_c   = *res_d_c;
      tmp_bvc = res_tmp_bvc;
    }
  } while (progress);

  assert (btor_bvprop_is_valid (mm, tmp_bvc));
  assert (btor_bvprop_is_valid (mm, tmp_c));
  assert (btor_bvprop_is_valid (mm, tmp_x));
  assert (btor_bvprop_is_valid (mm, tmp_y));
  assert (btor_bvprop_is_valid (mm, tmp_z));

DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;
  *res_d_c = tmp_c;

  btor_bv_free (mm, not_hi_x);
  btor_bv_free (mm, not_lo_x);
  btor_bv_free (mm, not_hi_y);
  btor_bv_free (mm, not_hi_z);
  btor_bv_free (mm, not_hi_bvc);

  btor_bv_free (mm, ones);
  btor_bv_free (mm, zero);
  btor_bvprop_free (mm, tmp_bvc);

  return res;
}

static bool
bvprop_add_aux (BtorMemMgr *mm,
                BtorBvDomain *d_x,
                BtorBvDomain *d_y,
                BtorBvDomain *d_z,
                BtorBvDomain *d_cout,
                BtorBvDomain **res_d_x,
                BtorBvDomain **res_d_y,
                BtorBvDomain **res_d_z,
                BtorBvDomain **res_d_cout,
                bool no_overflows)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_y);
  assert (btor_bvprop_is_valid (mm, d_y));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (res_d_x);
  assert (res_d_y);
  assert (res_d_z);
  assert (res_d_cout);

  bool progress, res;
  uint32_t bw;
  BtorBitVector *one;
  BtorBvDomain *tmp_x, *tmp_y, *tmp_z;
  BtorBvDomain *tmp_cin, *tmp_cout;
  BtorBvDomain *tmp_x_xor_y, *tmp_x_and_y;
  BtorBvDomain *tmp_cin_and_x_xor_y;
  BtorBvDomain *tmp_cout_msb;
  BtorBvDomain *d_one;

  res = true;

  bw = d_x->lo->width;
  assert (bw == d_x->hi->width);
  assert (bw == d_y->lo->width);
  assert (bw == d_y->hi->width);
  assert (bw == d_z->lo->width);
  assert (bw == d_z->hi->width);
  one = btor_bv_one (mm, bw);

  /* cin = x...x0 */
  tmp_cin = btor_bvprop_new_init (mm, bw);
  btor_bv_set_bit (tmp_cin->hi, 0, 0);
  /* cout = x...x if not given */
  tmp_cout = d_cout ? btor_bvprop_new (mm, d_cout->lo, d_cout->hi)
                    : btor_bvprop_new_init (mm, bw);

  /**
   * full adder:
   * z    = x ^ y ^ cin
   * cout = (x & y) | (cin & (x ^ y))
   * cin  = cout << 1
   */

  tmp_x = btor_bvprop_new (mm, d_x->lo, d_x->hi);
  tmp_y = btor_bvprop_new (mm, d_y->lo, d_y->hi);
  tmp_z = btor_bvprop_new (mm, d_z->lo, d_z->hi);

  tmp_x_xor_y         = btor_bvprop_new_init (mm, bw);
  tmp_x_and_y         = btor_bvprop_new_init (mm, bw);
  tmp_cin_and_x_xor_y = btor_bvprop_new_init (mm, bw);

  tmp_cout_msb = 0;
  d_one        = 0;
  if (no_overflows)
  {
    tmp_cout_msb = btor_bvprop_new_init (mm, 1);
    d_one        = btor_bvprop_new_init (mm, 1);
    btor_bv_set_bit (d_one->lo, 0, 1);
  }

  do
  {
    progress = false;

    /* x_xor_y = x ^ y */
    if (!btor_bvprop_xor (
            mm, tmp_x, tmp_y, tmp_x_xor_y, res_d_x, res_d_y, res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_y);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_y));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress (
          tmp_x, tmp_y, tmp_x_xor_y, 0, *res_d_x, *res_d_y, *res_d_z, 0);
    }
    btor_bvprop_free (mm, tmp_x);
    btor_bvprop_free (mm, tmp_y);
    btor_bvprop_free (mm, tmp_x_xor_y);
    tmp_x       = *res_d_x;
    tmp_y       = *res_d_y;
    tmp_x_xor_y = *res_d_z;

    /* z = x_xor_y ^ cin */
    if (!btor_bvprop_xor (
            mm, tmp_x_xor_y, tmp_cin, tmp_z, res_d_x, res_d_y, res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_y);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_y));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress (
          tmp_x_xor_y, tmp_cin, tmp_z, 0, *res_d_x, *res_d_y, *res_d_z, 0);
    }
    btor_bvprop_free (mm, tmp_x_xor_y);
    btor_bvprop_free (mm, tmp_cin);
    btor_bvprop_free (mm, tmp_z);
    tmp_x_xor_y = *res_d_x;
    tmp_cin     = *res_d_y;
    tmp_z       = *res_d_z;

    /* x_and_y = x & y */
    if (!btor_bvprop_and (
            mm, tmp_x, tmp_y, tmp_x_and_y, res_d_x, res_d_y, res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_y);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_y));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress (
          tmp_x, tmp_y, tmp_x_and_y, 0, *res_d_x, *res_d_y, *res_d_z, 0);
    }
    btor_bvprop_free (mm, tmp_x);
    btor_bvprop_free (mm, tmp_y);
    btor_bvprop_free (mm, tmp_x_and_y);
    tmp_x       = *res_d_x;
    tmp_y       = *res_d_y;
    tmp_x_and_y = *res_d_z;

    /* cin_and_x_xor_y = cin & x_xor_y */
    if (!btor_bvprop_and (mm,
                          tmp_cin,
                          tmp_x_xor_y,
                          tmp_cin_and_x_xor_y,
                          res_d_x,
                          res_d_y,
                          res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_y);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_y));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress (tmp_cin,
                                tmp_x_xor_y,
                                tmp_cin_and_x_xor_y,
                                0,
                                *res_d_x,
                                *res_d_y,
                                *res_d_z,
                                0);
    }
    btor_bvprop_free (mm, tmp_cin);
    btor_bvprop_free (mm, tmp_x_xor_y);
    btor_bvprop_free (mm, tmp_cin_and_x_xor_y);
    tmp_cin             = *res_d_x;
    tmp_x_xor_y         = *res_d_y;
    tmp_cin_and_x_xor_y = *res_d_z;

    /* cout = x_and_y | cin_and_x_xor_y */
    if (!btor_bvprop_or (mm,
                         tmp_x_and_y,
                         tmp_cin_and_x_xor_y,
                         tmp_cout,
                         res_d_x,
                         res_d_y,
                         res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_y);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_y));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress (tmp_x_and_y,
                                tmp_cin_and_x_xor_y,
                                tmp_cout,
                                0,
                                *res_d_x,
                                *res_d_y,
                                *res_d_z,
                                0);
    }
    btor_bvprop_free (mm, tmp_x_and_y);
    btor_bvprop_free (mm, tmp_cin_and_x_xor_y);
    btor_bvprop_free (mm, tmp_cout);
    tmp_x_and_y         = *res_d_x;
    tmp_cin_and_x_xor_y = *res_d_y;
    tmp_cout            = *res_d_z;

    /* cin  = cout << 1 */
    if (!btor_bvprop_sll_const (mm, tmp_cout, tmp_cin, one, res_d_x, res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress =
          made_progress (tmp_cout, 0, tmp_cin, 0, *res_d_x, 0, *res_d_z, 0);
    }
    btor_bvprop_free (mm, tmp_cout);
    btor_bvprop_free (mm, tmp_cin);
    tmp_cout = *res_d_x;
    tmp_cin  = *res_d_z;

    if (no_overflows)
    {
      assert (tmp_cout_msb);
      assert (d_one);

      /**
       * Overflow:
       * cout[MSB:MSB] == 1
       *
       * Add no-overflow propagation constraint:
       * cout[MSB:MSB] == 0
       * <->
       * 1 xor cout[MSB:MSB] = 1
       */

      /* cout[MSB:MSB] */
      if (!btor_bvprop_slice (
              mm, tmp_cout, tmp_cout_msb, bw - 1, bw - 1, res_d_x, res_d_z))
      {
        res = false;
        btor_bvprop_free (mm, *res_d_x);
        btor_bvprop_free (mm, *res_d_z);
        goto DONE;
      }
      assert (btor_bvprop_is_valid (mm, *res_d_x));
      assert (btor_bvprop_is_valid (mm, *res_d_z));
      if (!progress)
      {
        progress = made_progress (
            tmp_cout, 0, tmp_cout_msb, 0, *res_d_x, 0, *res_d_z, 0);
      }
      btor_bvprop_free (mm, tmp_cout);
      btor_bvprop_free (mm, tmp_cout_msb);
      tmp_cout     = *res_d_x;
      tmp_cout_msb = *res_d_z;

      /* 1 xor cout[MSB:MSB] = 1 */
      if (!btor_bvprop_xor (
              mm, d_one, tmp_cout_msb, d_one, res_d_x, res_d_y, res_d_z))
      {
        res = false;
        btor_bvprop_free (mm, *res_d_x);
        btor_bvprop_free (mm, *res_d_y);
        btor_bvprop_free (mm, *res_d_z);
        goto DONE;
      }
      assert (btor_bvprop_is_valid (mm, *res_d_x));
      assert (btor_bvprop_is_valid (mm, *res_d_y));
      assert (btor_bvprop_is_valid (mm, *res_d_z));
      if (!progress)
      {
        progress = made_progress (
            d_one, tmp_cout_msb, d_one, 0, *res_d_x, *res_d_y, *res_d_z, 0);
      }
      assert (!btor_bv_compare (d_one->lo, (*res_d_x)->lo));
      assert (!btor_bv_compare (d_one->hi, (*res_d_x)->hi));
      assert (!btor_bv_compare (d_one->lo, (*res_d_z)->lo));
      assert (!btor_bv_compare (d_one->hi, (*res_d_z)->hi));
      btor_bvprop_free (mm, tmp_cout_msb);
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_z);
      tmp_cout_msb = *res_d_y;
    }
  } while (progress);

  assert (btor_bvprop_is_valid (mm, tmp_x));
  assert (btor_bvprop_is_valid (mm, tmp_y));
  assert (btor_bvprop_is_valid (mm, tmp_z));

DONE:
  *res_d_x    = tmp_x;
  *res_d_y    = tmp_y;
  *res_d_z    = tmp_z;
  *res_d_cout = tmp_cout;

  btor_bvprop_free (mm, tmp_cin);
  btor_bvprop_free (mm, tmp_x_xor_y);
  btor_bvprop_free (mm, tmp_x_and_y);
  btor_bvprop_free (mm, tmp_cin_and_x_xor_y);
  if (tmp_cout_msb) btor_bvprop_free (mm, tmp_cout_msb);
  if (d_one) btor_bvprop_free (mm, d_one);

  btor_bv_free (mm, one);

  return res;
}

bool
btor_bvprop_add_aux (BtorMemMgr *mm,
                     BtorBvDomain *d_x,
                     BtorBvDomain *d_y,
                     BtorBvDomain *d_z,
                     BtorBvDomain **res_d_x,
                     BtorBvDomain **res_d_y,
                     BtorBvDomain **res_d_z,
                     bool no_overflows)
{
  bool res;
  BtorBvDomain *res_d_cout;
  res = bvprop_add_aux (mm,
                        d_x,
                        d_y,
                        d_z,
                        0,
                        res_d_x,
                        res_d_y,
                        res_d_z,
                        &res_d_cout,
                        no_overflows);
  btor_bvprop_free (mm, res_d_cout);
  return res;
}

bool
btor_bvprop_add (BtorMemMgr *mm,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_y,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_y,
                 BtorBvDomain **res_d_z)
{
  return btor_bvprop_add_aux (
      mm, d_x, d_y, d_z, res_d_x, res_d_y, res_d_z, false);
}

bool
btor_bvprop_mul_aux (BtorMemMgr *mm,
                     BtorBvDomain *d_x,
                     BtorBvDomain *d_y,
                     BtorBvDomain *d_z,
                     BtorBvDomain **res_d_x,
                     BtorBvDomain **res_d_y,
                     BtorBvDomain **res_d_z,
                     bool no_overflows)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_y);
  assert (btor_bvprop_is_valid (mm, d_y));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));
  assert (res_d_x);
  assert (res_d_y);
  assert (res_d_z);

  /* z_[bw] = x_[bw] * y_[bw]
   * rewrites to
   * ite (y[bw-1:bw-1], x << (bw - 1), 0)
   *   + ite (y[bw-2:bw-2], x << (bw-2), 0)
   *   + ...
   *   + ite (y[1:1], x << 1, 0)
   *   + ite (y[0:0], x, 0)
   */

  uint32_t i, bw, bwo, n;
  bool res, progress;
  BtorBitVector *bv, *lo, *hi;
  BtorBvDomain *d, *d_one, *d_zero;
  BtorBvDomain *tmp_x, *tmp_y, *tmp_z, *tmp_zero;
  BtorBvDomain **tmp_c, **tmp_shift, **tmp_ite, **tmp0, **tmp1, **tmp_add;
  BtorBvDomain *tmp_res_c, *tmp_slice;
  BtorBvDomain **tmp;
  BtorBvDomainPtrStack d_c_stack, d_shift_stack, d_ite_stack, d_add_stack;
  BtorBitVectorPtrStack shift_stack;

  res = true;

  BTOR_INIT_STACK (mm, d_c_stack);
  BTOR_INIT_STACK (mm, d_shift_stack);
  BTOR_INIT_STACK (mm, d_ite_stack);
  BTOR_INIT_STACK (mm, d_add_stack);
  BTOR_INIT_STACK (mm, shift_stack);

  bw = d_x->lo->width;
  assert (bw == d_x->hi->width);
  assert (bw == d_y->lo->width);
  assert (bw == d_y->hi->width);
  assert (bw == d_z->lo->width);
  assert (bw == d_z->hi->width);

  d_one     = 0;
  d_zero    = 0;
  tmp_slice = 0;

  tmp_y = btor_bvprop_new (mm, d_y->lo, d_y->hi);
  tmp_z = btor_bvprop_new (mm, d_z->lo, d_z->hi);

  if (bw == 1)
  {
    /**
     * For bit-width 1, multiplication simplifies to d_z = ite (d_y, x, 0).
     * No overflows for bit-width 1.
     */

    tmp_x = btor_bvprop_new (mm, d_x->lo, d_x->hi);

    bv       = btor_bv_zero (mm, bw);
    tmp_zero = btor_bvprop_new (mm, bv, bv);
    btor_bv_free (mm, bv);

    if (!btor_bvprop_ite (
            mm, d_y, d_x, tmp_zero, d_z, &tmp_res_c, res_d_x, res_d_y, res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, tmp_res_c);
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_y);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    btor_bvprop_free (mm, tmp_x);
    btor_bvprop_free (mm, tmp_y);
    btor_bvprop_free (mm, tmp_z);
    tmp_x = *res_d_x;
    tmp_y = tmp_res_c;
    tmp_z = *res_d_z;
    btor_bvprop_free (mm, *res_d_y);
  }
  else
  {
    /**
     * The full implementation of
     *   ite (y[bw-1:bw-1], x << (bw - 1), 0)
     *     + ite (y[bw-2:bw-2], x << (bw-2), 0)
     *     + ...
     *     + ite (y[1:1], x << 1, 0)
     *     + ite (y[0:0], x, 0)
     * would require n left shift propagators, n ite propagators, and n - 1
     * add propagators (n = bw).
     * We can simplify that since for each ite, the initial result domain is
     * x...x = ite (condition, shift, 0). If the y bit at an index i (and
     * therefore the condition for the i-th ite) is 0, the result of the ite
     * is always 0 (that's the only possible propagation, no invalid results
     * possible). Hence we can skip all 0 bits of y (i.e., all ite with a 0
     * condition), except the last one (the last one is the end result).
     */

    bwo = no_overflows ? 2 * bw : bw;

    if (no_overflows)
    {
      /**
       * no overflows: double the bit-width and assert that the upper half of
       *               the multiplication result is 0
       */

      lo    = btor_bv_uext (mm, d_x->lo, d_x->lo->width);
      hi    = btor_bv_uext (mm, d_x->hi, d_x->hi->width);
      tmp_x = btor_bvprop_new (mm, lo, hi);
      btor_bv_free (mm, lo);
      btor_bv_free (mm, hi);

      tmp_zero     = new_domain (mm);
      tmp_zero->lo = btor_bv_zero (mm, bwo);
      tmp_zero->hi = btor_bv_zero (mm, bwo);

      tmp_slice = btor_bvprop_new_init (mm, bw);

      d_zero     = new_domain (mm);
      d_zero->lo = btor_bv_zero (mm, bw);
      d_zero->hi = btor_bv_zero (mm, bw);

      d_one     = new_domain (mm);
      d_one->lo = btor_bv_one (mm, 1);
      d_one->hi = btor_bv_one (mm, 1);
    }
    else
    {
      tmp_x        = btor_bvprop_new (mm, d_x->lo, d_x->hi);
      tmp_zero     = new_domain (mm);
      tmp_zero->lo = btor_bv_zero (mm, bw);
      tmp_zero->hi = btor_bv_zero (mm, bw);
    }

    for (i = 0; i < bw; i++)
    {
      n = bw - 1 - i;

      /* if y bit is zero, the result of the ite is zero, skip */
      if (i < bw - 1 && !btor_bv_get_bit (d_y->lo, n)
          && !btor_bv_get_bit (d_y->hi, n))
        continue;

      /* slice y into bw ite conditions */
      d     = new_domain (mm);
      d->lo = btor_bv_slice (mm, d_y->lo, n, n);
      d->hi = btor_bv_slice (mm, d_y->hi, n, n);
      BTOR_PUSH_STACK (d_c_stack, d);
      /* m shift propagators (m = number of 1 or x bits in y) */
      d = btor_bvprop_new_init (mm, bwo);
      BTOR_PUSH_STACK (d_shift_stack, d);
      /* m ite propagators */
      d = btor_bvprop_new_init (mm, bwo);
      BTOR_PUSH_STACK (d_ite_stack, d);
      /* m - 1 add propagators */
      if (BTOR_COUNT_STACK (d_c_stack) > 1)
      {
        d = btor_bvprop_new_init (mm, bwo);
        BTOR_PUSH_STACK (d_add_stack, d);
      }
      /* shift width */
      bv = btor_bv_uint64_to_bv (mm, n, bwo);
      BTOR_PUSH_STACK (shift_stack, bv);
    }

    /**
     * if m > 0: final add is end result
     * else    : there is a single ite which is the end result
     */
    if (BTOR_COUNT_STACK (d_add_stack))
    {
      /* last adder is end result: d_z = add_[m-1]*/
      if (no_overflows)
      {
        d     = new_domain (mm);
        d->lo = btor_bv_uext (mm, d_z->lo, d_z->lo->width);
        d->hi = btor_bv_uext (mm, d_z->hi, d_z->hi->width);
      }
      else
      {
        d = btor_bvprop_new (mm, d_z->lo, d_z->hi);
      }
      btor_bvprop_free (mm, BTOR_POP_STACK (d_add_stack));
      BTOR_PUSH_STACK (d_add_stack, d);
    }
    else
    {
      /**
       * We have at least one ite propagator, even if all bits in y are 0.
       * In case there is only a single ite propagator, it is the end result.
       */
      assert (BTOR_COUNT_STACK (d_ite_stack) == 1);
      if (BTOR_COUNT_STACK (d_ite_stack))
      {
        if (no_overflows)
        {
          d     = new_domain (mm);
          d->lo = btor_bv_uext (mm, d_z->lo, d_z->lo->width);
          d->hi = btor_bv_uext (mm, d_z->hi, d_z->hi->width);
        }
        else
        {
          d = btor_bvprop_new (mm, d_z->lo, d_z->hi);
        }
        btor_bvprop_free (mm, BTOR_POP_STACK (d_ite_stack));
        BTOR_PUSH_STACK (d_ite_stack, d);
      }
    }

    assert (BTOR_COUNT_STACK (d_c_stack) == BTOR_COUNT_STACK (d_shift_stack));
    assert (BTOR_COUNT_STACK (d_c_stack) == BTOR_COUNT_STACK (d_ite_stack));
    assert (BTOR_COUNT_STACK (d_c_stack) == BTOR_COUNT_STACK (d_add_stack) + 1);
    assert (BTOR_COUNT_STACK (d_c_stack) == BTOR_COUNT_STACK (shift_stack));

    do
    {
      progress = false;

      for (i = 0; i < BTOR_COUNT_STACK (d_c_stack); i++)
      {
        /**
         * x << bw - 1 - m where m is the current bit index.
         * The shift width of the current bit index (!= i) is stored at index i.
         * The current bit index is not explicit here, since we only generate
         * propagators for bits that 1/x (or for the last 0 bit if y = 0).
         */
        bv        = BTOR_PEEK_STACK (shift_stack, i);
        tmp_shift = &d_shift_stack.start[i];
        if (!btor_bvprop_sll_const (
                mm, tmp_x, *tmp_shift, bv, res_d_x, res_d_z))
        {
          res = false;
          btor_bvprop_free (mm, *res_d_x);
          btor_bvprop_free (mm, *res_d_z);
          goto DONE;
        }
        assert (btor_bvprop_is_valid (mm, *res_d_x));
        assert (btor_bvprop_is_valid (mm, *res_d_z));
        if (!progress)
        {
          progress =
              made_progress (tmp_x, 0, *tmp_shift, 0, *res_d_x, 0, *res_d_z, 0);
        }
        btor_bvprop_free (mm, tmp_x);
        btor_bvprop_free (mm, *tmp_shift);
        tmp_x      = *res_d_x;
        *tmp_shift = *res_d_z;

        /* ite (y[bw-1-m:bw-1-m], x << bw - 1 - m, 0) */
        tmp_c   = &d_c_stack.start[i];
        tmp_ite = &d_ite_stack.start[i];
        assert (!no_overflows || (*tmp_shift)->lo->width == bwo);
        assert (!no_overflows || (tmp_zero)->lo->width == bwo);
        assert (!no_overflows || (*tmp_ite)->lo->width == bwo);
        if (!btor_bvprop_ite (mm,
                              *tmp_c,
                              *tmp_shift,
                              tmp_zero,
                              *tmp_ite,
                              &tmp_res_c,
                              res_d_x,
                              res_d_y,
                              res_d_z))
        {
          res = false;
          btor_bvprop_free (mm, tmp_res_c);
          btor_bvprop_free (mm, *res_d_x);
          btor_bvprop_free (mm, *res_d_y);
          btor_bvprop_free (mm, *res_d_z);
          goto DONE;
        }
        assert (btor_bvprop_is_valid (mm, *res_d_x));
        assert (btor_bvprop_is_valid (mm, *res_d_y));
        assert (btor_bvprop_is_valid (mm, *res_d_z));
        assert (btor_bvprop_is_valid (mm, tmp_res_c));
        if (!progress)
        {
          progress = made_progress (*tmp_shift,
                                    tmp_zero,
                                    *tmp_ite,
                                    *tmp_c,
                                    *res_d_x,
                                    *res_d_y,
                                    *res_d_z,
                                    tmp_res_c);
        }
        btor_bvprop_free (mm, *tmp_shift);
        assert (!btor_bv_compare (tmp_zero->lo, (*res_d_y)->lo)
                && !btor_bv_compare (tmp_zero->hi, (*res_d_y)->hi));
        btor_bvprop_free (mm, *tmp_c);
        btor_bvprop_free (mm, *tmp_ite);
        *tmp_shift = *res_d_x;
        btor_bvprop_free (mm, *res_d_y);
        *tmp_ite = *res_d_z;
        *tmp_c   = tmp_res_c;

        /**
         * ite (y[bw-1:bw-1], x << (bw - 1), 0)
         *   + ite (y[bw-2:bw-2], x << (bw-2), 0)
         *   + ...
         *   + ite (y[1:1], x << 1, 0)
         *   + ite (y[0:0], x, 0)
         *
         * Note that we only create ite for bits in y that are 1/x. Thus, we
         * don't create 'bw' adders but 'm = number of 1/x bits - 1' adders.
         */
        if (i > 0)
        {
          tmp0 = i == 1 ? &d_ite_stack.start[i - 1] : &d_add_stack.start[i - 2];
          tmp1 = tmp_ite;
          tmp_add = &d_add_stack.start[i - 1];
          if (!btor_bvprop_add_aux (mm,
                                    *tmp0,
                                    *tmp1,
                                    *tmp_add,
                                    res_d_x,
                                    res_d_y,
                                    res_d_z,
                                    no_overflows))
          {
            res = false;
            btor_bvprop_free (mm, *res_d_x);
            btor_bvprop_free (mm, *res_d_y);
            btor_bvprop_free (mm, *res_d_z);
            goto DONE;
          }
          assert (btor_bvprop_is_valid (mm, *res_d_x));
          assert (btor_bvprop_is_valid (mm, *res_d_y));
          assert (btor_bvprop_is_valid (mm, *res_d_z));
          if (!progress)
          {
            progress = made_progress (
                *tmp0, *tmp1, *tmp_add, 0, *res_d_x, *res_d_y, *res_d_z, 0);
          }
          btor_bvprop_free (mm, *tmp0);
          btor_bvprop_free (mm, *tmp1);
          btor_bvprop_free (mm, *tmp_add);
          *tmp0    = *res_d_x;
          *tmp1    = *res_d_y;
          *tmp_add = *res_d_z;
        }
      }

      if (no_overflows)
      {
        /* upper half of multiplication result must be 0 */
        tmp = n > 1 ? &d_add_stack.start[n - 2] : &d_ite_stack.start[0];
        if (!btor_bvprop_slice (
                mm, *tmp, tmp_slice, bwo - 1, bw, res_d_x, res_d_z))
        {
          res = false;
          btor_bvprop_free (mm, *res_d_x);
          btor_bvprop_free (mm, *res_d_z);
          goto DONE;
        }
        assert (btor_bvprop_is_valid (mm, *res_d_x));
        assert (btor_bvprop_is_valid (mm, *res_d_z));
        if (!progress)
        {
          progress =
              made_progress (*tmp, 0, tmp_slice, 0, *res_d_x, 0, *res_d_z, 0);
        }
        btor_bvprop_free (mm, *tmp);
        btor_bvprop_free (mm, tmp_slice);
        *tmp      = *res_d_x;
        tmp_slice = *res_d_z;
        assert (!no_overflows || (*tmp)->lo->width == bwo);

        if (!btor_bvprop_eq (
                mm, tmp_slice, d_zero, d_one, res_d_x, res_d_y, res_d_z))
        {
          res = false;
          btor_bvprop_free (mm, *res_d_x);
          btor_bvprop_free (mm, *res_d_y);
          btor_bvprop_free (mm, *res_d_z);
          goto DONE;
        }
        assert (btor_bvprop_is_valid (mm, *res_d_x));
        assert (btor_bvprop_is_valid (mm, *res_d_y));
        assert (!btor_bv_compare (d_zero->lo, (*res_d_y)->lo));
        assert (!btor_bv_compare (d_zero->hi, (*res_d_y)->hi));
        assert (btor_bvprop_is_valid (mm, *res_d_z));
        assert (!btor_bv_compare (d_one->lo, (*res_d_z)->lo));
        assert (!btor_bv_compare (d_one->hi, (*res_d_z)->hi));
        if (!progress)
        {
          progress = made_progress (
              tmp_slice, d_zero, d_one, 0, *res_d_x, *res_d_y, *res_d_z, 0);
        }
        btor_bvprop_free (mm, tmp_slice);
        tmp_slice = *res_d_x;
        btor_bvprop_free (mm, *res_d_y);
        btor_bvprop_free (mm, *res_d_z);
      }
    } while (progress);

    /* Collect y bits into the result for d_y. */
    for (i = 0, n = 0; i < bw; i++)
    {
      if (i < bw - 1 && !btor_bv_get_bit (tmp_y->lo, bw - 1 - i)
          && !btor_bv_get_bit (tmp_y->hi, bw - 1 - i))
        continue;
      assert (n < BTOR_COUNT_STACK (d_c_stack));
      d = BTOR_PEEK_STACK (d_c_stack, n);
      assert (d->lo->width == 1);
      assert (d->hi->width == 1);
      btor_bv_set_bit (tmp_y->lo, bw - 1 - i, btor_bv_get_bit (d->lo, 0));
      btor_bv_set_bit (tmp_y->hi, bw - 1 - i, btor_bv_get_bit (d->hi, 0));
      n += 1;
    }
    assert (n == BTOR_COUNT_STACK (d_c_stack));

    /* Result for d_z. */
    btor_bvprop_free (mm, tmp_z);
    tmp_z = new_domain (mm);
    tmp   = n > 1 ? &d_add_stack.start[n - 2] : &d_ite_stack.start[0];
    if (no_overflows)
    {
      tmp_z->lo = btor_bv_slice (mm, (*tmp)->lo, bw - 1, 0);
      tmp_z->hi = btor_bv_slice (mm, (*tmp)->hi, bw - 1, 0);
    }
    else
    {
      tmp_z->lo = btor_bv_copy (mm, (*tmp)->lo);
      tmp_z->hi = btor_bv_copy (mm, (*tmp)->hi);
    }
  }
  assert (btor_bvprop_is_valid (mm, tmp_x));
  assert (btor_bvprop_is_valid (mm, tmp_y));
  assert (btor_bvprop_is_valid (mm, tmp_z));
DONE:
  if (bw > 1 && no_overflows)
  {
    lo = btor_bv_slice (mm, tmp_x->lo, bw - 1, 0);
    hi = btor_bv_slice (mm, tmp_x->hi, bw - 1, 0);
    btor_bvprop_free (mm, tmp_x);
    tmp_x     = new_domain (mm);
    tmp_x->lo = lo;
    tmp_x->hi = hi;
  }

  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  btor_bvprop_free (mm, tmp_zero);
  if (tmp_slice) btor_bvprop_free (mm, tmp_slice);
  if (d_one) btor_bvprop_free (mm, d_one);
  if (d_zero) btor_bvprop_free (mm, d_zero);

  for (i = 0, n = BTOR_COUNT_STACK (d_c_stack); i < n; i++)
  {
    assert (!BTOR_EMPTY_STACK (d_c_stack));
    assert (!BTOR_EMPTY_STACK (d_shift_stack));
    assert (!BTOR_EMPTY_STACK (d_ite_stack));
    assert (!BTOR_EMPTY_STACK (shift_stack));
    btor_bvprop_free (mm, BTOR_POP_STACK (d_c_stack));
    btor_bvprop_free (mm, BTOR_POP_STACK (d_shift_stack));
    btor_bvprop_free (mm, BTOR_POP_STACK (d_ite_stack));
    btor_bv_free (mm, BTOR_POP_STACK (shift_stack));
    if (i < n - 1)
    {
      assert (!BTOR_EMPTY_STACK (d_add_stack));
      btor_bvprop_free (mm, BTOR_POP_STACK (d_add_stack));
    }
  }
  BTOR_RELEASE_STACK (d_c_stack);
  BTOR_RELEASE_STACK (d_shift_stack);
  BTOR_RELEASE_STACK (d_ite_stack);
  BTOR_RELEASE_STACK (d_add_stack);
  BTOR_RELEASE_STACK (shift_stack);
  return res;
}

bool
btor_bvprop_mul (BtorMemMgr *mm,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_y,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_y,
                 BtorBvDomain **res_d_z)
{
  return btor_bvprop_mul_aux (
      mm, d_x, d_y, d_z, res_d_x, res_d_y, res_d_z, false);
}

bool
btor_bvprop_ult (BtorMemMgr *mm,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_y,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_y,
                 BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (btor_bvprop_is_valid (mm, d_x));
  assert (d_y);
  assert (btor_bvprop_is_valid (mm, d_y));
  assert (d_z);
  assert (btor_bvprop_is_valid (mm, d_z));

  bool progress, res;
  uint32_t bw;
  BtorBitVector *one;
  BtorBvDomain *tmp_add_1, *tmp_add_2;
  BtorBvDomain *tmp_cout_1, *tmp_cout_msb_1, *tmp_cout_2, *tmp_cout_msb_2;
  BtorBvDomain *tmp_x, *tmp_y, *tmp_not_y, *tmp_z, *tmp_cout_msb;
  BtorBvDomain *res_d_cout;
  BtorBvDomain *d_one;

  res = true;

  bw = d_x->lo->width;
  assert (bw == d_x->hi->width);
  assert (bw == d_y->lo->width);
  assert (bw == d_y->hi->width);
  assert (d_z->lo->width == 1);
  assert (d_z->hi->width == 1);

  /**
   * z_[1] = x_[bw] < y_[bw]
   *       = ~(cout(x - y))[MSB:MSB]
   *       = ~(cout(x + (~y + 1)))[MSB:MSB]
   *       = ~(cout(~y + 1)[MSB:MSB] | cout(x + (~y + 1))[MSB:MSB]) */

  tmp_x = btor_bvprop_new (mm, d_x->lo, d_x->hi);
  tmp_y = btor_bvprop_new (mm, d_y->lo, d_y->hi);
  tmp_z = btor_bvprop_new (mm, d_z->lo, d_z->hi);

  tmp_not_y  = btor_bvprop_new_init (mm, bw);
  tmp_add_1  = btor_bvprop_new_init (mm, bw);
  tmp_add_2  = btor_bvprop_new_init (mm, bw);
  tmp_cout_1 = btor_bvprop_new_init (mm, bw);
  tmp_cout_2 = btor_bvprop_new_init (mm, bw);

  tmp_cout_msb   = btor_bvprop_new_init (mm, 1);
  tmp_cout_msb_1 = btor_bvprop_new_init (mm, 1);
  tmp_cout_msb_2 = btor_bvprop_new_init (mm, 1);

  one   = btor_bv_one (mm, bw);
  d_one = btor_bvprop_new (mm, one, one);

  do
  {
    progress = false;

    /* not_y = ~y */
    if (!btor_bvprop_not (mm, tmp_y, tmp_not_y, res_d_x, res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress =
          made_progress (tmp_y, 0, tmp_not_y, 0, *res_d_x, 0, *res_d_z, 0);
    }
    btor_bvprop_free (mm, tmp_y);
    btor_bvprop_free (mm, tmp_not_y);
    tmp_y     = *res_d_x;
    tmp_not_y = *res_d_z;

    /* (add_1, cout_1) = not_y + 1 */
    if (!bvprop_add_aux (mm,
                         tmp_not_y,
                         d_one,
                         tmp_add_1,
                         tmp_cout_1,
                         res_d_x,
                         res_d_y,
                         res_d_z,
                         &res_d_cout,
                         false))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_y);
      btor_bvprop_free (mm, *res_d_z);
      btor_bvprop_free (mm, res_d_cout);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_y));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    assert (btor_bvprop_is_valid (mm, res_d_cout));
    assert (!btor_bv_compare (d_one->lo, (*res_d_y)->lo));
    assert (!btor_bv_compare (d_one->hi, (*res_d_y)->hi));
    if (!progress)
    {
      progress = made_progress (tmp_not_y,
                                d_one,
                                tmp_add_1,
                                tmp_cout_1,
                                *res_d_x,
                                *res_d_y,
                                *res_d_z,
                                res_d_cout);
    }
    btor_bvprop_free (mm, tmp_not_y);
    btor_bvprop_free (mm, tmp_add_1);
    btor_bvprop_free (mm, tmp_cout_1);
    tmp_not_y = *res_d_x;
    btor_bvprop_free (mm, *res_d_y);
    tmp_add_1  = *res_d_z;
    tmp_cout_1 = res_d_cout;

    /* (add_2, cout_2) = x + add_1 */
    if (!bvprop_add_aux (mm,
                         tmp_x,
                         tmp_add_1,
                         tmp_add_2,
                         tmp_cout_2,
                         res_d_x,
                         res_d_y,
                         res_d_z,
                         &res_d_cout,
                         false))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_y);
      btor_bvprop_free (mm, *res_d_z);
      btor_bvprop_free (mm, res_d_cout);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_y));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    assert (btor_bvprop_is_valid (mm, res_d_cout));
    if (!progress)
    {
      progress = made_progress (tmp_x,
                                tmp_add_1,
                                tmp_add_2,
                                tmp_cout_2,
                                *res_d_x,
                                *res_d_y,
                                *res_d_z,
                                res_d_cout);
    }
    btor_bvprop_free (mm, tmp_x);
    btor_bvprop_free (mm, tmp_add_1);
    btor_bvprop_free (mm, tmp_add_2);
    btor_bvprop_free (mm, tmp_cout_2);
    tmp_x      = *res_d_x;
    tmp_add_1  = *res_d_y;
    tmp_add_2  = *res_d_z;
    tmp_cout_2 = res_d_cout;

    /* cout_msb_1 = cout(add_1)[MSB:MSB] */
    if (!btor_bvprop_slice (
            mm, tmp_cout_1, tmp_cout_msb_1, bw - 1, bw - 1, res_d_x, res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress (
          tmp_cout_1, 0, tmp_cout_msb_1, 0, *res_d_x, 0, *res_d_z, 0);
    }
    btor_bvprop_free (mm, tmp_cout_1);
    btor_bvprop_free (mm, tmp_cout_msb_1);
    tmp_cout_1     = *res_d_x;
    tmp_cout_msb_1 = *res_d_z;

    /* cout_msb_2 = cout(add_2))[MSB:MSB] */
    if (!btor_bvprop_slice (
            mm, tmp_cout_2, tmp_cout_msb_2, bw - 1, bw - 1, res_d_x, res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress (
          tmp_cout_2, 0, tmp_cout_msb_2, 0, *res_d_x, 0, *res_d_z, 0);
    }
    btor_bvprop_free (mm, tmp_cout_2);
    btor_bvprop_free (mm, tmp_cout_msb_2);
    tmp_cout_2     = *res_d_x;
    tmp_cout_msb_2 = *res_d_z;

    /* cout_msb = cout_msb_1 | cout_msb_2 */
    if (!btor_bvprop_or (mm,
                         tmp_cout_msb_1,
                         tmp_cout_msb_2,
                         tmp_cout_msb,
                         res_d_x,
                         res_d_y,
                         res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_y);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_y));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress = made_progress (tmp_cout_msb_1,
                                tmp_cout_msb_2,
                                tmp_cout_msb,
                                0,
                                *res_d_x,
                                *res_d_y,
                                *res_d_z,
                                0);
    }
    btor_bvprop_free (mm, tmp_cout_msb_1);
    btor_bvprop_free (mm, tmp_cout_msb_2);
    btor_bvprop_free (mm, tmp_cout_msb);
    tmp_cout_msb_1 = *res_d_x;
    tmp_cout_msb_2 = *res_d_y;
    tmp_cout_msb   = *res_d_z;

    /* z = ~cout_msb */
    if (!btor_bvprop_not (mm, tmp_cout_msb, tmp_z, res_d_x, res_d_z))
    {
      res = false;
      btor_bvprop_free (mm, *res_d_x);
      btor_bvprop_free (mm, *res_d_z);
      goto DONE;
    }
    assert (btor_bvprop_is_valid (mm, *res_d_x));
    assert (btor_bvprop_is_valid (mm, *res_d_z));
    if (!progress)
    {
      progress =
          made_progress (tmp_cout_msb, 0, tmp_z, 0, *res_d_x, 0, *res_d_z, 0);
    }
    btor_bvprop_free (mm, tmp_cout_msb);
    btor_bvprop_free (mm, tmp_z);
    tmp_cout_msb = *res_d_x;
    tmp_z        = *res_d_z;
  } while (progress);

  assert (btor_bvprop_is_valid (mm, tmp_x));
  assert (btor_bvprop_is_valid (mm, tmp_y));
  assert (btor_bvprop_is_valid (mm, tmp_z));

DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  btor_bvprop_free (mm, tmp_not_y);
  btor_bvprop_free (mm, tmp_add_1);
  btor_bvprop_free (mm, tmp_add_2);
  btor_bvprop_free (mm, tmp_cout_1);
  btor_bvprop_free (mm, tmp_cout_2);
  btor_bvprop_free (mm, tmp_cout_msb);
  btor_bvprop_free (mm, tmp_cout_msb_1);
  btor_bvprop_free (mm, tmp_cout_msb_2);
  btor_bvprop_free (mm, d_one);
  btor_bv_free (mm, one);

  return res;
}
