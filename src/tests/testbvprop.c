/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testbvprop.h"

#include "boolector.h"
#include "btorbv.h"
#include "btorbvprop.h"
#include "testrunner.h"
#include "utils/btormem.h"
#include "utils/btorutil.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

/*------------------------------------------------------------------------*/

static BtorMemMgr *g_mm;

/*------------------------------------------------------------------------*/

#define TEST_BVPROP_RELEASE_D_XZ  \
  do                              \
  {                               \
    btor_bvprop_free (g_mm, d_x); \
    btor_bvprop_free (g_mm, d_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_RES_XZ  \
  do                                \
  {                                 \
    btor_bvprop_free (g_mm, res_x); \
    btor_bvprop_free (g_mm, res_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_D_XYZ \
  do                              \
  {                               \
    btor_bvprop_free (g_mm, d_x); \
    btor_bvprop_free (g_mm, d_y); \
    btor_bvprop_free (g_mm, d_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_RES_XYZ \
  do                                \
  {                                 \
    btor_bvprop_free (g_mm, res_x); \
    btor_bvprop_free (g_mm, res_y); \
    btor_bvprop_free (g_mm, res_z); \
  } while (0)

/*------------------------------------------------------------------------*/

/* Initialize all possible values for 3-valued constants of bit-width bw */
uint32_t
generate_consts (uint32_t bw, char ***res)
{
  assert (bw);
  assert (res);

  uint32_t psize, num_consts = 1;
  char bit = '0';

  for (uint32_t i = 0; i < bw; i++) num_consts *= 3;
  psize = num_consts;

  BTOR_NEWN (g_mm, *res, num_consts);
  for (uint32_t i = 0; i < num_consts; i++)
    BTOR_CNEWN (g_mm, (*res)[i], bw + 1);

  for (uint32_t i = 0; i < bw; i++)
  {
    psize = psize / 3;
    for (uint32_t j = 0; j < num_consts; j++)
    {
      (*res)[j][i] = bit;
      if ((j + 1) % psize == 0)
      {
        bit = bit == '0' ? '1' : (bit == '1' ? 'x' : '0');
      }
    }
  }
  return num_consts;
}

void
free_consts (uint32_t bw, uint32_t num_consts, char **consts)
{
  assert (bw);
  assert (consts);
  for (uint32_t i = 0; i < num_consts; i++)
    BTOR_DELETEN (g_mm, consts[i], bw + 1);
  BTOR_DELETEN (g_mm, consts, num_consts);
}

/*------------------------------------------------------------------------*/

void
init_bvprop_tests (void)
{
  g_mm = btor_mem_mgr_new ();
}

char *
slice_str_const (char *str_const, uint32_t from, uint32_t to)
{
  char *res;
  uint32_t len = to - from + 1;

  BTOR_CNEWN (g_mm, res, len + 1);
  strncpy (res, str_const + from, len);
  return res;
}

void
to_str (BtorBvDomain *d, char **res_lo, char **res_hi, bool print_short)
{
  assert (d);
  assert (d->lo->width == d->hi->width);

  if (print_short)
  {
    assert (res_lo);
    char *lo = btor_bv_to_char (g_mm, d->lo);
    char *hi = btor_bv_to_char (g_mm, d->hi);
    for (size_t i = 0, len = strlen (lo); i < len; i++)
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
    btor_mem_freestr (g_mm, hi);
    *res_lo = lo;
    if (res_hi) *res_hi = 0;
  }
  else
  {
    assert (res_hi);
    *res_lo = btor_bv_to_char (g_mm, d->lo);
    *res_hi = btor_bv_to_char (g_mm, d->hi);
  }
}

static void
print_domain (BtorBvDomain *d, bool print_short)
{
  char *lo, *hi;

  to_str (d, &lo, &hi, print_short);

  if (print_short)
  {
    printf ("%s\n", lo);
  }
  else
  {
    printf ("lo: %s\n", lo);
    printf ("hi: %s\n", hi);
    btor_mem_freestr (g_mm, hi);
  }
  btor_mem_freestr (g_mm, lo);
}

/* Create 2-valued bit-vector from 3-valued bit-vector 'bv' by initializing
 * 'x' values to 'bit'. */
static BtorBitVector *
to_bv (const char *c, char bit)
{
  size_t len = strlen (c);
  char buf[len + 1];
  buf[len] = '\0';
  for (size_t i = 0; i < len; i++)
  {
    buf[i] = (c[i] == 'x') ? bit : c[i];
  }
  return btor_bv_char_to_bv (g_mm, buf);
}

/* Create hi for domain from 3-valued bit-vector 'bv'. */
static BtorBitVector *
to_hi (const char *bv)
{
  return to_bv (bv, '1');
}

/* Create lo for domain from 3-valued bit-vector 'bv'. */
static BtorBitVector *
to_lo (const char *bv)
{
  return to_bv (bv, '0');
}

/* Create domain from 3-valued bit-vector 'bv'. */
static BtorBvDomain *
create_domain (const char *bv)
{
  BtorBitVector *lo = to_lo (bv);
  BtorBitVector *hi = to_hi (bv);
  BtorBvDomain *res = btor_bvprop_new (g_mm, lo, hi);
  btor_bv_free (g_mm, lo);
  btor_bv_free (g_mm, hi);
  return res;
}

/* Create 3-valued bit-vector from domain 'd'. */
static char *
from_domain (BtorMemMgr *mm, BtorBvDomain *d)
{
  assert (btor_bvprop_is_valid (mm, d));
  char *lo = btor_bv_to_char (mm, d->lo);
  char *hi = btor_bv_to_char (mm, d->hi);

  size_t len = strlen (lo);
  for (size_t i = 0; i < len; i++)
  {
    if (lo[i] != hi[i])
    {
      /* lo[i] == '1' && hi[i] == '0' would be an invalid domain. */
      assert (lo[i] == '0');
      assert (hi[i] == '1');
      lo[i] = 'x';
    }
  }
  btor_mem_freestr (mm, hi);
  return lo;
}

static bool
is_xxx_domain (BtorMemMgr *mm, BtorBvDomain *d)
{
  assert (mm);
  assert (d);
  char *str_d = from_domain (mm, d);
  bool res    = strchr (str_d, '1') == NULL && strchr (str_d, '0') == NULL;
  btor_mem_freestr (mm, str_d);
  return res;
}

static bool
is_valid (BtorMemMgr *mm,
          BtorBvDomain *d_x,
          BtorBvDomain *d_y,
          BtorBvDomain *d_z,
          BtorBvDomain *d_c)
{
  return (!d_x || btor_bvprop_is_valid (mm, d_x))
         && (!d_y || btor_bvprop_is_valid (mm, d_y))
         && (!d_z || btor_bvprop_is_valid (mm, d_z))
         && (!d_c || btor_bvprop_is_valid (mm, d_c));
}

static bool
is_fixed (BtorMemMgr *mm,
          BtorBvDomain *d_x,
          BtorBvDomain *d_y,
          BtorBvDomain *d_z,
          BtorBvDomain *d_c)
{
  return (!d_x || btor_bvprop_is_fixed (mm, d_x))
         && (!d_y || btor_bvprop_is_fixed (mm, d_y))
         && (!d_z || btor_bvprop_is_fixed (mm, d_z))
         && (!d_c || btor_bvprop_is_fixed (mm, d_c));
}

static bool
is_false_eq (const char *a, const char *b)
{
  assert (strlen (a) == strlen (b));
  size_t len = strlen (a);
  for (size_t i = 0; i < len; i++)
  {
    if (a[i] == 'x' || b[i] == 'x')
    {
      continue;
    }
    if (a[i] != b[i])
    {
      return true;
    }
  }
  return false;
}

static bool
is_true_eq (const char *a, const char *b)
{
  assert (strlen (a) == strlen (b));
  size_t len = strlen (a);
  for (size_t i = 0; i < len; i++)
  {
    if (a[i] == 'x' && b[i] == 'x')
    {
      return false;
    }
    if (a[i] != 'x' && b[i] != 'x')
    {
      if (a[i] != b[i])
      {
        return false;
      }
    }
  }
  return true;
}

static void
check_not (BtorBvDomain *d_x, BtorBvDomain *d_z)
{
  char *str_x = from_domain (g_mm, d_x);
  char *str_z = from_domain (g_mm, d_z);
  assert (strlen (str_x) == strlen (str_z));

  size_t len = strlen (str_x);
  for (size_t i = 0; i < len; i++)
  {
    assert (str_x[i] != 'x' || str_z[i] == 'x');
    assert (str_x[i] != '0' || str_z[i] == '1');
    assert (str_x[i] != '1' || str_z[i] == '0');
    assert (str_z[i] != '0' || str_x[i] == '1');
    assert (str_z[i] != '1' || str_x[i] == '0');
  }
  btor_mem_freestr (g_mm, str_x);
  btor_mem_freestr (g_mm, str_z);
}

static bool
check_const_bits (BtorBvDomain *d, const char *expected)
{
  assert (btor_bvprop_is_valid (g_mm, d));
  size_t len = strlen (expected);
  uint32_t bit_lo, bit_hi;
  bool res = true;

  for (size_t i = 0; i < len && res; i++)
  {
    bit_lo = btor_bv_get_bit (d->lo, len - 1 - i);
    bit_hi = btor_bv_get_bit (d->hi, len - 1 - i);
    if (expected[i] == 'x')
    {
      res &= bit_lo != bit_hi;
    }
    else
    {
      res &= bit_lo == bit_hi;
    }
  }
  return res;
}

static void
check_sll_const (BtorBvDomain *d_x, BtorBvDomain *d_z, uint32_t n)
{
  if (btor_bvprop_is_valid (g_mm, d_x) && btor_bvprop_is_valid (g_mm, d_z))
  {
    size_t i, len;
    char *str_x = from_domain (g_mm, d_x);
    char *str_z = from_domain (g_mm, d_z);
    assert (strlen (str_x) == strlen (str_z));

    for (i = 0, len = strlen (str_x); i < len; i++)
    {
      assert (i >= n || str_z[len - 1 - i] == '0');
      assert (i < n || str_z[len - 1 - i] == str_x[len - 1 - i + n]);
    }
    btor_mem_freestr (g_mm, str_x);
    btor_mem_freestr (g_mm, str_z);
  }
}

static void
check_srl_const (BtorBvDomain *d_x, BtorBvDomain *d_z, uint32_t n)
{
  if (btor_bvprop_is_valid (g_mm, d_x) && btor_bvprop_is_valid (g_mm, d_z))
  {
    size_t i, len;
    char *str_x = from_domain (g_mm, d_x);
    char *str_z = from_domain (g_mm, d_z);
    assert (strlen (str_x) == strlen (str_z));

    for (i = 0, len = strlen (str_x); i < len; i++)
    {
      assert (i >= n || str_z[i] == '0');
      assert (i < n || str_z[i] == str_x[i - n]);
    }
    btor_mem_freestr (g_mm, str_x);
    btor_mem_freestr (g_mm, str_z);
  }
}

static void
check_concat (BtorBvDomain *d_x, BtorBvDomain *d_y, BtorBvDomain *d_z)
{
  size_t i, len_x, len_y;
  char *str_x = from_domain (g_mm, d_x);
  char *str_y = from_domain (g_mm, d_y);
  char *str_z = from_domain (g_mm, d_z);
  assert (strlen (str_x) + strlen (str_y) == strlen (str_z));

  for (i = 0, len_x = strlen (str_x); i < len_x; i++)
  {
    assert (str_x[i] == str_z[i]);
  }
  for (i = 0, len_y = strlen (str_y); i < len_y; i++)
  {
    assert (str_y[i] == str_z[i + len_x]);
  }
  btor_mem_freestr (g_mm, str_x);
  btor_mem_freestr (g_mm, str_y);
  btor_mem_freestr (g_mm, str_z);
}

static void
check_sext (BtorBvDomain *d_x, BtorBvDomain *d_z)
{
  if (btor_bvprop_is_valid (g_mm, d_x) && btor_bvprop_is_valid (g_mm, d_z))
  {
    size_t i, len_x, len_z, n;
    char *str_x = from_domain (g_mm, d_x);
    char *str_z = from_domain (g_mm, d_z);

    len_x = strlen (str_x);
    len_z = strlen (str_z);
    n     = len_z - len_x;

    for (i = 0; i < n; i++) assert (str_z[i] == str_x[0]);
    for (i = 0; i < len_x; i++) assert (str_z[i + n] == str_x[i]);

    btor_mem_freestr (g_mm, str_x);
    btor_mem_freestr (g_mm, str_z);
  }
}

static void
check_ite (BtorBvDomain *d_x,
           BtorBvDomain *d_y,
           BtorBvDomain *d_z,
           BtorBvDomain *d_c)
{
  assert (d_c->lo->width == 1);
  assert (d_c->hi->width == 1);
  assert (btor_bvprop_is_valid (g_mm, d_x));
  assert (btor_bvprop_is_valid (g_mm, d_y));
  assert (btor_bvprop_is_valid (g_mm, d_z));
  assert (btor_bvprop_is_valid (g_mm, d_c));

  char *str_x = from_domain (g_mm, d_x);
  char *str_y = from_domain (g_mm, d_y);
  char *str_z = from_domain (g_mm, d_z);
  char *str_c = from_domain (g_mm, d_c);

  if (str_c[0] == '0')
  {
    assert (!strcmp (str_z, str_y));
  }
  else if (str_c[0] == '1')
  {
    assert (!strcmp (str_z, str_x));
  }
  else
  {
    size_t len = strlen (str_x);
    assert (len == strlen (str_y));
    assert (len == strlen (str_z));

    if (strcmp (str_z, str_x) && strcmp (str_z, str_y))
    {
      for (size_t i = 0; i < len; i++)
      {
        assert (
            (str_z[i] == str_x[i] || str_z[i] == 'x' || str_x[i] == 'x')
            && (str_z[i] == str_y[i] || str_z[i] == 'x' || str_y[i] == 'x'));
      }
    }
  }

  btor_mem_freestr (g_mm, str_x);
  btor_mem_freestr (g_mm, str_y);
  btor_mem_freestr (g_mm, str_z);
  btor_mem_freestr (g_mm, str_c);
}

static void
check_sat (BtorBvDomain *d_x,
           BtorBvDomain *d_y,
           BtorBvDomain *d_z,
           BtorBvDomain *d_c,
           BtorBvDomain *res_x,
           BtorBvDomain *res_y,
           BtorBvDomain *res_z,
           BtorBvDomain *res_c,
           BoolectorNode *(*unfun) (Btor *, BoolectorNode *),
           BoolectorNode *(*binfun) (Btor *, BoolectorNode *, BoolectorNode *),
           BoolectorNode *(*binofun) (Btor *, BoolectorNode *, BoolectorNode *),
           BoolectorNode *(*extfun) (Btor *, BoolectorNode *, uint32_t),
           uint32_t hi,
           uint32_t lo,
           bool decompositional,
           bool valid)
{
  assert (d_x);
  assert (d_z);
  assert (res_x);
  assert (res_z);
  assert (!d_c || (!unfun && !binfun && !extfun));
  assert (!d_y || d_c || binfun || extfun);
  assert (!extfun || hi);
  assert (!binofun || binfun);

  int32_t sat_res;
  uint32_t i, bwx, bwy, bwz, idx;
  char *str_x, *str_y, *str_z, *str_c;
  Btor *btor;
  BoolectorNode *x, *y, *z, *c, *fun, *ofun, *not, *eq, *slice, *one, *zero;
  BoolectorSort swx, swy, swz, s1;

  str_x = from_domain (g_mm, d_x);
  str_y = 0;
  str_z = from_domain (g_mm, d_z);
  str_c = 0;

  btor = boolector_new ();
  boolector_set_opt (btor, BTOR_OPT_MODEL_GEN, 1);
  bwx  = d_x->lo->width;
  swx  = boolector_bitvec_sort (btor, bwx);
  bwz  = d_z->lo->width;
  swz  = boolector_bitvec_sort (btor, bwz);
  s1   = boolector_bitvec_sort (btor, 1);
  one  = boolector_one (btor, s1);
  zero = boolector_zero (btor, s1);
  x    = boolector_var (btor, swx, "x");
  z    = boolector_var (btor, swz, "z");
  y    = 0;
  c    = 0;

  if (d_y)
  {
    str_y = from_domain (g_mm, d_y);
    bwy   = d_y->lo->width;
    swy   = boolector_bitvec_sort (btor, bwy);
    y     = boolector_var (btor, swy, "y");
  }

  if (d_c)
  {
    assert (y);
    str_c = from_domain (g_mm, d_c);
    c     = boolector_var (btor, s1, "c");
    fun   = boolector_cond (btor, c, x, y);
  }
  else if (unfun)
  {
    assert (!binfun && !extfun);
    fun = unfun (btor, x);
  }
  else if (binfun)
  {
    assert (y);
    assert (!unfun && !extfun);
    fun = binfun (btor, x, y);
    if (binofun)
    {
      ofun = binofun (btor, x, y);
      not  = boolector_not (btor, ofun);
      boolector_assert (btor, not);
      boolector_release (btor, not);
      boolector_release (btor, ofun);
    }
  }
  else if (extfun)
  {
    assert (!unfun && !binfun);
    fun = extfun (btor, x, hi);
  }
  else
  {
    fun = boolector_slice (btor, x, hi, lo);
  }
  eq = boolector_eq (btor, fun, z);
  boolector_assert (btor, eq);
  boolector_release (btor, fun);
  boolector_release (btor, eq);

  for (i = 0; i < bwx; i++)
  {
    idx = bwx - i - 1;
    if (str_x[i] != 'x')
    {
      slice = boolector_slice (btor, x, idx, idx);
      eq    = boolector_eq (btor, slice, str_x[i] == '1' ? one : zero);
      boolector_assert (btor, eq);
      boolector_release (btor, eq);
      boolector_release (btor, slice);
    }
  }
  if (str_y)
  {
    for (i = 0; i < bwy; i++)
    {
      idx = bwy - i - 1;
      if (str_y[i] != 'x')
      {
        slice = boolector_slice (btor, y, idx, idx);
        eq    = boolector_eq (btor, slice, str_y[i] == '1' ? one : zero);
        boolector_assert (btor, eq);
        boolector_release (btor, eq);
        boolector_release (btor, slice);
      }
    }
  }
  for (i = 0; i < bwz; i++)
  {
    idx = bwz - i - 1;
    if (str_z[i] != 'x')
    {
      slice = boolector_slice (btor, z, idx, idx);
      eq    = boolector_eq (btor, slice, str_z[i] == '1' ? one : zero);
      boolector_assert (btor, eq);
      boolector_release (btor, eq);
      boolector_release (btor, slice);
    }
  }
  if (str_c)
  {
    if (str_c[0] != 'x')
    {
      eq = boolector_eq (btor, c, str_c[0] == '1' ? one : zero);
      boolector_assert (btor, eq);
      boolector_release (btor, eq);
    }
  }

  // boolector_dump_smt2 (btor, stdout);
  sat_res = boolector_sat (btor);
  assert (sat_res != BTOR_RESULT_SAT
          || (valid && is_valid (g_mm, res_x, res_y, res_z, res_c)));
  assert (sat_res != BTOR_RESULT_UNSAT
          || ((decompositional
               || (!valid && !is_valid (g_mm, res_x, res_y, res_z, res_c)))
              && (!decompositional || !valid
                  || !is_fixed (g_mm, res_x, res_y, res_z, res_c))));

  // printf ("sat_res %d\n", sat_res);
  // if (sat_res == BOOLECTOR_SAT)
  //{
  //  boolector_print_model (btor, "btor", stdout);
  //}

  boolector_release (btor, x);
  if (c) boolector_release (btor, c);
  if (y) boolector_release (btor, y);
  boolector_release (btor, z);
  boolector_release (btor, one);
  boolector_release (btor, zero);
  boolector_release_sort (btor, swx);
  if (y) boolector_release_sort (btor, swy);
  boolector_release_sort (btor, swz);
  boolector_release_sort (btor, s1);
  boolector_delete (btor);
  btor_mem_freestr (g_mm, str_x);
  if (str_c) btor_mem_freestr (g_mm, str_c);
  if (str_y) btor_mem_freestr (g_mm, str_y);
  btor_mem_freestr (g_mm, str_z);
}

/*------------------------------------------------------------------------*/

void
test_valid_domain_bvprop ()
{
  BtorBitVector *lo, *hi;
  BtorBvDomain *d;

  /* check valid */
  lo = btor_bv_char_to_bv (g_mm, "0101011");
  hi = btor_bv_char_to_bv (g_mm, "1101011");
  d  = btor_bvprop_new (g_mm, lo, hi);

  assert (btor_bvprop_is_valid (g_mm, d));
  btor_bv_free (g_mm, lo);
  btor_bv_free (g_mm, hi);
  btor_bvprop_free (g_mm, d);

  /* check invalid */
  lo = btor_bv_char_to_bv (g_mm, "1101011");
  hi = btor_bv_char_to_bv (g_mm, "0101011");
  d  = btor_bvprop_new (g_mm, lo, hi);

  assert (!btor_bvprop_is_valid (g_mm, d));
  btor_bv_free (g_mm, lo);
  btor_bv_free (g_mm, hi);
  btor_bvprop_free (g_mm, d);
}

void
test_fixed_domain_bvprop ()
{
  BtorBitVector *lo, *hi;
  BtorBvDomain *d;

  /* check fixed */
  lo = btor_bv_char_to_bv (g_mm, "0001111");
  hi = btor_bv_char_to_bv (g_mm, "0001111");
  d  = btor_bvprop_new (g_mm, lo, hi);

  assert (btor_bvprop_is_fixed (g_mm, d));
  btor_bv_free (g_mm, lo);
  btor_bv_free (g_mm, hi);
  btor_bvprop_free (g_mm, d);

  /* check not fixed */
  lo = btor_bv_char_to_bv (g_mm, "0001111");
  hi = btor_bv_char_to_bv (g_mm, "0001011");
  d  = btor_bvprop_new (g_mm, lo, hi);

  assert (!btor_bvprop_is_fixed (g_mm, d));
  btor_bv_free (g_mm, lo);
  btor_bv_free (g_mm, hi);
  btor_bvprop_free (g_mm, d);
}

void
test_new_init_domain_bvprop ()
{
  BtorBvDomain *d = btor_bvprop_new_init (g_mm, 32);
  assert (btor_bvprop_is_valid (g_mm, d));
  assert (!btor_bvprop_is_fixed (g_mm, d));
  btor_bvprop_free (g_mm, d);
}

void
eq_bvprop (uint32_t bw)
{
  bool res;
  char **consts;
  uint32_t num_consts;
  const char *values_z[] = {"x", "0", "1"};
  BtorBvDomain *d_x, *d_y, *d_z, *res_x, *res_y, *res_z;

  num_consts = generate_consts (bw, &consts);

  for (size_t k = 0; k < 3; k++)
  {
    d_z = create_domain (values_z[k]);
    for (size_t i = 0; i < num_consts; i++)
    {
      d_x = create_domain (consts[i]);
      for (size_t j = 0; j < num_consts; j++)
      {
        d_y = create_domain (consts[j]);
        res = btor_bvprop_eq (g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);

        check_sat (d_x,
                   d_y,
                   d_z,
                   0,
                   res_x,
                   res_y,
                   res_z,
                   0,
                   0,
                   boolector_eq,
                   0,
                   0,
                   0,
                   0,
                   true,
                   res);

        btor_bvprop_free (g_mm, d_y);
        btor_bvprop_free (g_mm, res_x);
        btor_bvprop_free (g_mm, res_y);
        btor_bvprop_free (g_mm, res_z);
      }
      btor_bvprop_free (g_mm, d_x);
    }
    btor_bvprop_free (g_mm, d_z);
  }
  free_consts (bw, num_consts, consts);
}

void
not_bvprop (uint32_t bw)
{
  bool res;
  uint32_t num_consts;
  char **consts;
  BtorBvDomain *d_x, *d_z, *res_x, *res_z;

  num_consts = generate_consts (bw, &consts);

  for (uint32_t i = 0; i < num_consts; i++)
  {
    d_x = create_domain (consts[i]);

    for (uint32_t j = 0; j < num_consts; j++)
    {
      d_z = create_domain (consts[j]);
      res = btor_bvprop_not (g_mm, d_x, d_z, &res_x, &res_z);
      check_sat (d_x,
                 0,
                 d_z,
                 0,
                 res_x,
                 0,
                 res_z,
                 0,
                 boolector_not,
                 0,
                 0,
                 0,
                 0,
                 0,
                 false,
                 res);

      if (btor_bvprop_is_valid (g_mm, res_z))
      {
        assert (res);
        assert (!btor_bvprop_is_fixed (g_mm, d_x)
                || !btor_bv_compare (d_x->lo, res_x->lo));
        assert (!btor_bvprop_is_fixed (g_mm, d_z)
                || !btor_bv_compare (d_z->lo, res_z->lo));
        assert (btor_bvprop_is_valid (g_mm, res_x));
        assert (!btor_bvprop_is_fixed (g_mm, d_z)
                || (btor_bvprop_is_fixed (g_mm, res_x)
                    && btor_bvprop_is_fixed (g_mm, res_z)));
        check_not (res_x, res_z);
      }
      else
      {
        assert (!res);
        bool valid = true;
        for (uint32_t k = 0; k < bw && valid; k++)
        {
          if (consts[i][k] != 'x' && consts[i][k] == consts[j][k])
          {
            valid = false;
          }
        }
        assert (!valid);
      }
      btor_bvprop_free (g_mm, d_z);
      TEST_BVPROP_RELEASE_RES_XZ;
    }
    btor_bvprop_free (g_mm, d_x);
  }
  free_consts (bw, num_consts, consts);
}

static void
shift_const_bvprop_aux (uint32_t bw, bool is_srl)
{
  bool res;
  uint32_t i, j, n, num_consts;
  char **consts;
  BtorBitVector *bv_n;
  BtorBvDomain *d_x, *d_y, *d_z, *res_x, *res_z;

  num_consts = generate_consts (bw, &consts);

  for (i = 0; i < num_consts; i++)
  {
    d_z = create_domain (consts[i]);
    for (j = 0; j < num_consts; j++)
    {
      d_x = create_domain (consts[j]);

      for (n = 0; n < bw + 1; n++)
      {
        bv_n = btor_bv_uint64_to_bv (g_mm, n, bw);
        d_y  = btor_bvprop_new (g_mm, bv_n, bv_n);
        if (is_srl)
        {
          res = btor_bvprop_srl_const (g_mm, d_x, d_z, bv_n, &res_x, &res_z);
          check_sat (d_x,
                     d_y,
                     d_z,
                     0,
                     res_x,
                     0,
                     res_z,
                     0,
                     0,
                     boolector_srl,
                     0,
                     0,
                     0,
                     0,
                     false,
                     res);
        }
        else
        {
          res = btor_bvprop_sll_const (g_mm, d_x, d_z, bv_n, &res_x, &res_z);
          check_sat (d_x,
                     d_y,
                     d_z,
                     0,
                     res_x,
                     0,
                     res_z,
                     0,
                     0,
                     boolector_sll,
                     0,
                     0,
                     0,
                     0,
                     false,
                     res);
        }
        assert (res || !is_valid (g_mm, res_x, 0, res_z, 0));

        assert (!btor_bvprop_is_fixed (g_mm, d_x)
                || !btor_bvprop_is_valid (g_mm, res_x)
                || !btor_bv_compare (d_x->lo, res_x->lo));
        assert (!res || !btor_bvprop_is_fixed (g_mm, d_z)
                || !btor_bvprop_is_valid (g_mm, res_z)
                || !btor_bv_compare (d_z->lo, res_z->lo));
        if (is_srl)
          check_srl_const (res_x, res_z, n);
        else
          check_sll_const (res_x, res_z, n);

        TEST_BVPROP_RELEASE_RES_XZ;
        btor_bv_free (g_mm, bv_n);
        btor_bvprop_free (g_mm, d_y);
      }
      btor_bvprop_free (g_mm, d_x);
    }
    btor_bvprop_free (g_mm, d_z);
  }
  free_consts (bw, num_consts, consts);
}

void
sll_const_bvprop (uint32_t bw)
{
  shift_const_bvprop_aux (bw, false);
}

void
srl_const_bvprop (uint32_t bw)
{
  shift_const_bvprop_aux (bw, true);
}

static void
shift_bvprop_aux (uint32_t bw, bool is_srl)
{
  assert (btor_util_is_power_of_2 (bw));

  bool res;
  uint32_t i, j, k, num_consts, num_consts_shift, bw_shift;
  char **consts, **consts_shift;
  BtorBvDomain *d_x, *d_y, *d_z, *res_x, *res_y, *res_z;

  bw_shift         = btor_util_log_2 (bw);
  num_consts       = generate_consts (bw, &consts);
  num_consts_shift = generate_consts (bw_shift, &consts_shift);

  for (i = 0; i < num_consts; i++)
  {
    d_z = create_domain (consts[i]);
    for (j = 0; j < num_consts; j++)
    {
      d_x = create_domain (consts[j]);

      for (k = 0; k < num_consts_shift; k++)
      {
        d_y = create_domain (consts_shift[k]);
        if (is_srl)
        {
          res = btor_bvprop_srl (g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat (d_x,
                     d_y,
                     d_z,
                     0,
                     res_x,
                     res_y,
                     res_z,
                     0,
                     0,
                     boolector_srl,
                     0,
                     0,
                     0,
                     0,
                     true,
                     res);
        }
        else
        {
          res = btor_bvprop_sll (g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat (d_x,
                     d_y,
                     d_z,
                     0,
                     res_x,
                     res_y,
                     res_z,
                     0,
                     0,
                     boolector_sll,
                     0,
                     0,
                     0,
                     0,
                     true,
                     res);
        }

        assert (!btor_bvprop_is_fixed (g_mm, d_x)
                || !btor_bvprop_is_valid (g_mm, res_x)
                || !btor_bv_compare (d_x->lo, res_x->lo));
        assert (!btor_bvprop_is_fixed (g_mm, d_y)
                || !btor_bvprop_is_valid (g_mm, res_y)
                || !btor_bv_compare (d_y->lo, res_y->lo));
        assert (!res || !btor_bvprop_is_fixed (g_mm, d_z)
                || !btor_bvprop_is_valid (g_mm, res_z)
                || !btor_bv_compare (d_z->lo, res_z->lo));
        TEST_BVPROP_RELEASE_RES_XYZ;
        btor_bvprop_free (g_mm, d_y);
      }
      btor_bvprop_free (g_mm, d_x);
    }
    btor_bvprop_free (g_mm, d_z);
  }
  free_consts (bw, num_consts, consts);
  free_consts (bw_shift, num_consts_shift, consts_shift);
}

void
sll_bvprop (uint32_t bw)
{
  shift_bvprop_aux (bw, false);
}

void
srl_bvprop (uint32_t bw)
{
  shift_bvprop_aux (bw, true);
}

#define TEST_BVPROP_AND 0
#define TEST_BVPROP_OR 1
#define TEST_BVPROP_XOR 2

void
and_or_xor_bvprop_aux (int32_t op, uint32_t bw)
{
  bool res;
  uint32_t num_consts;
  char **consts, *str_z, *str_x, *str_y, *str_res_z, *str_res_x, *str_res_y;
  BtorBitVector *tmp;
  BtorBvDomain *d_x, *d_y, *d_z;
  BtorBvDomain *res_x, *res_y, *res_z;
  BoolectorNode *(*boolectorfun) (Btor *, BoolectorNode *, BoolectorNode *);
  BtorBitVector *(*bvfun) (
      BtorMemMgr *, const BtorBitVector *, const BtorBitVector *);
  bool (*bvpropfun) (BtorMemMgr *,
                     BtorBvDomain *,
                     BtorBvDomain *,
                     BtorBvDomain *,
                     BtorBvDomain **,
                     BtorBvDomain **,
                     BtorBvDomain **);

  num_consts = generate_consts (bw, &consts);

  for (uint32_t i = 0; i < num_consts; i++)
  {
    d_z = create_domain (consts[i]);
    str_z = consts[i];

    for (uint32_t j = 0; j < num_consts; j++)
    {
      d_x = create_domain (consts[j]);
      str_x = consts[j];

      for (uint32_t k = 0; k < num_consts; k++)
      {
        d_y = create_domain (consts[k]);
        str_y = consts[k];

        if (op == TEST_BVPROP_AND)
        {
          boolectorfun = boolector_and;
          bvpropfun    = btor_bvprop_and;
          bvfun        = btor_bv_and;
        }
        else if (op == TEST_BVPROP_OR)
        {
          boolectorfun = boolector_or;
          bvpropfun    = btor_bvprop_or;
          bvfun        = btor_bv_or;
        }
        else
        {
          assert (op == TEST_BVPROP_XOR);
          boolectorfun = boolector_xor;
          bvpropfun    = btor_bvprop_xor;
          bvfun        = btor_bv_xor;
        }

        res = bvpropfun (g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
        check_sat (d_x,
                   d_y,
                   d_z,
                   0,
                   res_x,
                   res_y,
                   res_z,
                   0,
                   0,
                   boolectorfun,
                   0,
                   0,
                   0,
                   0,
                   false,
                   res);

        to_str (res_x, &str_res_x, 0, true);
        to_str (res_y, &str_res_y, 0, true);
        to_str (res_z, &str_res_z, 0, true);

        assert (res || !is_valid (g_mm, res_x, res_y, res_z, 0));

        assert (!btor_bvprop_is_fixed (g_mm, d_x)
                || !btor_bvprop_is_valid (g_mm, res_x)
                || !btor_bv_compare (d_x->lo, res_x->lo));
        assert (!btor_bvprop_is_fixed (g_mm, d_y)
                || !btor_bvprop_is_valid (g_mm, res_y)
                || !btor_bv_compare (d_y->lo, res_y->lo));
        assert (!btor_bvprop_is_fixed (g_mm, d_z)
                || !btor_bvprop_is_valid (g_mm, res_z)
                || !btor_bv_compare (d_z->lo, res_z->lo));

        if (res && btor_bvprop_is_fixed (g_mm, d_x)
            && btor_bvprop_is_fixed (g_mm, d_y))
        {
          assert (btor_bvprop_is_fixed (g_mm, res_x));
          assert (btor_bvprop_is_fixed (g_mm, res_y));
          if (is_xxx_domain (g_mm, d_z))
          {
            tmp = bvfun (g_mm, res_x->lo, res_y->lo);
            assert (!btor_bv_compare (d_x->lo, res_x->lo));
            assert (!btor_bv_compare (d_y->lo, res_y->lo));
            assert (btor_bvprop_is_fixed (g_mm, res_z));
            assert (!btor_bv_compare (tmp, res_z->lo));
            btor_bv_free (g_mm, tmp);
          }
          else if (btor_bvprop_is_fixed (g_mm, d_z))
          {
            assert (btor_bvprop_is_fixed (g_mm, res_z));
            tmp = bvfun (g_mm, d_x->lo, d_y->lo);
            if (!btor_bv_compare (tmp, d_z->lo))
            {
              assert (!btor_bv_compare (d_x->lo, res_x->lo));
              assert (!btor_bv_compare (d_y->lo, res_y->lo));
              btor_bv_free (g_mm, tmp);
              tmp = bvfun (g_mm, res_x->lo, res_y->lo);
              assert (!btor_bv_compare (tmp, res_z->lo));
            }
            btor_bv_free (g_mm, tmp);
          }
        }

        if (btor_bvprop_is_valid (g_mm, res_z))
        {
          assert (btor_bvprop_is_valid (g_mm, res_x));
          assert (btor_bvprop_is_valid (g_mm, res_y));

          for (uint32_t l = 0; l < bw; l++)
          {
            if (op == TEST_BVPROP_AND)
            {
              assert (str_z[l] != '1' || (str_x[l] != '0' && str_y[l] != '0'));
              assert (str_z[l] != '0' || (str_x[l] != '1' || str_y[l] != '1'));

              assert (str_z[l] != '1' || str_x[l] != '1'
                      || str_res_y[l] == '1');
              assert (str_z[l] != '1' || str_y[l] != '1'
                      || str_res_x[l] == '1');
              assert (str_z[l] != '0' || str_x[l] != '1'
                      || str_res_y[l] == '0');
              assert (str_z[l] != '0' || str_y[l] != '1'
                      || str_res_x[l] == '0');
            }
            else if (op == TEST_BVPROP_OR)
            {
              assert (str_z[l] != '1' || str_x[l] != '0' || str_y[l] != '0');
              assert (str_z[l] != '0' || (str_x[l] != '1' && str_y[l] != '1'));

              assert (str_z[l] != '0' || str_x[l] != '0'
                      || str_res_y[l] == '0');
              assert (str_z[l] != '0' || str_y[l] != '0'
                      || str_res_x[l] == '0');
              assert (str_z[l] != '1' || str_x[l] != '0'
                      || str_res_y[l] == '1');
              assert (str_z[l] != '1' || str_y[l] != '0'
                      || str_res_x[l] == '1');
            }
            else
            {
              assert (op == TEST_BVPROP_XOR);
              assert (str_z[l] != '1' || (str_x[l] != '0' || str_y[l] != '0')
                      || (str_x[l] != '1' || str_y[l] != '1'));
              assert (str_z[l] != '0'
                      || ((str_x[l] != '0' || str_y[l] != '1')
                          && (str_x[l] != '1' || str_y[l] != '0')));

              assert (str_z[l] != '1' || str_x[l] != '1'
                      || str_res_y[l] == '0');
              assert (str_z[l] != '1' || str_y[l] != '1'
                      || str_res_x[l] == '0');
              assert (str_z[l] != '0' || str_x[l] != '0'
                      || str_res_y[l] == '0');
              assert (str_z[l] != '0' || str_y[l] != '0'
                      || str_res_x[l] == '0');
              assert (str_z[l] != '0' || str_x[l] != '1'
                      || str_res_y[l] == '1');
              assert (str_z[l] != '0' || str_y[l] != '1'
                      || str_res_x[l] == '1');
            }
          }
        }
        else
        {
          bool valid = true;
          for (uint32_t l = 0; l < bw && valid; l++)
          {
            if ((op == TEST_BVPROP_AND
                 && ((str_z[l] == '0' && str_x[l] != '0' && str_y[l] != '0')
                     || (str_z[l] == '1'
                         && (str_x[l] == '0' || str_y[l] == '0'))))
                || (op == TEST_BVPROP_OR
                    && ((str_z[l] == '1' && str_x[l] != '1' && str_y[l] != '1')
                        || (str_z[l] == '0'
                            && (str_x[l] == '1' || str_y[l] == '1'))))
                || (op == TEST_BVPROP_XOR
                    && ((str_z[l] == '1'
                         && ((str_x[l] != '0' && str_y[l] != '0')
                             || (str_x[l] != '1' && str_y[l] != '1')))
                        || (str_z[l] == '0'
                            && ((str_x[l] != '1' && str_y[l] != '0')
                                || (str_x[l] != '0' && str_y[l] != '1'))))))
            {
              valid = false;
            }
          }
          assert (!valid);
        }

        btor_mem_freestr (g_mm, str_res_x);
        btor_mem_freestr (g_mm, str_res_y);
        btor_mem_freestr (g_mm, str_res_z);

        btor_bvprop_free (g_mm, d_y);
        TEST_BVPROP_RELEASE_RES_XYZ;
      }
      btor_bvprop_free (g_mm, d_x);
    }
    btor_bvprop_free (g_mm, d_z);
  }
  free_consts (bw, num_consts, consts);
}

void
and_bvprop (uint32_t bw)
{
  and_or_xor_bvprop_aux (TEST_BVPROP_AND, bw);
}

void
or_bvprop (uint32_t bw)
{
  and_or_xor_bvprop_aux (TEST_BVPROP_OR, bw);
}

void
xor_bvprop (uint32_t bw)
{
  and_or_xor_bvprop_aux (TEST_BVPROP_XOR, bw);
}

void
slice_bvprop (uint32_t bw)
{
  bool res;
  uint32_t num_consts;
  char *buf, **consts;
  BtorBvDomain *d_x, *d_z, *res_x, *res_z;

  num_consts = generate_consts (bw, &consts);
  BTOR_CNEWN (g_mm, buf, bw + 1);

  for (uint32_t i = 0; i < num_consts; i++)
  {
    d_x = create_domain (consts[i]);
    for (uint32_t j = 0; j < num_consts; j++)
    {
      for (uint32_t lower = 0; lower < bw; lower++)
      {
        for (uint32_t upper = lower; upper < bw; upper++)
        {
          memset (buf, 0, bw + 1);
          memcpy (buf, &consts[j][bw - 1 - upper], upper - lower + 1);
          assert (strlen (buf) > 0);
          assert (strlen (buf) == upper - lower + 1);

          d_z = create_domain (buf);
          res =
              btor_bvprop_slice (g_mm, d_x, d_z, upper, lower, &res_x, &res_z);
          /* not compositional but eq always returns true */
          assert (res || !is_valid (g_mm, res_x, 0, res_z, 0));
          check_sat (d_x,
                     0,
                     d_z,
                     0,
                     res_x,
                     0,
                     res_z,
                     0,
                     0,
                     0,
                     0,
                     0,
                     upper,
                     lower,
                     false,
                     res);

          assert (!btor_bvprop_is_fixed (g_mm, d_x)
                  || !btor_bvprop_is_valid (g_mm, res_x)
                  || !btor_bv_compare (d_x->lo, res_x->lo));
          assert (!btor_bvprop_is_fixed (g_mm, d_z)
                  || !btor_bvprop_is_valid (g_mm, res_z)
                  || !btor_bv_compare (d_z->lo, res_z->lo));

          if (btor_bvprop_is_valid (g_mm, res_z))
          {
            assert (btor_bvprop_is_valid (g_mm, res_x));
            char *str_res_x = from_domain (g_mm, res_x);
            char *str_res_z = from_domain (g_mm, res_z);
            for (uint32_t k = 0; k < upper - lower + 1; k++)
            {
              assert (str_res_z[k] == str_res_x[bw - 1 - upper + k]);
            }
            btor_mem_freestr (g_mm, str_res_x);
            btor_mem_freestr (g_mm, str_res_z);
          }
          else
          {
            assert (!btor_bvprop_is_valid (g_mm, res_x));
            bool valid = true;
            for (uint32_t k = 0; k < bw; k++)
            {
              if (buf[k] != consts[i][bw - 1 - upper + k])
              {
                valid = false;
                break;
              }
            }
            assert (!valid);
          }
          btor_bvprop_free (g_mm, d_z);
          TEST_BVPROP_RELEASE_RES_XZ;
        }
      }
    }
    btor_bvprop_free (g_mm, d_x);
  }
  BTOR_DELETEN (g_mm, buf, bw + 1);
  free_consts (bw, num_consts, consts);
}

#define TEST_PROPBV_CONCAT                                                  \
  do                                                                        \
  {                                                                         \
    res = btor_bvprop_concat (g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z); \
    assert (res || !is_valid (g_mm, res_x, res_y, res_z, 0));               \
    check_sat (d_x,                                                         \
               d_y,                                                         \
               d_z,                                                         \
               0,                                                           \
               res_x,                                                       \
               res_y,                                                       \
               res_z,                                                       \
               0,                                                           \
               0,                                                           \
               boolector_concat,                                            \
               0,                                                           \
               0,                                                           \
               0,                                                           \
               0,                                                           \
               false, /* not compositional but eq always returns true */    \
               res);                                                        \
    assert (!btor_bvprop_is_fixed (g_mm, d_x)                               \
            || !btor_bv_compare (d_x->lo, res_x->lo));                      \
    assert (!btor_bvprop_is_fixed (g_mm, d_y)                               \
            || !btor_bv_compare (d_y->lo, res_y->lo));                      \
    assert (!btor_bvprop_is_fixed (g_mm, d_z)                               \
            || !btor_bv_compare (d_z->lo, res_z->lo));                      \
    check_concat (res_x, res_y, res_z);                                     \
    assert (btor_bvprop_is_valid (g_mm, res_x));                            \
    assert (btor_bvprop_is_valid (g_mm, res_y));                            \
    assert (btor_bvprop_is_valid (g_mm, res_z));                            \
    assert (!btor_bvprop_is_fixed (g_mm, d_x)                               \
            || btor_bvprop_is_fixed (g_mm, res_x));                         \
    assert (!btor_bvprop_is_fixed (g_mm, d_y)                               \
            || btor_bvprop_is_fixed (g_mm, res_y));                         \
    assert (!btor_bvprop_is_fixed (g_mm, d_z)                               \
            || (btor_bvprop_is_fixed (g_mm, res_x)                          \
                && btor_bvprop_is_fixed (g_mm, res_y)                       \
                && btor_bvprop_is_fixed (g_mm, res_z)));                    \
    TEST_BVPROP_RELEASE_D_XYZ;                                              \
    TEST_BVPROP_RELEASE_RES_XYZ;                                            \
  } while (0)

void
concat_bvprop (uint32_t bw)
{
  bool res;
  uint32_t i, j, k, num_consts;
  char *s_const, **consts;
  BtorBvDomain *d_x, *d_y, *d_z, *res_x, *res_y, *res_z;

  num_consts = generate_consts (bw, &consts);

  for (i = 1; i < bw; i++)
  {
    j = bw - i;
    for (k = 0; k < num_consts; k++)
    {
      d_x = btor_bvprop_new_init (g_mm, i);
      d_y = btor_bvprop_new_init (g_mm, j);
      assert (i + j == bw);
      d_z = btor_bvprop_new_init (g_mm, bw);
      TEST_PROPBV_CONCAT;

      s_const = slice_str_const (consts[k], 0, i - 1);
      d_x     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_y = btor_bvprop_new_init (g_mm, j);
      d_z = btor_bvprop_new_init (g_mm, bw);
      TEST_PROPBV_CONCAT;

      d_x     = btor_bvprop_new_init (g_mm, i);
      s_const = slice_str_const (consts[k], i, bw - 1);
      d_y     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_z = btor_bvprop_new_init (g_mm, bw);
      TEST_PROPBV_CONCAT;

      d_x = btor_bvprop_new_init (g_mm, i);
      d_y = btor_bvprop_new_init (g_mm, j);
      d_z = create_domain (consts[k]);
      TEST_PROPBV_CONCAT;

      s_const = slice_str_const (consts[k], 0, i - 1);
      d_x     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      s_const = slice_str_const (consts[k], i, bw - 1);
      d_y     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_z = btor_bvprop_new_init (g_mm, bw);
      TEST_PROPBV_CONCAT;

      s_const = slice_str_const (consts[k], 0, i - 1);
      d_x     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_y = btor_bvprop_new_init (g_mm, j);
      d_z = create_domain (consts[k]);
      TEST_PROPBV_CONCAT;

      d_x     = btor_bvprop_new_init (g_mm, i);
      s_const = slice_str_const (consts[k], i, bw - 1);
      d_y     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_z = create_domain (consts[k]);
      TEST_PROPBV_CONCAT;

      s_const = slice_str_const (consts[k], 0, i - 1);
      d_x     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      s_const = slice_str_const (consts[k], i, bw - 1);
      d_y     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_z = create_domain (consts[k]);
      TEST_PROPBV_CONCAT;
    }
  }
  free_consts (bw, num_consts, consts);
}

void
sext_bvprop (uint32_t bw)
{
  bool res;
  uint32_t n, i, j, num_consts;
  char **consts;
  BtorBvDomain *d_x, *d_z, *res_x, *res_z;

  num_consts = generate_consts (bw, &consts);

  for (i = 0; i < num_consts; i++)
  {
    d_z = create_domain (consts[i]);
    for (j = 0; j < num_consts; j++)
    {
      for (n = 1; n < bw; n++)
      {
        d_x = create_domain (consts[j] + n);
        res = btor_bvprop_sext (g_mm, d_x, d_z, &res_x, &res_z);
        check_sat (d_x,
                   0,
                   d_z,
                   0,
                   res_x,
                   0,
                   res_z,
                   0,
                   0,
                   0,
                   0,
                   boolector_sext,
                   n,
                   0,
                   false,
                   res);

        assert (!btor_bvprop_is_fixed (g_mm, d_x)
                || !btor_bvprop_is_valid (g_mm, res_x)
                || !btor_bv_compare (d_x->lo, res_x->lo));
        assert (!res || !btor_bvprop_is_fixed (g_mm, d_z)
                || !btor_bvprop_is_valid (g_mm, res_z)
                || !btor_bv_compare (d_z->lo, res_z->lo));
        check_sext (res_x, res_z);
        TEST_BVPROP_RELEASE_RES_XZ;
        btor_bvprop_free (g_mm, d_x);
      }
    }
    btor_bvprop_free (g_mm, d_z);
  }
  free_consts (bw, num_consts, consts);
}

void
ite_bvprop (uint32_t bw)
{
  bool res;
  uint32_t num_consts;
  char **consts;
  BtorBitVector *tmp;
  BtorBvDomain *d_c, *d_x, *d_y, *d_z;
  BtorBvDomain *res_c, *res_x, *res_y, *res_z;

  num_consts = generate_consts (bw, &consts);

  for (uint32_t c = 0; c < 3; c++)
  {
    if (c > 1)
    {
      d_c = btor_bvprop_new_init (g_mm, 1);
    }
    else
    {
      tmp = btor_bv_uint64_to_bv (g_mm, c, 1);
      d_c = btor_bvprop_new (g_mm, tmp, tmp);
      btor_bv_free (g_mm, tmp);
    }

    for (uint32_t i = 0; i < num_consts; i++)
    {
      d_z = create_domain (consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = create_domain (consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = create_domain (consts[k]);

          res = btor_bvprop_ite (
              g_mm, d_c, d_x, d_y, d_z, &res_c, &res_x, &res_y, &res_z);
          check_sat (d_x,
                     d_y,
                     d_z,
                     d_c,
                     res_x,
                     res_y,
                     res_z,
                     res_c,
                     0,
                     0,
                     0,
                     0,
                     0,
                     0,
                     false, /* we always get an invalid result if invalid */
                     res);
          if (res) check_ite (res_x, res_y, res_z, res_c);

          btor_bvprop_free (g_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
          btor_bvprop_free (g_mm, res_c);
        }
        btor_bvprop_free (g_mm, d_x);
      }
      btor_bvprop_free (g_mm, d_z);
    }
    btor_bvprop_free (g_mm, d_c);
  }
  free_consts (bw, num_consts, consts);
}

void
add_bvprop (uint32_t bw, bool no_overflows)
{
  bool res;
  uint32_t num_consts;
  char **consts;
  BtorBitVector *tmp;
  BtorBvDomain *d_x, *d_y, *d_z;
  BtorBvDomain *res_x, *res_y, *res_z;

  num_consts = generate_consts (bw, &consts);

  for (uint32_t i = 0; i < num_consts; i++)
  {
    d_z = create_domain (consts[i]);
    for (uint32_t j = 0; j < num_consts; j++)
    {
      d_x = create_domain (consts[j]);
      for (uint32_t k = 0; k < num_consts; k++)
      {
        d_y = create_domain (consts[k]);

        res = btor_bvprop_add_aux (
            g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z, no_overflows);
        check_sat (d_x,
                   d_y,
                   d_z,
                   0,
                   res_x,
                   res_y,
                   res_z,
                   0,
                   0,
                   boolector_add,
                   no_overflows ? boolector_uaddo : 0,
                   0,
                   0,
                   0,
                   true,
                   res);

        if (btor_bvprop_is_fixed (g_mm, d_x)
            && btor_bvprop_is_fixed (g_mm, d_y))
        {
          assert (btor_bvprop_is_fixed (g_mm, res_x));
          assert (btor_bvprop_is_fixed (g_mm, res_y));
          if (is_xxx_domain (g_mm, d_z))
          {
            tmp = btor_bv_add (g_mm, res_x->lo, res_y->lo);
            assert (!btor_bv_compare (d_x->lo, res_x->lo));
            assert (!btor_bv_compare (d_y->lo, res_y->lo));
            assert (no_overflows || btor_bvprop_is_fixed (g_mm, res_z));
            assert (!btor_bvprop_is_fixed (g_mm, res_z)
                    || !btor_bv_compare (tmp, res_z->lo));
            btor_bv_free (g_mm, tmp);
          }
          else if (btor_bvprop_is_fixed (g_mm, d_z))
          {
            assert (btor_bvprop_is_fixed (g_mm, res_z));
            tmp = btor_bv_add (g_mm, d_x->lo, d_y->lo);
            if (!btor_bv_compare (tmp, d_z->lo))
            {
              assert (!btor_bv_compare (d_x->lo, res_x->lo));
              assert (!btor_bv_compare (d_y->lo, res_y->lo));
              btor_bv_free (g_mm, tmp);
              tmp = btor_bv_add (g_mm, res_x->lo, res_y->lo);
              assert (!btor_bv_compare (tmp, res_z->lo));
            }
            btor_bv_free (g_mm, tmp);
          }
        }
        btor_bvprop_free (g_mm, d_y);
        TEST_BVPROP_RELEASE_RES_XYZ;
      }
      btor_bvprop_free (g_mm, d_x);
    }
    btor_bvprop_free (g_mm, d_z);
  }
  free_consts (bw, num_consts, consts);
}

void
mul_bvprop (uint32_t bw, bool no_overflows)
{
  bool res;
  uint32_t num_consts;
  char **consts;
  BtorBitVector *tmp;
  BtorBvDomain *d_x, *d_y, *d_z;
  BtorBvDomain *res_x, *res_y, *res_z;

  num_consts = generate_consts (bw, &consts);

  for (uint32_t i = 0; i < num_consts; i++)
  {
    d_z = create_domain (consts[i]);
    for (uint32_t j = 0; j < num_consts; j++)
    {
      d_x = create_domain (consts[j]);
      for (uint32_t k = 0; k < num_consts; k++)
      {
        d_y = create_domain (consts[k]);

        res = btor_bvprop_mul_aux (
            g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z, no_overflows);
        check_sat (d_x,
                   d_y,
                   d_z,
                   0,
                   res_x,
                   res_y,
                   res_z,
                   0,
                   0,
                   boolector_mul,
                   no_overflows ? boolector_umulo : 0,
                   0,
                   0,
                   0,
                   true,
                   res);

        if (btor_bvprop_is_fixed (g_mm, d_x)
            && btor_bvprop_is_fixed (g_mm, d_y))
        {
          assert (btor_bvprop_is_fixed (g_mm, res_x));
          assert (btor_bvprop_is_fixed (g_mm, res_y));
          if (is_xxx_domain (g_mm, d_z))
          {
            tmp = btor_bv_mul (g_mm, res_x->lo, res_y->lo);
            assert (!btor_bv_compare (d_x->lo, res_x->lo));
            assert (!btor_bv_compare (d_y->lo, res_y->lo));
            assert (no_overflows || btor_bvprop_is_fixed (g_mm, res_z));
            assert (!btor_bvprop_is_fixed (g_mm, res_z)
                    || !btor_bv_compare (tmp, res_z->lo));
            btor_bv_free (g_mm, tmp);
          }
          else if (btor_bvprop_is_fixed (g_mm, d_z))
          {
            assert (btor_bvprop_is_fixed (g_mm, res_z));
            tmp = btor_bv_mul (g_mm, d_x->lo, d_y->lo);
            if (!btor_bv_compare (tmp, d_z->lo))
            {
              assert (!btor_bv_compare (d_x->lo, res_x->lo));
              assert (!btor_bv_compare (d_y->lo, res_y->lo));
              btor_bv_free (g_mm, tmp);
              tmp = btor_bv_mul (g_mm, res_x->lo, res_y->lo);
              assert (!btor_bv_compare (tmp, res_z->lo));
            }
            btor_bv_free (g_mm, tmp);
          }
        }

        btor_bvprop_free (g_mm, d_y);
        TEST_BVPROP_RELEASE_RES_XYZ;
      }
      btor_bvprop_free (g_mm, d_x);
    }
    btor_bvprop_free (g_mm, d_z);
  }
  free_consts (bw, num_consts, consts);
}

void
ult_bvprop (uint32_t bw)
{
  bool res;
  uint32_t num_consts, num_consts_z;
  char **consts, **consts_z;
  BtorBitVector *tmp;
  BtorBvDomain *d_x, *d_y, *d_z;
  BtorBvDomain *res_x, *res_y, *res_z;

  num_consts   = generate_consts (bw, &consts);
  num_consts_z = generate_consts (1, &consts_z);

  for (uint32_t i = 0; i < num_consts_z; i++)
  {
    d_z = create_domain (consts_z[i]);
    for (uint32_t j = 0; j < num_consts; j++)
    {
      d_x = create_domain (consts[j]);
      for (uint32_t k = 0; k < num_consts; k++)
      {
        d_y = create_domain (consts[k]);

        res = btor_bvprop_ult (g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
        check_sat (d_x,
                   d_y,
                   d_z,
                   0,
                   res_x,
                   res_y,
                   res_z,
                   0,
                   0,
                   boolector_ult,
                   0,
                   0,
                   0,
                   0,
                   true,
                   res);

        if (btor_bvprop_is_fixed (g_mm, d_x)
            && btor_bvprop_is_fixed (g_mm, d_y))
        {
          assert (btor_bvprop_is_fixed (g_mm, res_x));
          assert (btor_bvprop_is_fixed (g_mm, res_y));
          if (is_xxx_domain (g_mm, d_z))
          {
            tmp = btor_bv_ult (g_mm, res_x->lo, res_y->lo);
            assert (!btor_bv_compare (d_x->lo, res_x->lo));
            assert (!btor_bv_compare (d_y->lo, res_y->lo));
            assert (btor_bvprop_is_fixed (g_mm, res_z));
            assert (!btor_bv_compare (tmp, res_z->lo));
            btor_bv_free (g_mm, tmp);
          }
          else if (btor_bvprop_is_fixed (g_mm, d_z))
          {
            assert (btor_bvprop_is_fixed (g_mm, res_z));
            tmp = btor_bv_ult (g_mm, d_x->lo, d_y->lo);
            if (!btor_bv_compare (tmp, d_z->lo))
            {
              assert (!btor_bv_compare (d_x->lo, res_x->lo));
              assert (!btor_bv_compare (d_y->lo, res_y->lo));
              btor_bv_free (g_mm, tmp);
              tmp = btor_bv_ult (g_mm, res_x->lo, res_y->lo);
              assert (!btor_bv_compare (tmp, res_z->lo));
            }
            btor_bv_free (g_mm, tmp);
          }
        }
        btor_bvprop_free (g_mm, d_y);
        TEST_BVPROP_RELEASE_RES_XYZ;
      }
      btor_bvprop_free (g_mm, d_x);
    }
    btor_bvprop_free (g_mm, d_z);
  }
  free_consts (bw, num_consts, consts);
  free_consts (1, num_consts_z, consts_z);
}

void
test_eq_bvprop ()
{
  eq_bvprop (1);
  eq_bvprop (2);
  eq_bvprop (3);
}

void
test_not_bvprop ()
{
  not_bvprop (1);
  not_bvprop (2);
  not_bvprop (3);
}

void
test_sll_const_bvprop ()
{
  sll_const_bvprop (1);
  sll_const_bvprop (2);
  sll_const_bvprop (3);
}

void
test_srl_const_bvprop ()
{
  srl_const_bvprop (1);
  srl_const_bvprop (2);
  srl_const_bvprop (3);
}

void
test_sll_bvprop ()
{
  sll_bvprop (2);
  sll_bvprop (4);
}

void
test_srl_bvprop ()
{
  srl_bvprop (2);
  srl_bvprop (4);
}

void
test_and_bvprop ()
{
  and_bvprop (1);
  and_bvprop (2);
  and_bvprop (3);
}

void
test_or_bvprop ()
{
  or_bvprop (1);
  or_bvprop (2);
  or_bvprop (3);
}

void
test_xor_bvprop ()
{
  xor_bvprop (1);
  xor_bvprop (2);
  xor_bvprop (3);
}

void
test_slice_bvprop ()
{
  slice_bvprop (1);
  slice_bvprop (2);
  slice_bvprop (3);
}

void
test_concat_bvprop ()
{
  concat_bvprop (2);
  concat_bvprop (3);
  concat_bvprop (4);
}

void
test_sext_bvprop ()
{
  sext_bvprop (2);
  sext_bvprop (3);
  sext_bvprop (4);
}

void
test_ite_bvprop ()
{
  ite_bvprop (1);
  ite_bvprop (2);
  ite_bvprop (3);
}

void
test_add_bvprop ()
{
  add_bvprop (1, false);
  add_bvprop (2, false);
  add_bvprop (3, false);
  add_bvprop (1, true);
  add_bvprop (2, true);
  add_bvprop (3, true);
}

void
test_ult_bvprop ()
{
  ult_bvprop (1);
  ult_bvprop (2);
  ult_bvprop (3);
}

void
test_mul_bvprop ()
{
  mul_bvprop (1, false);
  mul_bvprop (2, false);
  mul_bvprop (3, false);
  mul_bvprop (1, true);
  mul_bvprop (2, true);
  mul_bvprop (3, true);
}

/*------------------------------------------------------------------------*/

void
run_bvprop_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (valid_domain_bvprop);
  BTOR_RUN_TEST (fixed_domain_bvprop);
  BTOR_RUN_TEST (new_init_domain_bvprop);
  BTOR_RUN_TEST (eq_bvprop);
  BTOR_RUN_TEST (not_bvprop);
  BTOR_RUN_TEST (sll_const_bvprop);
  BTOR_RUN_TEST (srl_const_bvprop);
  BTOR_RUN_TEST (sll_bvprop);
  BTOR_RUN_TEST (srl_bvprop);
  BTOR_RUN_TEST (and_bvprop);
  BTOR_RUN_TEST (or_bvprop);
  BTOR_RUN_TEST (xor_bvprop);
  BTOR_RUN_TEST (slice_bvprop);
  BTOR_RUN_TEST (concat_bvprop);
  BTOR_RUN_TEST (sext_bvprop);
  BTOR_RUN_TEST (ite_bvprop);
  BTOR_RUN_TEST (add_bvprop);
  BTOR_RUN_TEST (mul_bvprop);
  BTOR_RUN_TEST (ult_bvprop);
}

void
finish_bvprop_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}
