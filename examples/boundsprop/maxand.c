#include "maxand.h"
#include "../../boolector.h"
#include "../../btorutil.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

/* maxAND algorithm from hacker's delight, page 61 */

BtorNode *
btor_maxand (Btor *btor,
             BtorNode *a_in,
             BtorNode *b_in,
             BtorNode *c_in,
             BtorNode *d_in,
             BtorNode *m_in,
             int num_bits)
{
  BtorNode *temp_1, *temp_2, *m, *zero;
  BtorNode *tmp, *a, *b, *c, *d, *not_b, *not_d, *not_m, *m_minus_1;
  BtorNode *b_and_not_d, *b_and_not_d_and_m, *b_and_not_d_and_m_ne_zero;
  BtorNode *b_and_not_m, *not_b_and_d, *not_b_and_d_and_m, *d_and_not_m;
  BtorNode *not_b_and_d_and_m_ne_zero, *temp_1_ugte_a, *temp_2_ugte_c;
  BtorNode *result, *cond_if, *cond_else_1, *cond_else_2;
  BtorNode *one_log_bits, *one_full_bits;
  int i;

  assert (btor != NULL);
  assert (a_in != NULL);
  assert (b_in != NULL);
  assert (c_in != NULL);
  assert (d_in != NULL);
  assert (m_in != NULL);
  assert (num_bits > 0);
  assert (btor_is_power_of_2_util (num_bits));

  a = boolector_copy (btor, a_in);
  b = boolector_copy (btor, b_in);
  c = boolector_copy (btor, c_in);
  d = boolector_copy (btor, d_in);
  m = boolector_copy (btor, m_in);

  one_log_bits  = boolector_one (btor, btor_log_2_util (num_bits));
  one_full_bits = boolector_one (btor, num_bits);
  zero          = boolector_zero (btor, num_bits);

  for (i = 0; i < num_bits; i++)
  {
    not_m     = boolector_not (btor, m);
    m_minus_1 = boolector_sub (btor, m, one_full_bits);

    not_d                     = boolector_not (btor, d);
    b_and_not_d               = boolector_and (btor, b, not_d);
    b_and_not_d_and_m         = boolector_and (btor, b_and_not_d, m);
    b_and_not_d_and_m_ne_zero = boolector_ne (btor, b_and_not_d_and_m, zero);

    b_and_not_m   = boolector_and (btor, b, not_m);
    temp_1        = boolector_or (btor, b_and_not_m, m_minus_1);
    temp_1_ugte_a = boolector_ugte (btor, temp_1, a);

    not_b                     = boolector_not (btor, b);
    not_b_and_d               = boolector_and (btor, not_b, d);
    not_b_and_d_and_m         = boolector_and (btor, not_b_and_d, m);
    not_b_and_d_and_m_ne_zero = boolector_ne (btor, not_b_and_d_and_m, zero);

    d_and_not_m   = boolector_and (btor, d, not_m);
    temp_2        = boolector_or (btor, d_and_not_m, m_minus_1);
    temp_2_ugte_c = boolector_ugte (btor, temp_2, c);

    /* update b */
    cond_if = boolector_cond (btor, temp_1_ugte_a, temp_1, b);
    tmp     = boolector_cond (btor, b_and_not_d_and_m_ne_zero, cond_if, b);
    boolector_release (btor, b);
    b = tmp;

    /* update d */
    cond_else_1 = boolector_cond (btor, temp_2_ugte_c, temp_2, d);
    cond_else_2 =
        boolector_cond (btor, not_b_and_d_and_m_ne_zero, cond_else_1, d);
    tmp = boolector_cond (btor, b_and_not_d_and_m_ne_zero, d, cond_else_2);
    boolector_release (btor, d);
    d = tmp;

    /* update m */
    tmp = boolector_srl (btor, m, one_log_bits);
    boolector_release (btor, m);
    m = tmp;

    boolector_release (btor, not_b);
    boolector_release (btor, not_d);
    boolector_release (btor, not_m);
    boolector_release (btor, m_minus_1);
    boolector_release (btor, b_and_not_d);
    boolector_release (btor, b_and_not_d_and_m);
    boolector_release (btor, b_and_not_d_and_m_ne_zero);
    boolector_release (btor, not_b_and_d);
    boolector_release (btor, not_b_and_d_and_m);
    boolector_release (btor, not_b_and_d_and_m_ne_zero);
    boolector_release (btor, b_and_not_m);
    boolector_release (btor, d_and_not_m);
    boolector_release (btor, temp_1);
    boolector_release (btor, temp_2);
    boolector_release (btor, temp_1_ugte_a);
    boolector_release (btor, temp_2_ugte_c);
    boolector_release (btor, cond_if);
    boolector_release (btor, cond_else_1);
    boolector_release (btor, cond_else_2);
  }
  result = boolector_and (btor, b, d);

  boolector_release (btor, a);
  boolector_release (btor, b);
  boolector_release (btor, c);
  boolector_release (btor, d);
  boolector_release (btor, m);
  boolector_release (btor, zero);
  boolector_release (btor, one_log_bits);
  boolector_release (btor, one_full_bits);

  return result;
}
