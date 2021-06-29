#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include "core_json.h"

/** @cond DO_NOT_DOCUMENT */

//@ #include <bitops.gh>

#define implies(a,b) (!(a) || (b))


/*@

// Lemmas for skipUTF8MultiByte

lemma uint8_t define_mask(size_t bitCount)
  requires 0 <= bitCount && bitCount < 8;
  ensures result == ((1 << (7U - bitCount)) - 1) &&
          0 <= result && result <= 0xFFU;
{
  shiftleft_def(1, nat_of_int( 7U - bitCount ));
  return (1 << (7U - bitCount)) - 1;
}


lemma uint8_t define_value(uint8_t cu, size_t bitCount)
  requires 0x00U <= cu && cu <= 0xFFU &&
           0 <= bitCount && bitCount < 8;
  ensures result == (cu & ((1 << (7U - bitCount)) - 1)) &&
           0 <= result && result <= 0xFFU;
{
  define_mask(bitCount);
  uint8_t mask = (1 << (7U - bitCount)) - 1;

  Z z_cu = Z_of_uint8(cu);
  Z z_mask = Z_of_uint8(mask);
  bitand_def(cu, z_cu, mask, z_mask);
  return cu & mask;
}


@*/
