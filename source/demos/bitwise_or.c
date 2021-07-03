#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include "core_json.h"

//@#include <bitops.gh>


/*@

lemma uint8_t define_mask_six(uint8_t byte)
requires 0 <= byte && byte <= 0xFF;
ensures (result == (byte & 0x3FU)) && 0 <= result && result <= 0x3FU;
{
  Z z_byte = Z_of_uint8(byte);
  Z z_mask = Z_of_uint8(0x3FU);
  bitand_def(byte, z_byte, 0x3FU, z_mask);
  return byte & 0x3FU;
}

lemma uint32_t define_shift_six(uint32_t value)
requires 0 <= value && value <= 0xFFFFFFFFU;
ensures (result == (value << 6)) && (result == 64 * value);
{
  shiftleft_def(value, nat_of_int( 6 ));
  return value << 6U;
}

// Note: While writing define_shift_six_plus_mask_six lemma, observed
//   deleting ensures upper bound on result, time 23 sec -> 4 sec
//   remaining -> i slows from 6 seconds to 23 seconds.
//   reordering ensures slows from 1 second to 6 seconds.

lemma uint32_t define_shift_six_plus_mask_six(uint32_t value,
                                              uint8_t byte,
                                              uint8_t remaining)
requires
  0 <= value && value <= pow_nat(2, nat_of_int(32-6*remaining)) - 1 &&
  0 <= byte && byte <= 0xFFU &&
  1 <= remaining && remaining <= 4;
ensures
  0 <= result && result <= pow_nat(2, nat_of_int(32-6*(remaining-1))) - 1 &&
  (result == ((value << 6) | (byte & 0x3FU)));
{
  uint32_t high_addend = define_shift_six(value);
  uint8_t low_addend = define_mask_six(byte);

  Z z_low_addend = Z_of_uint32(low_addend);
  Z z_high_addend = Z_of_uint32(high_addend);
  bitor_def(high_addend, z_high_addend, low_addend, z_low_addend);
  return high_addend | low_addend;
}

@*/
