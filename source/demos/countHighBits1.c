#include <stddef.h>
#include <stdint.h>

//@ #include <bitops.gh>

static size_t countHighBits( uint8_t c )
//@ requires true;
//@ ensures 0 <= result && result <= 8;
{
  uint8_t n = c;
  size_t i = 0;

  while( true )
    /*@
      invariant
        0 <= i && i <= 8 &&
        0 <= n && n <= 0xFF - (pow_nat(2, nat_of_int(i)) - 1);
    @*/
  {
    uint8_t high_bit = (uint8_t) (n & 0x80U);
    //@ Z zn = Z_of_uint8(n);
    //@ Z zhigh_mask = Z_of_uint8(0x80U);
    //@ bitand_def(n, zn, 0x80U, zhigh_mask);
    if (!(high_bit != 0U)) break;

    i++;
    uint8_t low_bits = (uint8_t) (n & 0x7FU);
    //@ Z zlow_mask = Z_of_uint8(0x7FU);
    //@ bitand_def(n, zn, 0x7FU, zlow_mask);
    n = (uint8_t) (low_bits << 1U);
    //@ shiftleft_def(low_bits, nat_of_int(1));
  }

  return i;
}
