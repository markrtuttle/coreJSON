#include <stddef.h>
#include <stdint.h>

//@ #include <bitops.gh>

static size_t countHighBits( uint8_t c )
//@ requires true;
//@ ensures 0 <= result && result <= 8;
{
  uint8_t n = c;
  size_t i = 0;

  while( n >= 0x80 )
    /*@
      invariant
        0 <= i && i <= 8 &&
        0 <= n && n <= 0xFF - (pow_nat(2, nat_of_int(i)) - 1);
    @*/
  {
    i++;

    //@ Z z_n = Z_of_uint8(n);
    //@ Z z_low_mask = Z_of_uint8(0x7FU);
    //@ bitand_def(n, z_n, 0x7FU, z_low_mask);
    uint8_t low_bits = (uint8_t) (n & 0x7FU);

    //@ shiftleft_def(low_bits, nat_of_int(1));
    n = (uint8_t) (low_bits << 1U);
  }

  return i;
}
