#include <stddef.h>
#include <stdint.h>
//@ #include <bitops.gh>

/*@
fixpoint Z take_low_bits(Z bits, int count) {
  switch (bits) {
    case Zsign(bit): return bits;
    case Zdigit(bits0, bit): return
      count <= 0 ?
        take_low_bits(bits0, count-1) :
        Zdigit( take_low_bits(bits0, count-1), bit);
  }
}

fixpoint Z push_low_bits(Z bits, nat count, bool bit) {
  switch (count) {
    case zero: return bits;
    case succ(count0): return Zdigit(push_low_bits(bits, count0, bit), bit);
  }
}

fixpoint uint8_t shift_left(Z bits, int count) {
  return
    int_of_Z(
       take_low_bits(
         push_low_bits(bits, nat_of_int(count), false), 8) );
}
@*/


static size_t countHighBits( uint8_t n )
//@ requires 0 <= n && n <= 0xFFU;
//@ ensures 0 <= result && result <= 8;
{
  size_t i = 0;

  //@ Z z_high_mask = Z_of_uint8(0x80U);
  //@ Z z_low_mask = Z_of_uint8(0x7FU);

  //@ Z z_n0 = Z_of_uint8(n);
  //@ bitand_def(n, z_n0, 0x80U, z_high_mask);
  while( ( n & 0x80U ) != 0U )
    /*@
      invariant 0 <= i && i <= 8U && n == shift_left(z_n0, i);
    @*/
  {
    //@ Z z_n = Z_of_uint8(n);
    //@ bitand_def(n, z_n, 0x7FU, z_low_mask);
    uint8_t low_bits = (uint8_t) (n & 0x7FU);

    //@ shiftleft_def(low_bits, nat_of_int(1));
    n = (uint8_t) (low_bits << 1U);

    //@ z_n = Z_of_uint8(n);
    //@ bitand_def(n, z_n, 0x80U, z_high_mask);
    i++;
  }

  return i;
}
