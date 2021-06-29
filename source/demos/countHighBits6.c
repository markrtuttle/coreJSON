#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
//@ #include <bitops.gh>

#define implies(a,b) (!(a) || (b))

/*@

lemma uint8_t define_high_bit_is_high(uint8_t n)
  requires 0 <= n && n <= 0xFF;
  ensures result == (n & 0x80) && ((result != 0U) == (n >= 0x80));
{
  Z z_n = Z_of_uint8(n);
  Z z_mask = Z_of_uint8(0x80U);
  bitand_def(n, z_n, 0x80U, z_mask);
  return n & 0x80;
}

lemma uint8_t define_low_bits_shifted_one_bit_left(uint8_t n)
  requires 0 <= n && n <= 0xFFU;
  ensures (result == (n & 0x7FU) << 1U) && (result == (n < 0x80U ? 2 * n : 2 * (n - 0x80U)));
{
  Z z_n = Z_of_uint8(n);
  Z z_mask = Z_of_uint8(0x7FU);
  bitand_def(n, z_n, 0x7FU, z_mask);
  shiftleft_def(n & 0x7FU, nat_of_int(1));
  return (n & 0x7FU) << 1U;
}

@*/

static size_t countHighBits( uint8_t c )
//@ requires 0 <= c && c <= 0xFFU;
//@ ensures 0 <= result && result <= 8 && implies(c < 0xFFU, result < 8);
{
    uint8_t n = c;
    size_t i = 0;

    while( ( n & 0x80U ) != 0U )
    /*@
      invariant
        ((i == 0 && (c < 0xFFU ? n < 0xFFU : n <= 0xFFU)) ||
         (i == 1 && (c < 0xFFU ? n < 0xFEU : n <= 0xFEU)) ||
         (i == 2 && (c < 0xFFU ? n < 0xFCU : n <= 0xFCU)) ||
         (i == 3 && (c < 0xFFU ? n < 0xF8U : n <= 0xF8U)) ||
         (i == 4 && (c < 0xFFU ? n < 0xF0U : n <= 0xF0U)) ||
         (i == 5 && (c < 0xFFU ? n < 0xE0U : n <= 0xE0U)) ||
         (i == 6 && (c < 0xFFU ? n < 0xC0U : n <= 0xC0U)) ||
         (i == 7 && (c < 0xFFU ? n < 0x80U : n <= 0x80U)) ||
         (i == 8 && c == 0xFFU && n == 0x00U));
    @*/
    {
        //@ define_high_bit_is_high(n);
        i++;
        //@ define_low_bits_shifted_one_bit_left(n);
        n = (uint8_t) (( n & 0x7FU ) << 1U);
    }

    return i;
}
