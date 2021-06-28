#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>

//@ #include <bitops.gh>

/*@

// Functions for signed<->unsigned conversion

// The k-bit representation KREP of an integer INT in two's complement
// in k bits is KREP = 2^k + INT (mod 2^k).  This representation
//   requires -2^(k-1) <= INT <= 2^(k-1) - 1
//   ensures 0 <= KREP <= 2^k - 1
// Notice that
//    KREP == INT < 0 ? 2^k + INT : INT
// Converseley, INT = KREP - 2^k (mod 2^k) and
//   requires 0 <= KREP <= 2^k - 1
//   ensures -2^(k-1) <= INT <= 2^(k-1) - 1
// Notice that
//    INT = KREP < 2^(k-1) ? KREP : KREP - 2^k

fixpoint uint8_t uint8_from_int8(int8_t n) {
    return (uint8_t) (
        -0x80 <= n && n <= 0x7F // n is valid int8 value
             ? ( n < 0 ? 0x0100 + n : n ) // interpret two's complement
             : ( 0 )                      // error
    );
}

fixpoint int8_t int8_from_uint8(uint8_t n) {
    return (int8_t) (
        0x00U <= n && n <= 0xFFU // n is valid uint8 value
             ? ( n < 0x80U ? n : n - 0x0100) // interpret two's complement
             : ( 0 )                         // error
    );
}

lemma void inverse0 (int8_t s)
requires -0x80 <= s && s <= 0x7F;
ensures s == int8_from_uint8( uint8_from_int8(s) );
{
}

lemma void inverse1 (uint8_t u)
requires 0x00U <= u && u <= 0xFFU;
ensures u == uint8_from_int8( int8_from_uint8(u) );
{
}

lemma void regression1 ()
requires true;
ensures true;
{
  assert 0U == uint8_from_int8(0);
  assert 1U == uint8_from_int8(1);
  assert 2U == uint8_from_int8(2);
  assert 4U == uint8_from_int8(4);
  assert 8U == uint8_from_int8(8);
  assert 16U == uint8_from_int8(16);
  assert 32U == uint8_from_int8(32);
  assert 64U == uint8_from_int8(64);
  assert 127U == uint8_from_int8(127);
  assert 0U == uint8_from_int8(128);
}

lemma void regression2 ()
requires true;
ensures true;
{
  assert 0U == uint8_from_int8(0);
  assert 0xFFU == uint8_from_int8(-1);
  assert 0xFEU == uint8_from_int8(-2);
  assert 0xFCU == uint8_from_int8(-4);
  assert 0xF8U == uint8_from_int8(-8);
  assert 0xF0U == uint8_from_int8(-16);
  assert 0xE0U == uint8_from_int8(-32);
  assert 0xC0U == uint8_from_int8(-64);
  assert 0x80U == uint8_from_int8(-128);
  assert 0U == uint8_from_int8(-129);
}

lemma void regression3 ()
requires true;
ensures true;
{
  assert 0 == int8_from_uint8(-1);

  assert 0 == int8_from_uint8(0U);
  assert 1 == int8_from_uint8(1U);
  assert 2 == int8_from_uint8(2U);
  assert 4 == int8_from_uint8(4U);
  assert 8 == int8_from_uint8(8U);
  assert 16 == int8_from_uint8(16U);
  assert 32 == int8_from_uint8(32U);
  assert 64 == int8_from_uint8(64U);
  assert 127  == int8_from_uint8(127U);
  assert -128  == int8_from_uint8(128U);
  assert -1 == int8_from_uint8(255);
  assert 0 == int8_from_uint8(256);
}


lemma void regresion4 ()
requires true;
ensures true;
{
  assert 0 == int8_from_uint8(0U);
  assert -1 == int8_from_uint8(0xFFU);
  assert -2 == int8_from_uint8(0xFEU);
  assert -4 == int8_from_uint8(0xFCU);
  assert -8 == int8_from_uint8(0xF8U);
  assert -16 == int8_from_uint8(0xF0U);
  assert -32 == int8_from_uint8(0xE0U);
  assert -64 == int8_from_uint8(0xC0U);
  assert -128 == int8_from_uint8(0x80U);
}

lemma void unsigned_from_signed();
  requires integer_(?s, 1, true, ?s_val);
  // ensures integer_(s, 1, false, uint8_from_int8(s_val));
  ensures integer_(s, 1, true, uint8_from_int8(s_val));

lemma void signed_from_unsigned();
  requires integer_(?u, 1, false, ?u_val);
  ensures integer_(u, 1, true, int8_from_uint8(u_val));

@*/


int main()
//@ requires true;
//@ ensures true;
{
  int8_t s = (int8_t) -1;
  uint8_t u = (uint8_t) 1;

  true;
#if VERIFAST
  // Shows that signed bit of integer_ is meaningless
  //@ open character(&s,_);
  //@ unsigned_from_signed();
  //@ close character(&s,_);
#else
  // Shows that verifast cast does not match c semantics (not just value filter)
#endif
  u = (uint8_t) s;
  assert( u == 0xFFU );

  return 0;
}
