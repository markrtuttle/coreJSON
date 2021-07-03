#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include "core_json.h"

//@#include <bitops.gh>

typedef union
{
    char c;
    uint8_t u;
} char_;

#if ( CHAR_MIN == 0 )
    #define isascii_( x )    ( ( x ) <= '\x7F' )
#else
    #define isascii_( x )    ( ( x ) >= '\0' )
#endif
#define iscntrl_( x )        ( isascii_( x ) && ( ( x ) < ' ' ) )
#define isdigit_( x )        ( ( ( x ) >= '0' ) && ( ( x ) <= '9' ) )
/* NB. This is whitespace as defined by the JSON standard (ECMA-404). */
#define isspace_( x )                          \
    ( ( ( x ) == ' ' ) || ( ( x ) == '\t' ) || \
      ( ( x ) == '\n' ) || ( ( x ) == '\r' ) )

#define isOpenBracket_( x )           ( ( ( x ) == '{' ) || ( ( x ) == '[' ) )
#define isCloseBracket_( x )          ( ( ( x ) == '}' ) || ( ( x ) == ']' ) )
#define isCurlyPair_( x, y )          ( ( ( x ) == '{' ) && ( ( y ) == '}' ) )
#define isSquarePair_( x, y )         ( ( ( x ) == '[' ) && ( ( y ) == ']' ) )
#define isMatchingBracket_( x, y )    ( isCurlyPair_( x, y ) || isSquarePair_( x, y ) )
#define isSquareOpen_( x )            ( ( x ) == '[' )
#define isSquareClose_( x )           ( ( x ) == ']' )


/*@

// Lemmas for countHighBits

lemma uint8_t define_high_bit_is_high(uint8_t n)
  requires 0 <= n && n <= 0xFF;
  ensures result == (n & 0x80) && result == (n < 0x80U ? 0x00U : 0x80U);
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
        -128 <= n && n <= 127 // n is valid int8 value
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

lemma uint8_t uint8_from_char(char *c);
requires
  character(c, ?c_val) &*&
  -128 <= c_val && c_val <= 127;
ensures
  u_character((uint8_t*) c, ?u_val) &*&
  (u_val == uint8_from_int8(c_val)) &&
  0 <= u_val && u_val <= 0xFFU;

lemma char char_from_uint8(uint8_t *c);
requires
  u_character(c, ?u_val) &*&
  0 <= u_val && u_val <= 0xFFU;
ensures
  character((int8_t *) c, ?c_val) &*&
  (c_val == int8_from_uint8(u_val)) &&
  -128 <= c_val && c_val <= 127;
@*/

#define implies(a,b) (!(a) || (b))

#if 0
        ((i == 0 && n <= 0xFFU && implies(c <= 0xF7U, n <= 0xF0 + 0x07U)) && implies(c >= 0xC0U, n >= 0xC0U) ||
         (i == 1 && n <= 0xFEU && implies(c <= 0xF7U, n <= 0xE0 + 0x0EU)) && implies(c >= 0xC0U, n >= 0x80U) ||
         (i == 2 && n <= 0xFCU && implies(c <= 0xF7U, n <= 0xC0 + 0x1C)) ||
         (i == 3 && n <= 0xF8U && implies(c <= 0xF7U, n <= 0x80 + 0x38)) ||
         (i == 4 && n <= 0xF0U && implies(c <= 0xF7U, n <  0x80)) ||
         (i == 5 && n <= 0xE0U && c >= 0xF8U) ||
         (i == 6 && n <= 0xC0U && c >= 0xFCU) ||
         (i == 7 && n <= 0x80U && c >= 0xFEU) ||
         (i == 8 && c == 0xFFU && n == 0x00U));
#endif

#define countHighBitsTermination \
  ((i == 0 && n <= 0xFFU) ||     \
   (i == 1 && n <= 0xFEU) ||     \
   (i == 2 && n <= 0xFCU) ||     \
   (i == 3 && n <= 0xF8U) ||     \
   (i == 4 && n <= 0xF0U) ||     \
   (i == 5 && n <= 0xE0U) ||     \
   (i == 6 && n <= 0xC0U) ||     \
   (i == 7 && n <= 0x80U) ||     \
   (i == 8 && n == 0x00U))

#define countHighBitsLowerBound                                \
  ((i == 0 && implies(c <= 0xF7U, n <= 0xF0 + 0x07U)) ||       \
   (i == 1 && implies(c <= 0xF7U, n <= 0xE0 + 0x0EU)) ||       \
   (i == 2 && implies(c <= 0xF7U, n <= 0xC0 + 0x1C)) ||        \
   (i == 3 && implies(c <= 0xF7U, n <= 0x80 + 0x38)) ||        \
   (i == 4 && implies(c <= 0xF7U, n <  0x80)) ||               \
   (i > 4 && implies(c <= 0xF7U, i <= 4)))

#define countHighBitsUpperBound                        \
  ((i == 0 && implies(c >= 0xC0U, n >= 0xC0U)) ||      \
   (i == 1 && implies(c >= 0xC0U, n >= 0x80U)) ||      \
   (i > 1))

static size_t countHighBits( uint8_t c )
/*@
  requires
    0x00U <= c && c <= 0xFFU;
@*/
/*@
  ensures
    0 <= result && result <= 8 &&
    implies (c >= 0xC0U, result >= 2) &&
    implies(c <= 0xF7U, result <= 4);
@*/
{
    uint8_t n = c;
    size_t i = 0;

    while( ( n & 0x80U ) != 0U )
    /*@
      invariant
        countHighBitsTermination &&
        countHighBitsLowerBound &&
        countHighBitsUpperBound;
    @*/
    {
        //@ define_high_bit_is_high(n);
        i++;
        //@ define_low_bits_shifted_one_bit_left(n);
        n = (uint8_t) (( n & 0x7FU ) << 1U);
    }

    //@ define_high_bit_is_high(n);
    assert(implies(c <= 0xF7U, i <= 4));
    return i;
}

static bool shortestUTF8( size_t length,
                          uint32_t value )
/*@
  requires
    2 <= length && length <= 4;
@*/
//@ ensures true;
{
    bool ret = false;
    uint32_t min, max;

    assert( ( length >= 2U ) && ( length <= 4U ) );

    switch( length )
    {
        case 2:
            min = ( uint32_t ) 0x00000080U /* 1 << 7U */;
            max = ( ( uint32_t ) 0x00000800U /* 1 << 11U */) - 1U;
            break;

        case 3:
            min = ( uint32_t ) 0x00000800U /* 1 << 11U */;
            max = ( ( uint32_t ) 0x00010000U /* 1 << 16U */) - 1U;
            break;

        default:
            min = ( uint32_t ) 0x00010000U /* 1 << 16U */;
            max = 0x10FFFFU;
            break;
    }

    if( ( value >= min ) && ( value <= max ) &&
        ( ( value < 0xD800U ) || ( value > 0xDFFFU ) ) )
    {
        ret = true;
    }

    return ret;
}

static bool skipUTF8MultiByte( const char * buf,
                               size_t * start,
                               size_t max )
/*@
requires
  buf != NULL &*& start != NULL &*& max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0)  &*&
  0 <= start_val0 && start_val0 < max && !isascii_(nth(start_val0, buf_val));
@*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1);
@*/
{
    bool ret = false;
    size_t i, bitCount, j;
    uint32_t value = 0;
    char_ c;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    i = *start;
    assert( i < max );
    assert( !isascii_( buf[ i ] ) );

    c.c = buf[ i ];
    //@ character_limits(&c.c);
    assert(-128 <= c.c);
    //@ uint8_from_char(&c.c);

    if( ( c.u > 0xC1U ) && ( c.u < 0xF5U ) )
    {
        bitCount = countHighBits( c.u );
        //@ define_mask(bitCount);
        //@ define_value(c.u, bitCount);
        value = ( ( uint32_t ) c.u ) & ( ( ( uint32_t ) 1 << ( 7U - bitCount ) ) - 1U );

        /* The bit count is 1 greater than the number of bytes,
         * e.g., when j is 2, we skip one more byte. */
        for( j = bitCount - 1U; j > 0U; j-- )
          /*@
            invariant
              0 <= j && j <= bitCount - 1 &&
              0 <= i && i < max &&
              0 <= value && value <= pow_nat(2, nat_of_int(32-6*j)) - 1 &*&
              chars(buf, max, buf_val) &*&
              integer_(start, sizeof(size_t), false, start_val0) &*&
              u_character(&c.u, ?u_val) &*&
              0 <= u_val && u_val <= 0xFFU &*&
              chars(&c.c + 1, 0, nil);
           @*/

        {
            i++;

            if( i >= max )
            {
                break;
            }

            //@ char_from_uint8(&c.u);
            c.c = buf[ i ];
            //@ character_limits(&c.c);
            assert(-128 <= c.c);
            //@ uint8_from_char(&c.c);

            /* Additional bytes must match 10xxxxxx. */
            if( ( c.u & 0xC0U ) != 0x80U )
            {
                break;
            }

            //@ define_shift_six_plus_mask_six(value, c.u, j);
            value = ( value << 6U ) | ( c.u & 0x3FU );
        }

        if( ( j == 0U ) && ( shortestUTF8( bitCount, value ) == true ) )
        {
            *start = i + 1U;
            ret = true;
        }
    }

    return ret;
}
