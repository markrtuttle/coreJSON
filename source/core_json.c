/*
 * coreJSON v3.0.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_json.c
 * @brief The source file that implements the user-facing functions in core_json.h.
 */

#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include "core_json.h"

/** @cond DO_NOT_DOCUMENT */

//@ #include <bitops.gh>

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

/* A compromise to satisfy both MISRA and CBMC */
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

/**
 * @brief Advance buffer index beyond whitespace.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 */
static void skipSpace( const char * buf,
                       size_t * start,
                       size_t max )
/*@
requires
  buf != NULL && start !=NULL && max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && implies(start_val0 < max, start_val1 <= max);
  @*/
{
    size_t i;
    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    for( i = *start; i < max; i++ )
    /*@ invariant
          chars(buf, max, buf_val) &*&
          start_val0 <= i && implies(start_val0 < max, i <= max);
    @*/
    {
        if( !isspace_( buf[ i ] ) )
        {
            break;
        }
    }

    *start = i;
}

/**
 * @brief Count the leading 1s in a byte.
 *
 * The high-order 1 bits of the first byte in a UTF-8 encoding
 * indicate the number of additional bytes to follow.
 *
 * @return the count
 */
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
    return i;
}

/**
 * @brief Is the value a legal Unicode code point and encoded with
 * the fewest bytes?
 *
 * The last Unicode code point is 0x10FFFF.
 *
 * Unicode 3.1 disallows UTF-8 interpretation of non-shortest form sequences.
 * 1 byte encodes 0 through 7 bits
 * 2 bytes encode 8 through 5+6 = 11 bits
 * 3 bytes encode 12 through 4+6+6 = 16 bits
 * 4 bytes encode 17 through 3+6+6+6 = 21 bits
 *
 * Unicode 3.2 disallows UTF-8 code point values in the surrogate range,
 * [U+D800 to U+DFFF].
 *
 * @note Disallow ASCII, as this is called only for multibyte sequences.
 */
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

/**
 * @brief Advance buffer index beyond a UTF-8 code point.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid code point was present;
 * false otherwise.
 *
 * 00–7F    Single-byte character
 * 80–BF    Trailing byte
 * C0–DF    Leading byte of two-byte character
 * E0–EF    Leading byte of three-byte character
 * F0–F7    Leading byte of four-byte character
 * F8–FB    Illegal (formerly leading byte of five-byte character)
 * FC–FD    Illegal (formerly leading byte of six-byte character)
 * FE–FF    Illegal
 *
 * The octet values C0, C1, and F5 to FF are illegal, since C0 and C1
 * would introduce a non-shortest sequence, and F5 or above would
 * introduce a value greater than the last code point, 0x10FFFF.
 */
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
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && start_val1 <= max && implies(result, start_val0 < start_val1);
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
              start_val0 <= i && i < max &&
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

/**
 * @brief Advance buffer index beyond an ASCII or UTF-8 code point.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid code point was present;
 * false otherwise.
 */
static bool skipUTF8( const char * buf,
                      size_t * start,
                      size_t max )
//@ requires true;
//@ ensures true;
#if 0
{
    bool ret = false;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    if( *start < max )
    {
        if( isascii_( buf[ *start ] ) )
        {
            *start += 1U;
            ret = true;
        }
        else
        {
            ret = skipUTF8MultiByte( buf, start, max );
        }
    }

    return ret;
}
#endif
{
  return true;
}

/**
 * @brief Convert a hexadecimal character to an integer.
 *
 * @param[in] c  The character to convert.
 *
 * @return the integer value upon success or NOT_A_HEX_CHAR on failure.
 */
#define NOT_A_HEX_CHAR    ( 0x10U )
static uint8_t hexToInt( char c )
//@ requires true;
//@ ensures 0 <= result &*& result <= 16;
{
    char_ n;

    n.c = c;

    if( ( c >= 'a' ) && ( c <= 'f' ) )
    {
        n.c -= 'a';
        //@ uint8_from_char(&n.c);
        n.u += 10U;
    }
    else if( ( c >= 'A' ) && ( c <= 'F' ) )
    {
        n.c -= 'A';
        //@ uint8_from_char(&n.c);
        n.u += 10U;
    }
    else if( isdigit_( c ) )
    {
        n.c -= '0';
        //@ uint8_from_char(&n.c);
    }
    else
    {
        //@ uint8_from_char(&n.c);
        n.u = NOT_A_HEX_CHAR;
    }

    return n.u;
}

/**
 * @brief Advance buffer index beyond a single \u Unicode
 * escape sequence and output the value.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[out] outValue  The value of the hex digits.
 *
 * @return true if a valid escape sequence was present;
 * false otherwise.
 *
 * @note For the sake of security, \u0000 is disallowed.
 */
static bool skipOneHexEscape( const char * buf,
                              size_t * start,
                              size_t max,
                              uint16_t * outValue )
/*@
requires
  buf != NULL &&  start != NULL && 0 < max && outValue != NULL &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  integer_(outValue, sizeof(uint16_t), false, _) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  integer_(outValue, sizeof(uint16_t), false, _) &*&
  start_val0 <= start_val1 && implies(result, start_val1 <= max);
  @*/
{
    bool ret = false;
    size_t i, end;
    uint16_t value = 0;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );
    assert( outValue != NULL );

#define HEX_ESCAPE_LENGTH    ( 6U )   /* e.g., \u1234 */
    if (*start > SIZE_MAX - HEX_ESCAPE_LENGTH)
    {
        return false;
    }

    i = *start;
    end = i + HEX_ESCAPE_LENGTH;

    if( ( end < max ) && ( buf[ i ] == '\\' ) && ( buf[ i + 1U ] == 'u' ) )
    {
        for( i += 2U; i < end; i++ )
          /*@ invariant
                chars(buf, max, buf_val) &*&
                0 <= end-i &*& end-i <= 4 &*&
                ((end-i == 0) ||
                 (end-i == 1 && value <= 0x0FFF) ||
                 (end-i == 2 && value <= 0x00FF) ||
                 (end-i == 3 && value <= 0x000F) ||
                 (end-i == 4 && value <= 0x0000))
               ;
          @*/
        {
            uint8_t n = hexToInt( buf[ i ] );

            if( n == NOT_A_HEX_CHAR )
            {
                break;
            }

            value = (uint16_t)((uint16_t)( value << 4U ) + n);
        }
    }

    if( ( i == end ) && ( value > 0U ) )
    {
        ret = true;
        *outValue = value;
        *start = i;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond one or a pair of \u Unicode escape sequences.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * Surrogate pairs are two escape sequences that together denote
 * a code point outside the Basic Multilingual Plane.  They must
 * occur as a pair with the first "high" value in [U+D800, U+DBFF],
 * and the second "low" value in [U+DC00, U+DFFF].
 *
 * @return true if a valid escape sequence was present;
 * false otherwise.
 *
 * @note For the sake of security, \u0000 is disallowed.
 */
#define isHighSurrogate( x )    ( ( ( x ) >= 0xD800U ) && ( ( x ) <= 0xDBFFU ) )
#define isLowSurrogate( x )     ( ( ( x ) >= 0xDC00U ) && ( ( x ) <= 0xDFFFU ) )

static bool skipHexEscape( const char * buf,
                           size_t * start,
                           size_t max )
/*@
requires
  buf != NULL && start != NULL && max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && implies(result, start_val1 <= max);
  @*/
{
    bool ret = false;
    size_t i;
    uint16_t value;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    i = *start;

    //@ assume(&i != NULL);
    //@ assume(&value != NULL);
    if( skipOneHexEscape( buf, &i, max, &value ) == true )
    {
        if( isHighSurrogate( value ) )
        {
            if( ( skipOneHexEscape( buf, &i, max, &value ) == true ) &&
                ( isLowSurrogate( value ) ) )
            {
                ret = true;
            }
        }
        else if( isLowSurrogate( value ) )
        {
            /* premature low surrogate */
        }
        else
        {
            ret = true;
        }
    }

    if( ret == true )
    {
        *start = i;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond an escape sequence.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid escape sequence was present;
 * false otherwise.
 *
 * @note For the sake of security, \NUL is disallowed.
 */
static bool skipEscape( const char * buf,
                        size_t * start,
                        size_t max )
/*@
requires
  buf != NULL && start != NULL && max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && implies(result, start_val1 <= max);
  @*/
{
    bool ret = false;
    size_t i;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    i = *start;

    if( ( i < ( max - 1U ) ) && ( buf[ i ] == '\\' ) )
    {
        char c = buf[ i + 1U ];

        switch( c )
        {
            case '\0':
                break;

            case 'u':
                //@ assume(&i != NULL);
                ret = skipHexEscape( buf, &i, max );
                break;

            case '"':
            case '\\':
            case '/':
            case 'b':
            case 'f':
            case 'n':
            case 'r':
            case 't':
                i += 2U;
                ret = true;
                break;

            default:

                /* a control character: (NUL,SPACE) */
                if( iscntrl_( c ) )
                {
                    i += 2U;
                    ret = true;
                }

                break;
        }
    }

    if( ret == true )
    {
        *start = i;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond a double-quoted string.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid string was present;
 * false otherwise.
 */
static bool skipString( const char * buf,
                        size_t * start,
                        size_t max )
/*@
requires
  buf != NULL && start != NULL && 0 < max &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && implies(result, start_val0 < start_val1);
  @*/
{
    bool ret = false;
    size_t i;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    i = *start;

    if( ( i < max ) && ( buf[ i ] == '"' ) )
    {
        i++;

        while( i < max )
        //@ invariant chars(buf, max, buf_val) &*& u_integer(&i, ?ival) &*& start_val0 <= ival;
        {
            if( buf[ i ] == '"' )
            {
                ret = true;
                i++;
                break;
            }

            if( buf[ i ] == '\\' )
            {
              //@ assume(&i != NULL);
                if( skipEscape( buf, &i, max ) != true )
                {
                    break;
                }
            }
            /* An unescaped control character is not allowed. */
            else if( iscntrl_( buf[ i ] ) )
            {
                break;
            }
            else if( skipUTF8( buf, &i, max ) != true )
            {
                break;
            }
            else
            {
                /* MISRA 15.7 */
            }
        }
    }

    if( ret == true )
    {
        *start = i;
    }

    return ret;
}

/**
 * @brief Compare the leading n bytes of two character sequences.
 *
 * @param[in] a  first character sequence
 * @param[in] b  second character sequence
 * @param[in] n  number of bytes
 *
 * @return true if the sequences are the same;
 * false otherwise
 */
static bool strnEq( const char * a,
                    const char * b,
                    size_t n )
/*@
requires
  a != NULL && b != NULL &*&
  chars(a, n, ?a_val) &*& chars(b, n, ?b_val);
  @*/
/*@
ensures
  chars(a, n, a_val) &*& chars(b, n, b_val);
  @*/
{
    size_t i;

    assert( ( a != NULL ) && ( b != NULL ) );

    for( i = 0; i < n; i++ )
      //@ invariant chars(a, n, a_val) &*& chars(b, n, b_val);
    {
        if( a[ i ] != b[ i ] )
        {
            break;
        }
    }

    return ( i == n ) ? true : false;
}

/**
 * @brief Advance buffer index beyond a literal.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[in] literal  The type of literal.
 * @param[in] length  The length of the literal.
 *
 * @return true if the literal was present;
 * false otherwise.
 */
static bool skipLiteral( const char * buf,
                         size_t * start,
                         size_t max,
                         const char * literal,
                         size_t length )
/*@
requires
  buf != NULL && start != NULL && max > 0 && literal != NULL &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  chars(literal, length, ?literal_val) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  chars(literal, length, literal_val) &*&
  start_val0 <= start_val1 && implies(result, length == 0 || start_val0 < start_val1);
  @*/
{
    bool ret = false;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );
    assert( literal != NULL );

    if( ( *start < max ) && ( length <= ( max - *start ) ) )
    {
        //@ chars_split(buf, start_val0);
        //@ chars_split(buf + start_val0, length);
        ret = strnEq( &buf[ *start ], literal, length );
        //@ chars_join(buf + start_val0);
        //@ chars_join(buf);
    }

    if( ret == true )
    {
        *start += length;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond a JSON literal.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid literal was present;
 * false otherwise.
 */
#define skipLit_( x )     ( skipLiteral( buf, start, max, ( x ), ( sizeof( x ) - 1UL ) ) == true )

static bool skipAnyLiteral( const char * buf,
                            size_t * start,
                            size_t max )
/*@
requires
  buf != NULL && start != NULL && max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && implies(result, start_val0 < start_val1);
  @*/
{
    bool ret = false;

//  if( skipLit_( "true" ) || skipLit_( "false" ) || skipLit_( "null" ) )
    char true_literal[5] = "true";
    char false_literal[6] = "false";
    char null_literal[5] = "null";

    char *true_ptr = true_literal;
    char *false_ptr = false_literal;
    char *null_ptr = null_literal;

    //@ assume(true_ptr != 0);
    //@ assume(false_ptr != 0);
    //@ assume(null_ptr != 0);

    if( skipLiteral( buf, start, max, true_ptr, ( 4 ) ) == true ||
        skipLiteral( buf, start, max, false_ptr, ( 5 ) ) == true ||
        skipLiteral( buf, start, max, null_ptr, ( 4 ) ) == true )
    {
        ret = true;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond one or more digits.
 * Optionally, output the integer value of the digits.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[out] outValue  The integer value of the digits.
 *
 * @note outValue may be NULL.  If not NULL, and the output
 * exceeds ~2 billion, then -1 is output.
 *
 * @return true if a digit was present;
 * false otherwise.
 */
#define MAX_FACTOR    ( MAX_INDEX_VALUE / 10 )
static bool skipDigits( const char * buf,
                        size_t * start,
                        size_t max,
                        int32_t * outValue )
/*@ requires
  buf != NULL && start != NULL && max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  (outValue != NULL ? integer_(outValue, sizeof(int32_t), true, ?outvalue0) &*& outvalue0 <= INT_MAX : true); // FIXME: remove INT_MAX?
  @*/
/*@ ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  (outValue != NULL ? integer_(outValue, sizeof(int32_t), true, ?outvalue1) &*& outvalue1 <= INT_MAX : true) &*& // FIXME: remove INT_MAX?
  start_val0 <= start_val1 && implies(result, start_val0 < start_val1);
  @*/

{
    bool ret = false;
    size_t i, saveStart;
    int32_t value = 0;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    saveStart = *start;

    for( i = *start; i < max; i++ )
    //@ invariant chars(buf, max, buf_val) &*& start_val0 <= i &*&  value <= INT_MAX;
    {
        if( !isdigit_( buf[ i ] ) )
        {
            break;
        }

        if( ( outValue != NULL ) && ( value > -1 ) )
        {
            int8_t n = ( int8_t ) hexToInt( buf[ i ] );

            if( value <= 214748353 /* MAX_FACTOR*/ )
            {
                value = ( value * 10 ) + n;
            }
            else
            {
                value = -1;
            }
        }
    }

    if( i > saveStart )
    {
        ret = true;
        *start = i;

        if( outValue != NULL )
        {
            *outValue = value;
        }
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond the decimal portion of a number.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 */
static void skipDecimals( const char * buf,
                          size_t * start,
                          size_t max )
/*@
requires
  buf != NULL && start != NULL && 0 < max &*&
  chars(buf, max, ?buffer) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buffer) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1;
  @*/
{
    size_t i;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    i = *start;

    if( ( i < max ) && ( buf[ i ] == '.' ) )
    {
        i++;

        //@ assume (&i != 0);
        if( skipDigits( buf, &i, max, NULL ) == true )
        {
            *start = i;
        }
    }
}

/**
 * @brief Advance buffer index beyond the exponent portion of a number.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 */
static void skipExponent( const char * buf,
                          size_t * start,
                          size_t max )
/*@
requires
  buf != NULL && start != NULL && 0 < max &*&
  chars(buf, max, ?buffer) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buffer) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1;
  @*/
{
    size_t i;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    i = *start;

    if( ( i < max ) && ( ( buf[ i ] == 'e' ) || ( buf[ i ] == 'E' ) ) )
    {
        i++;

        if( ( i < max ) && ( ( buf[ i ] == '-' ) || ( buf[ i ] == '+' ) ) )
        {
            i++;
        }

        //@ assume(&i != NULL);
        if( skipDigits( buf, &i, max, NULL ) == true )
        {
            *start = i;
        }
    }
}

/**
 * @brief Advance buffer index beyond a number.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid number was present;
 * false otherwise.
 */
static bool skipNumber( const char * buf,
                        size_t * start,
                        size_t max )
/*@
requires
  buf != NULL && start != NULL && max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && implies(result, start_val0 < start_val1);
  @*/
{
    bool ret = false;
    size_t i;
    //@ assume(&i != NULL);

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    i = *start;

    if( ( i < max ) && ( buf[ i ] == '-' ) )
    {
        i++;
    }

    if( i < max )
    {
        /* JSON disallows superfluous leading zeroes, so an
         * initial zero must either be alone, or followed by
         * a decimal or exponent.
         *
         * Should there be a digit after the zero, that digit
         * will not be skipped by this function, and later parsing
         * will judge this an illegal document. */
        if( buf[ i ] == '0' )
        {
            ret = true;
            i++;
        }
        else
        {

            ret = skipDigits( buf, &i, max, NULL );
        }
    }

    if( ret == true )
    {
        skipDecimals( buf, &i, max );
        skipExponent( buf, &i, max );
        *start = i;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond a scalar value.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a scalar value was present;
 * false otherwise.
 */
static bool skipAnyScalar( const char * buf,
                           size_t * start,
                           size_t max )
/*@
requires
  buf != NULL && start !=NULL && 0 < max &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && implies(result, start_val0 < start_val1);
  @*/
{
    bool ret = false;

    if( ( skipString( buf, start, max ) == true ) ||
        ( skipAnyLiteral( buf, start, max ) == true ) ||
        ( skipNumber( buf, start, max ) == true ) )
    {
        ret = true;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond a comma separator
 * and surrounding whitespace.
 *
 * JSON uses a comma to separate values in an array and key-value
 * pairs in an object.  JSON does not permit a trailing comma.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a non-terminal comma was present;
 * false otherwise.
 */
static bool skipSpaceAndComma( const char * buf,
                               size_t * start,
                               size_t max )
/*@
requires
  buf != NULL && start !=NULL && max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && implies(result, start_val0 < start_val1);
  @*/
{
    bool ret = false;
    size_t i;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    skipSpace( buf, start, max );
    i = *start;

    if( ( i < max ) && ( buf[ i ] == ',' ) )
    {
        i++;
        //@ assume (&i != 0);
        skipSpace( buf, &i, max );

        if( ( i < max ) && !isCloseBracket_( buf[ i ] ) )
        {
            ret = true;
            *start = i;
        }
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond the scalar values of an array.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @note Stops advance if a value is an object or array.
 */
static void skipArrayScalars( const char * buf,
                              size_t * start,
                              size_t max )
/*@
requires
  buf != NULL &*& start !=NULL &*& max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1;
  @*/
{
    size_t i;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    i = *start;
    //@ assume(&i != NULL);

    while( i < max )
          //@ invariant chars(buf, max, buf_val) &*& u_integer(&i, ?ival) &*& start_val0 <= ival;
    {
        if( skipAnyScalar( buf, &i, max ) != true )
        {
            break;
        }

        if( skipSpaceAndComma( buf, &i, max ) != true )
        {
            break;
        }
    }

    *start = i;
}

/**
 * @brief Advance buffer index beyond the scalar key-value pairs
 * of an object.
 *
 * In JSON, objects consist of comma-separated key-value pairs.
 * A key is always a string (a scalar) while a value may be a
 * scalar, an object, or an array.  A colon must appear between
 * each key and value.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @note Stops advance if a value is an object or array.
 */
static void skipObjectScalars( const char * buf,
                               size_t * start,
                               size_t max )
/*@
requires
  buf != NULL && start !=NULL && max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1;
  @*/
{
    size_t i;
    bool comma;
    //@ assume(&i != NULL);

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    i = *start;

    while( i < max )
      /*@ invariant chars(buf, max, buf_val) &*&
            integer_(start, sizeof(size_t), false, ?start_val) &*& start !=NULL &*&
            start_val0 <= start_val &*&
            u_integer(&i, ?ival) &*& start_val <= ival;
      @*/
    {
        if( skipString( buf, &i, max ) != true )
        {
            break;
        }

        skipSpace( buf, &i, max );

        if( ( i < max ) && ( buf[ i ] != ':' ) )
        {
            break;
        }

        if (i >= max) break;  // bug?
        i++;
        skipSpace( buf, &i, max );

        if( ( i < max ) && isOpenBracket_( buf[ i ] ) )
        {
            *start = i;
            break;
        }

        if( skipAnyScalar( buf, &i, max ) != true )
        {
            break;
        }

        comma = skipSpaceAndComma( buf, &i, max );
        *start = i;

        if( comma != true )
        {
            break;
        }
    }
}

/**
 * @brief Advance buffer index beyond one or more scalars.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[in] mode  The first character of an array '[' or object '{'.
 */
static void skipScalars( const char * buf,
                         size_t * start,
                         size_t max,
                         char mode )
/*@
requires
  isOpenBracket_( mode ) &&
  buf != NULL && start !=NULL && 0 < max &*&  // bug ?
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1;
  @*/
{
    assert( isOpenBracket_( mode ) );

    skipSpace( buf, start, max );

    if( mode == '[' )
    {
        skipArrayScalars( buf, start, max );
    }
    else
    {
        skipObjectScalars( buf, start, max );
    }
}

/**
 * @brief Advance buffer index beyond a collection and handle nesting.
 *
 * A stack is used to continue parsing the prior collection type
 * when a nested collection is finished.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return #JSONSuccess if the buffer contents are a valid JSON collection;
 * #JSONIllegalDocument if the buffer contents are NOT valid JSON;
 * #JSONMaxDepthExceeded if object and array nesting exceeds a threshold;
 * #JSONPartial if the buffer contents are potentially valid but incomplete.
 */
#ifndef JSON_MAX_DEPTH
    #define JSON_MAX_DEPTH    32
#endif

//@ predicate openbracket(char c) = c == '{' || c == '[';

static JSONStatus_t skipCollection( const char * buf,
                                    size_t * start,
                                    size_t max )
/*@
requires
  buf != NULL && start !=NULL && 0 < max &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && implies (result == JSONSuccess, start_val0 < start_val1);
  @*/
{
    JSONStatus_t ret = JSONPartial;
    char c, stack[ JSON_MAX_DEPTH ];
    int16_t depth = -1;
    size_t i;
    //@ assume(&i != NULL);

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );
    assert( ret == JSONPartial );

    i = *start;
    while( i < max )
      /*@ invariant chars(buf, max, buf_val) &*& u_integer(&i, ?ival) &*& start_val0 <= ival &*& -1 <= depth &*& depth < JSON_MAX_DEPTH
        &*& chars(stack, JSON_MAX_DEPTH, ?stack_val) &*& forall_(size_t idx; !(0 <= idx && idx <= depth) || isOpenBracket_(nth(idx,stack_val))) &*&
        (ival != start_val0 || ret == JSONPartial);
        @*/

    {
        c = buf[ i ];
        i++;

        switch( c )
        {
            case '{':
            case '[':
                depth++;

                if( depth == JSON_MAX_DEPTH )
                {
                    ret = JSONMaxDepthExceeded;

                    break;
                }
                stack[ depth ] = c;
                skipScalars( buf, &i, max, stack[ depth ] );
                break;

            case '}':
            case ']':

                if( ( depth > 0 ) && isMatchingBracket_( stack[ depth ], c ) )
                {
                    depth--;

                    if( skipSpaceAndComma( buf, &i, max ) == true )
                    {
                        skipScalars( buf, &i, max, stack[ depth ] );
                    }

                    break;
                }

                ret = ( depth == 0 ) ? JSONSuccess : JSONIllegalDocument;
                break;

            default:
                ret = JSONIllegalDocument;
                break;
        }

        if( ret != JSONPartial )
        {

            break;
        }
    }

    if( ret == JSONSuccess )
    {
        *start = i;
    }

    return ret;

}

/** @endcond */

/**
 * See core_json.h for docs.
 *
 * Verify that the entire buffer contains exactly one scalar
 * or collection within optional whitespace.
 */
JSONStatus_t JSON_Validate( const char * buf,
                            size_t max )
//@ requires chars(buf, max, ?buf_val);
//@ ensures  chars(buf, max, buf_val);
{
    JSONStatus_t ret;
    size_t i = 0;
    //@ assume(&i != NULL);

    if( buf == NULL )
    {
        ret = JSONNullParameter;
    }
    else if( max == 0U )
    {
        ret = JSONBadParameter;
    }
    else
    {
        skipSpace( buf, &i, max );

        /** @cond DO_NOT_DOCUMENT */
        #ifndef JSON_VALIDATE_COLLECTIONS_ONLY
            if( skipAnyScalar( buf, &i, max ) == true )
            {
                ret = JSONSuccess;
            }
            else
        #endif
        /** @endcond */
        {
            ret = skipCollection( buf, &i, max );
        }
    }

    if( ( ret == JSONSuccess ) && ( i < max ) )
    {
        skipSpace( buf, &i, max );

        if( i != max )
        {
            ret = JSONIllegalDocument;
        }
    }

    return ret;
}

/** @cond DO_NOT_DOCUMENT */

/**
 * @brief Output index and length for the next value.
 *
 * Also advances the buffer index beyond the value.
 * The value may be a scalar or a collection.
 * The start index should point to the beginning of the value.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[out] value  A pointer to receive the index of the value.
 * @param[out] valueLength  A pointer to receive the length of the value.
 *
 * @return true if a value was present;
 * false otherwise.
 */
static bool nextValue( const char * buf,
                       size_t * start,
                       size_t max,
                       size_t * value,
                       size_t * valueLength )
/*@
requires
  buf != NULL && start != NULL && max > 0 && value != NULL && valueLength != NULL &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  integer_(value, sizeof(size_t), false, _) &*&
  integer_(valueLength, sizeof(size_t), false, _) &*&
  0 <= start_val0;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  integer_(value, sizeof(size_t), false, _) &*&
  integer_(valueLength, sizeof(size_t), false, _) &*&
  start_val0 <= start_val1 && implies(result, start_val0 < start_val1);
  @*/
{
    bool ret = true;
    size_t i, valueStart;
    //@ assume(&i != NULL);

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );
    assert( ( value != NULL ) && ( valueLength != NULL ) );

    i = *start;
    valueStart = i;

    bool scalar_result = skipAnyScalar( buf, &i, max );
    int collection_result = skipCollection( buf, &i, max );
    if( ( scalar_result == true ) ||
        ( collection_result == JSONSuccess ) )
    {
        *value = valueStart;
        // Verifast needs to know i <= SIZE_MAX to avoid integer overflow
        //@ close u_integer(&i, ?val);
        //@ produce_limits(i);
        *valueLength = i - valueStart;
    }
    else
    {
        ret = false;
    }

    if( ret == true )
    {
        *start = i;
    }

    return ret;
}

/**
 * @brief Output indexes for the next key-value pair of an object.
 *
 * Also advances the buffer index beyond the key-value pair.
 * The value may be a scalar or a collection.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[out] key  A pointer to receive the index of the key.
 * @param[out] keyLength  A pointer to receive the length of the key.
 * @param[out] value  A pointer to receive the index of the value.
 * @param[out] valueLength  A pointer to receive the length of the value.
 *
 * @return true if a key-value pair was present;
 * false otherwise.
 */
static bool nextKeyValuePair( const char * buf,
                              size_t * start,
                              size_t max,
                              size_t * key,
                              size_t * keyLength,
                              size_t * value,
                              size_t * valueLength )
{
    bool ret = true;
    size_t i, keyStart;

    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );
    assert( ( key != NULL ) && ( keyLength != NULL ) );
    assert( ( value != NULL ) && ( valueLength != NULL ) );

    i = *start;
    keyStart = i;

    if( skipString( buf, &i, max ) == true )
    {
        *key = keyStart + 1U;
        *keyLength = i - keyStart - 2U;
    }
    else
    {
        ret = false;
    }

    if( ret == true )
    {
        skipSpace( buf, &i, max );

        if( ( i < max ) && ( buf[ i ] == ':' ) )
        {
            i++;
            skipSpace( buf, &i, max );
        }
        else
        {
            ret = false;
        }
    }

    if( ret == true )
    {
        ret = nextValue( buf, &i, max, value, valueLength );
    }

    if( ret == true )
    {
        *start = i;
    }

    return ret;
}

/**
 * @brief Find a key in a JSON object and output a pointer to its value.
 *
 * @param[in] buf  The buffer to search.
 * @param[in] max  size of the buffer.
 * @param[in] query  The object keys and array indexes to search for.
 * @param[in] queryLength  Length of the key.
 * @param[out] outValue  A pointer to receive the index of the value found.
 * @param[out] outValueLength  A pointer to receive the length of the value found.
 *
 * Iterate over the key-value pairs of an object, looking for a matching key.
 *
 * @return true if the query is matched and the value output;
 * false otherwise.
 *
 * @note Parsing stops upon finding a match.
 */
static bool objectSearch( const char * buf,
                          size_t max,
                          const char * query,
                          size_t queryLength,
                          size_t * outValue,
                          size_t * outValueLength )
{
    bool ret = false;

    size_t i = 0, key, keyLength, value = 0, valueLength = 0;

    assert( ( buf != NULL ) && ( query != NULL ) );
    assert( ( outValue != NULL ) && ( outValueLength != NULL ) );

    skipSpace( buf, &i, max );

    if( ( i < max ) && ( buf[ i ] == '{' ) )
    {
        i++;
        skipSpace( buf, &i, max );

        while( i < max )
        {
            if( nextKeyValuePair( buf, &i, max, &key, &keyLength,
                                  &value, &valueLength ) != true )
            {
                break;
            }

            if( ( queryLength == keyLength ) &&
                ( strnEq( query, &buf[ key ], keyLength ) == true ) )
            {
                ret = true;
                break;
            }

            if( skipSpaceAndComma( buf, &i, max ) != true )
            {
                break;
            }
        }
    }

    if( ret == true )
    {
        *outValue = value;
        *outValueLength = valueLength;
    }

    return ret;
}

/**
 * @brief Find an index in a JSON array and output a pointer to its value.
 *
 * @param[in] buf  The buffer to search.
 * @param[in] max  size of the buffer.
 * @param[in] queryIndex  The index to search for.
 * @param[out] outValue  A pointer to receive the index of the value found.
 * @param[out] outValueLength  A pointer to receive the length of the value found.
 *
 * Iterate over the values of an array, looking for a matching index.
 *
 * @return true if the queryIndex is found and the value output;
 * false otherwise.
 *
 * @note Parsing stops upon finding a match.
 */
static bool arraySearch( const char * buf,
                         size_t max,
                         uint32_t queryIndex,
                         size_t * outValue,
                         size_t * outValueLength )
/*@
requires
  buf != NULL && outValue != NULL && outValueLength != NULL &*&
  max > 0 &*& // bug?
  chars(buf, max, ?buf_val) &*&
  integer_(outValue, sizeof(size_t), false, ?outvalue) &*&
  integer_(outValueLength, sizeof(size_t), false, ?outvaluelength);
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(outValue, sizeof(size_t), false, _) &*&
  integer_(outValueLength, sizeof(size_t), false, _);
  @*/
{
    bool ret = false;
    size_t i = 0, value = 0, valueLength = 0;
    uint32_t currentIndex = 0;
    //@ assume(&i != NULL);
    //@ assume(&value != NULL);
    //@ assume(&valueLength != NULL);

    assert( buf != NULL );
    assert( ( outValue != NULL ) && ( outValueLength != NULL ) );

    skipSpace( buf, &i, max );

    if( ( i < max ) && ( buf[ i ] == '[' ) )
    {
        i++;
        skipSpace( buf, &i, max );

        while( i < max )
          /*@ invariant
              chars(buf, max, buf_val) &*&
              u_integer(&i, ?ival) &*&
              u_integer(&value, _) &*&
              u_integer(&valueLength, _) &*&
              0 <= ival && currentIndex <= queryIndex;
          @*/

        {
            if( nextValue( buf, &i, max, &value, &valueLength ) != true )
            {
                break;
            }

            if( currentIndex == queryIndex )
            {
                ret = true;
                break;
            }

            if( skipSpaceAndComma( buf, &i, max ) != true )
            {
                break;
            }

            currentIndex++;
        }
    }

    if( ret == true )
    {
        *outValue = value;
        *outValueLength = valueLength;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond a query part.
 *
 * The part is the portion of the query which is not
 * a separator or array index.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[out] outLength  The length of the query part.
 *
 * @return true if a valid string was present;
 * false otherwise.
 */
#ifndef JSON_QUERY_KEY_SEPARATOR
    #define JSON_QUERY_KEY_SEPARATOR    '.'
#endif
#define isSeparator_( x )    ( ( x ) == JSON_QUERY_KEY_SEPARATOR )
static bool skipQueryPart( const char * buf,
                           size_t * start,
                           size_t max,
                           size_t * outLength )
{
    bool ret = false;
    size_t i;

    assert( ( buf != NULL ) && ( start != NULL ) && ( outLength != NULL ) );
    assert( max > 0U );

    i = *start;

    while( ( i < max ) &&
           !isSeparator_( buf[ i ] ) &&
           !isSquareOpen_( buf[ i ] ) )
    {
        i++;
    }

    if( i > *start )
    {
        ret = true;
        *outLength = i - *start;
        *start = i;
    }

    return ret;
}

/**
 * @brief Handle a nested search by iterating over the parts of the query.
 *
 * @param[in] buf  The buffer to search.
 * @param[in] max  size of the buffer.
 * @param[in] query  The object keys and array indexes to search for.
 * @param[in] queryLength  Length of the key.
 * @param[out] outValue  A pointer to receive the index of the value found.
 * @param[out] outValueLength  A pointer to receive the length of the value found.
 *
 * @return #JSONSuccess if the query is matched and the value output;
 * #JSONBadParameter if the query is empty, or any part is empty,
 * or an index is too large to convert;
 * #JSONNotFound if the query is NOT found.
 *
 * @note Parsing stops upon finding a match.
 */
static JSONStatus_t multiSearch( const char * buf,
                                 size_t max,
                                 const char * query,
                                 size_t queryLength,
                                 size_t * outValue,
                                 size_t * outValueLength )
#if 0
/*@
requires
  chars(buf, max, ?buf_val) &*& buf != NULL &*&
  0 < max &*&
  chars(query, max, ?query_val) &*& query != NULL &*&
  0 < queryLength &*&
  queryLength <= max &*&
  integer_(outValue, sizeof(size_t), false, ?outvalue) &*& outValue != NULL &*&
  integer_(outValueLength, sizeof(size_t), false, ?outvaluelength) &*& outValueLength != NULL;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  chars(query, max, query_val) &*&
  integer_(outValue, sizeof(size_t), false, _) &*&
  integer_(outValueLength, sizeof(size_t), false, _);
  @*/
#endif
{
    JSONStatus_t ret = JSONSuccess;
    size_t i = 0, start = 0, queryStart = 0, value = 0, length = max;
    //@ assume(&i != NULL);

    assert( ( buf != NULL ) && ( query != NULL ) );
    assert( ( outValue != NULL ) && ( outValueLength != NULL ) );
    assert( ( max > 0U ) && ( queryLength > 0U ) );
    assert( queryLength <= max );

    while( i < queryLength )
      /*@ invariant
        chars(buf, max, buf_val) &*&
        chars(query, max, query_val) &*&
        integer_(&i, sizeof(size_t), false, ?ival) &*& 0 <= ival &*& ival <= queryLength &*&
        integer_(&length, sizeof(size_t), false, ?length_val) &*& 0 <= length_val &*& length_val <= max &*&
        start < max;
      @*/
    {
        bool found = false;

        if( isSquareOpen_( query[ i ] ) )
        {
            int32_t queryIndex = -1;
            i++;
            //@ assume(&queryIndex != NULL);

            skipDigits( query, &i, queryLength, &queryIndex );

            if( ( queryIndex < 0 ) ||
                ( i >= queryLength ) || !isSquareClose_( query[ i ] ) )
            {
                ret = JSONBadParameter;
                break;
            }

            i++;

            //@ chars_split(buf, start);
            //@ chars_split(buf + start, length);
            found = arraySearch( &buf[ start ], length, ( uint32_t ) queryIndex, &value, &length );
            //@ chars_join(buf, start);
        }
        else
        {
            size_t keyLength = 0;

            queryStart = i;

            if( ( skipQueryPart( query, &i, queryLength, &keyLength ) != true ) ||
                /* catch an empty key part or a trailing separator */
                ( i == ( queryLength - 1U ) ) )
            {
                ret = JSONBadParameter;
                break;
            }

            found = objectSearch( &buf[ start ], length, &query[ queryStart ], keyLength, &value, &length );
        }

        if( found == false )
        {
            ret = JSONNotFound;
            break;
        }

        start += value;

        if( ( i < queryLength ) && isSeparator_( query[ i ] ) )
        {
            i++;
        }
    }

    if( ret == JSONSuccess )
    {
        *outValue = start;
        *outValueLength = length;
    }

    return ret;
}

/**
 * @brief Return a JSON type based on a separator character or
 * the first character of a value.
 *
 * @param[in] c  The character to classify.
 *
 * @return an enum of JSONTypes_t
 */
static JSONTypes_t getType( char c )
{
    JSONTypes_t t;

    switch( c )
    {
        case '"':
            t = JSONString;
            break;

        case '{':
            t = JSONObject;
            break;

        case '[':
            t = JSONArray;
            break;

        case 't':
            t = JSONTrue;
            break;

        case 'f':
            t = JSONFalse;
            break;

        case 'n':
            t = JSONNull;
            break;

        default:
            t = JSONNumber;
            break;
    }

    return t;
}

/** @endcond */

/**
 * See core_json.h for docs.
 */
JSONStatus_t JSON_SearchConst( const char * buf,
                               size_t max,
                               const char * query,
                               size_t queryLength,
                               const char ** outValue,
                               size_t * outValueLength,
                               JSONTypes_t * outType )
#if 0
/*@
requires
  chars(buf, max, ?buf_val) &*& buf != NULL &*&
  0 <= max &*&
  chars(query, max, ?query_val) &*& query != NULL &*&
  0 <= queryLength &*&
  pointer(outValue, _) &*&
  integer_(outValueLength, sizeof(size_t), false, ?outvaluelength) &*&
  integer_(outType, sizeof(JSONTypes_t), false, ?outtype);
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  chars(query, max, query_val) &*&
  pointer(outValue, _) &*&
  integer_(outValueLength, sizeof(size_t), false, _) &*&
  integer_(outType, sizeof(JSONTypes_t), false, _);
  @*/
#endif
{
    JSONStatus_t ret;
    size_t value = 0U;

    if( ( buf == NULL ) || ( query == NULL ) ||
        ( outValue == NULL ) || ( outValueLength == NULL ) )
    {
        ret = JSONNullParameter;
    }
    else if( ( max == 0U ) || ( queryLength == 0U ) )
    {
        ret = JSONBadParameter;
    }
    else
    {
        ret = multiSearch( buf, max, query, queryLength, &value, outValueLength );
    }

    if( ret == JSONSuccess )
    {
        JSONTypes_t t = getType( buf[ value ] );

        if( t == JSONString )
        {
            /* strip the surrounding quotes */
            value++;
            *outValueLength -= 2U;
        }

        *outValue = &buf[ value ];

        if( outType != NULL )
        {
            *outType = t;
        }
    }

    return ret;
}

/**
 * See core_json.h for docs.
 */
JSONStatus_t JSON_SearchT( char * buf,
                           size_t max,
                           const char * query,
                           size_t queryLength,
                           char ** outValue,
                           size_t * outValueLength,
                           JSONTypes_t * outType )
{
    /* MISRA Rule 11.3 prohibits casting a pointer to a different type.
     * This instance is a false positive, as the rule permits the
     * addition of a type qualifier. */
    /* coverity[misra_c_2012_rule_11_3_violation] */
    return JSON_SearchConst( ( const char * ) buf, max, query, queryLength,
                             ( const char ** ) outValue, outValueLength, outType );
}

/** @cond DO_NOT_DOCUMENT */

/**
 * @brief Output the next key-value pair or value from a collection.
 *
 * @param[in] buf  The buffer to search.
 * @param[in] max  size of the buffer.
 * @param[in] start  The index at which the collection begins.
 * @param[in,out] next  The index at which to seek the next value.
 * @param[out] outKey  A pointer to receive the index of the value found.
 * @param[out] outKeyLength  A pointer to receive the length of the value found.
 * @param[out] outValue  A pointer to receive the index of the value found.
 * @param[out] outValueLength  A pointer to receive the length of the value found.
 *
 * @return #JSONSuccess if a value is output;
 * #JSONIllegalDocument if the buffer does not begin with '[' or '{';
 * #JSONNotFound if there are no further values in the collection.
 */
static JSONStatus_t iterate( const char * buf,
                             size_t max,
                             size_t * start,
                             size_t * next,
                             size_t * outKey,
                             size_t * outKeyLength,
                             size_t * outValue,
                             size_t * outValueLength )
{
    JSONStatus_t ret = JSONNotFound;
    bool found = false;

    assert( ( buf != NULL ) && ( max > 0U ) );
    assert( ( start != NULL ) && ( next != NULL ) );
    assert( ( outKey != NULL ) && ( outKeyLength != NULL ) );
    assert( ( outValue != NULL ) && ( outValueLength != NULL ) );

    if( *start < max )
    {
        switch( buf[ *start ] )
        {
            case '[':
                found = nextValue( buf, next, max, outValue, outValueLength );

                if( found == true )
                {
                    *outKey = 0;
                    *outKeyLength = 0;
                }

                break;

            case '{':
                found = nextKeyValuePair( buf, next, max, outKey, outKeyLength,
                                          outValue, outValueLength );
                break;

            default:
                ret = JSONIllegalDocument;
                break;
        }
    }

    if( found == true )
    {
        ret = JSONSuccess;
        ( void ) skipSpaceAndComma( buf, next, max );
    }

    return ret;
}

/** @endcond */

/**
 * See core_json.h for docs.
 */
JSONStatus_t JSON_Iterate( const char * buf,
                           size_t max,
                           size_t * start,
                           size_t * next,
                           JSONPair_t * outPair )
{
    JSONStatus_t ret;
    size_t key, keyLength, value, valueLength;

    if( ( buf == NULL ) || ( start == NULL ) || ( next == NULL ) ||
        ( outPair == NULL ) )
    {
        ret = JSONNullParameter;
    }
    else if( ( max == 0U ) || ( *start >= max ) || ( *next > max ) )
    {
        ret = JSONBadParameter;
    }
    else
    {
        skipSpace( buf, start, max );

        if( *next <= *start )
        {
            *next = *start + 1U;
            skipSpace( buf, next, max );
        }

        ret = iterate( buf, max, start, next, &key, &keyLength,
                       &value, &valueLength );
    }

    if( ret == JSONSuccess )
    {
        JSONTypes_t t = getType( buf[ value ] );

        if( t == JSONString )
        {
            /* strip the surrounding quotes */
            value++;
            valueLength -= 2U;
        }

        outPair->key = ( key == 0U ) ? NULL : &buf[ key ];
        outPair->keyLength = keyLength;
        outPair->value = &buf[ value ];
        outPair->valueLength = valueLength;
        outPair->jsonType = t;
    }

    return ret;
}
