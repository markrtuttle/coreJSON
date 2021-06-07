#include <stddef.h>
#include <stdint.h>

static size_t countHighBits( uint8_t c )
{
  uint8_t n = c;
  size_t i = 0;

  while( ( n & 0x80U ) != 0U )
  {
    i++;
    n = ( n & 0x7FU ) << 1U;
  }

  return i;
}
