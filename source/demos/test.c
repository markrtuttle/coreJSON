#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>

int main()
//@ requires true;
//@ ensures true;
{
  int8_t s = (int8_t) -1;
  uint8_t u = (uint8_t) s;

  assert( u == 0xFFU );

  return 0;
}
