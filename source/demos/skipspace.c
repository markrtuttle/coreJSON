#include <assert.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include "core_json.h"

/** @cond DO_NOT_DOCUMENT */

//@ #include <bitops.gh>

#define isspace_( x )                          \
    ( ( ( x ) == ' ' ) || ( ( x ) == '\t' ) || \
      ( ( x ) == '\n' ) || ( ( x ) == '\r' ) )

#define implies(a,b) (!(a) || (b))

static void skipSpace( const char * buf,
                       size_t * start,
                       size_t max )
/*@
requires
  buf != NULL && start !=NULL && max > 0 &*&
  chars(buf, max, ?buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val0) &*&
  0 <= start_val0 && start_val0 < max;
  @*/
/*@
ensures
  chars(buf, max, buf_val) &*&
  integer_(start, sizeof(size_t), false, ?start_val1) &*&
  start_val0 <= start_val1 && start_val1 <= max;
  @*/
{
    size_t i;
    assert( ( buf != NULL ) && ( start != NULL ) && ( max > 0U ) );

    for( i = *start; i < max; i++ )
    /*@ invariant
          chars(buf, max, buf_val) &*&
          integer_(start, sizeof(size_t), false, start_val0) &*&
          integer_(&i, sizeof(size_t), false, ?i_val) &*&
          start_val0 <= i_val && i_val <= max;
    @*/
    {
        if( !isspace_( buf[ i ] ) )
        {
            break;
        }
    }
    *start = i;
}
