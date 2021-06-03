//@ #include <bitops.gh>

int main ()
//@ requires true;
//@ ensures true;
{
  char stack[ 4 ];

  //@ assert chars(stack, 4, ?stack_before);
  stack[2] = 0;
  //@ assert chars(stack, 4, ?stack_after);
  //@ assert nth(0, stack_before) == nth(0, stack_after);
  //@ assert nth(1, stack_before) == nth(1, sstack_after);
  //@ assert take(1, stack_before) == take(1, stack_after);

  return 0;
}
