//@ #include <bitops.gh>

int main ()
//@ requires true;
//@ ensures true;
{
  int a = 0x000000F0;
  //@ Z za = Z_of_uint32(a);
  int b = 0x0000000F;
  //@ Z zb = Z_of_uint32(b);
  int c = a | b;
  //@ bitor_def(a, za, b, zb);
  assert( c <= 0x000000FF);

  return 0;
}
