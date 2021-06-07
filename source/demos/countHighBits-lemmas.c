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
  return int_of_Z( take_low_bits( push_low_bits(bits, nat_of_int(count), false), 8) );
}

lemma void test()
  requires true;
  ensures true;
{
  Z z_value = Z_of_uint8(0x01U);

  Z push1 = push_low_bits(z_value, nat_of_int(1), false);
  assert 0x02U == int_of_Z(push1);

  push1 = push_low_bits(z_value, nat_of_int(2), false);
  assert 0x04U == int_of_Z(push1);

  push1 = push_low_bits(z_value, nat_of_int(3), false);
  assert 0x08U == int_of_Z(push1);

  push1 = push_low_bits(z_value, nat_of_int(4), false);
  assert 0x10U == int_of_Z(push1);

  push1 = push_low_bits(z_value, nat_of_int(5), false);
  assert 0x20U == int_of_Z(push1);

  push1 = push_low_bits(z_value, nat_of_int(6), false);
  assert 0x40U == int_of_Z(push1);

  push1 = push_low_bits(z_value, nat_of_int(7), false);
  assert 0x80U == int_of_Z(push1);

  push1 = push_low_bits(z_value, nat_of_int(8), false);
  assert 0x100U == int_of_Z(push1);

}

lemma void test2()
  requires true;
  ensures true;
{
  Z z_value = Z_of_uint16(0xFFFFU);

  Z take1 = take_low_bits(z_value, (0));
  assert 0x00U == int_of_Z(take1);


  take1 = take_low_bits(z_value, (1));
  assert 0x01U == int_of_Z(take1);

  take1 = take_low_bits(z_value, (2));
  assert 0x03U == int_of_Z(take1);

  take1 = take_low_bits(z_value, (3));
  assert 0x07U == int_of_Z(take1);

  take1 = take_low_bits(z_value, (4));
  assert 0x0FU == int_of_Z(take1);

  take1 = take_low_bits(z_value, (5));
  assert 0x1FU == int_of_Z(take1);

  take1 = take_low_bits(z_value, (6));
  assert 0x3FU == int_of_Z(take1);

  take1 = take_low_bits(z_value, (7));
  assert 0x7FU == int_of_Z(take1);

  take1 = take_low_bits(z_value, (8));
  assert 0xFFU == int_of_Z(take1);

  take1 = take_low_bits(z_value, (12));
  assert 0xFFFU == int_of_Z(take1);


}

lemma void test3()
  requires true;
  ensures true;
{
  Z z_value = Z_of_uint8(0xFFU);

  uint8_t take1 = shift_left(z_value, (0));
  assert 0xFFU == (take1);

  take1 = shift_left(z_value, (1));
  assert 0xFEU == (take1);

  take1 = shift_left(z_value, (2));
  assert 0xFCU == (take1);

  take1 = shift_left(z_value, (3));
  assert 0xF8U == (take1);

  take1 = shift_left(z_value, (4));
  assert 0xF0U == (take1);

  take1 = shift_left(z_value, (5));
  assert 0xE0U == (take1);

  take1 = shift_left(z_value, (6));
  assert 0xC0U == (take1);

  take1 = shift_left(z_value, (7));
  assert 0x80U == (take1);

  take1 = shift_left(z_value, (8));
  assert 0x00U == (take1);



}


@*/
