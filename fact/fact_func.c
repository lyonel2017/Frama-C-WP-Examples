/*@ axiomatic Fact {
     logic integer fact(integer n);
     axiom Fact_1: fact(0) == 1;
     axiom Fact_2: \forall integer n; n > 0 ==> fact(n-1)*n == fact(n);
}
*/

/*@ requires n >= 0;
  @ ensures fact(n) == \result;
*/
int fact (int n) {
  int y = 1;
  int x = n;
  /*@ loop invariant 0 <= x <= n;
    @ loop invariant fact(x) * y == fact(n);
    @ loop assigns y,x;
    @ loop variant x;*/
  while (x > 1) {
    y = y * x;
    x = x - 1;
  };
  return y;
}
