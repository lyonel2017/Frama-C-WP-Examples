/*@ axiomatic Fact {
     predicate isFact(integer n, integer fact);
     axiom Fact_1: isFact(0,1);
     axiom Fact_2: \forall integer n,r1; n > 0 ==> isFact(n-1,r1)
                                              ==> isFact(n,n*r1);
}
*/

/*@ requires n >= 0;
  @ ensures isFact(n,\result);
*/
int fact (int n) {
  int y = 1;
  int x = n;
  /*@ loop invariant 0 <= x <= n;
    @ loop invariant \forall integer r1; isFact(x,r1) ==> isFact(n,y*r1);
    @ loop assigns y,x;
    @ loop variant x;*/
  while (x > 1) {
    y = y * x;
    x = x - 1;
  };
  return y;
}
