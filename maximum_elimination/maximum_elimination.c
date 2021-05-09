/* http://www.verifythis.org/post?pid=maximum-in-an-array-by-elimination- */

/*@ requires n > 0;
  @ requires \valid_read(a+(0..n-1));
  @ assigns \nothing;
  @ ensures 0 <= \result < n;
  @ ensures \forall integer i; 0 <= i < n ==> a[i] <= a[\result];
*/
int max(int *a, int n) {
  int x = 0;
  int y = n-1;

  /*@ loop invariant 0 <= x <= y <= n - 1;
    @ loop invariant (\forall integer i; 0 <= i < x || y < i < n ==> a[i] <= a[x])
                  || (\forall integer i; 0 <= i < x || y < i < n ==> a[i] <= a[y]);
    @ loop assigns x, y;
    @ loop variant y-x;
  */
  while (x != y) {
      if (a[x] <= a[y]) x++;
          else y--;
  }
  return x;
}
