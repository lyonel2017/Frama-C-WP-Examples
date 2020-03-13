/*@ predicate HasValue{A}(int *a, integer m, integer n, integer v) = 
      \exists int i; m <= i < n && a[i] == v;
*/

/*@ predicate HasValue{A}(int *a, integer n, integer v) =
      HasValue(a, 0, n, v);
*/

/*@ predicate HasValueOf{A}(int *a, int m, int *b, int n) =
      \exists integer i; 0 <= i < m && HasValue{A}(b, n, a[i]);
*/

/*@ requires \valid(t+(0 .. n-1));
  @ requires n >= 0;
  @ assigns \nothing;
  @ behavior some:
	assumes HasValue(t, n, val);
	ensures bound: 0 <= \result < n;
	ensures result: t[\result] == val;
	ensures first: !HasValue(t, \result, val);
  @ behavior none:
	assumes !HasValue(t, n, val);
	ensures result: \result == n;
  @ complete behaviors;
  @ disjoint behaviors;
*/
int find(int * t, int n, int val){
	int i = 0;
	
	/*@ loop invariant bound: 0 <= i <= n;
	  @ loop invariant not_found: !HasValue(t,i,val);
	  @ loop assigns i;
	  @ loop variant n-i;
	*/
	for(i = 0; i < n; i++){
		if(t[i] == val){
			return i;		
		}
	}
	return n;
}


/*@ requires \valid(a+(0 .. m-1));
  @ requires \valid(b+(0 .. n-1));
  @ requires n >= 0;
  @ requires m >= 0;
  @ assigns \nothing;
  @ behavior found:
	assumes HasValueOf(a, m, b, n);
	ensures bound: 0 <= \result < m;
	ensures result: HasValue(b, n, a[\result]);
	ensures first: !HasValueOf(a, \result, b, n);
  @ behavior not_found:
	assumes !HasValueOf(a, m, b, n);
	ensures result: \result == m;
  @ complete behaviors;
  @ disjoint behaviors;
*/
int find_first_of(int *a, int m, int *b, int n){
  int i = 0;
  
  /*@ loop invariant bound: 0 <= i <= m;
    @ loop invariant not_found: !HasValueOf(a, i, b, n);
    @ loop assigns i;
    @ loop variant m-i;
   */
  for(int i = 0; i < m; i++){
    if(find(b, n, a[i]) < n){
      return i;
    }
  }
  return m;
}
