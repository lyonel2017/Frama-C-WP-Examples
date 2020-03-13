/*@ predicate sorted(int* tab, integer idx) =
    \forall integer x,y; 0 <= x < y < idx ==> tab[x] <= tab[y]; */

/*@ predicate swap{L1, L2}(int *a, int *b, integer begin, integer i, integer j, integer end) =
      begin <= i < end && begin <= j < end &&
      \at(a[i], L1) == \at(b[j], L2) &&
      \at(a[j], L1) == \at(b[i], L2) &&
      \forall integer k; begin <= k < end && k != i && k != j ==> \at(a[k], L1) == \at(b[k], L2);
*/

/*@ predicate same_array{L1,L2}(int *a, int *b, integer begin, integer end) =
      \forall integer k; begin <= k < end ==> \at(a[k],L1) == \at(b[k],L2);
*/

/*@ inductive same_elements{L1, L2}(int *a, int *b, integer begin, integer end) {
      case refl{L1, L2}:
        \forall int *a, int *b, integer begin, end;
        same_array{L1,L2}(a, b, begin, end) ==>
        same_elements{L1, L2}(a, b, begin, end);
      case swap{L1, L2}: \forall int *a, int *b, integer begin, i, j, end;
        swap{L1, L2}(a, b, begin, i, j, end) ==>
        same_elements{L1, L2}(a, b, begin, end);
      case trans{L1, L2, L3}: \forall int* a, int *b, int *c, integer begin, end;
        same_elements{L1, L2}(a, b, begin, end) ==>
        same_elements{L2, L3}(b, c, begin, end) ==>
        same_elements{L1, L3}(a, c, begin, end);
}*/


/*@ predicate is_min(int* tab, integer a, integer b, integer min) =
      (\forall integer k; a <= k <= b ==> tab[min] <= tab[k]);*/

/*@ requires 0 <= a <= b;
    requires \valid(tab+(a..b));
    assigns \nothing;
    ensures is_min(tab,a,b,\result);
    ensures a <= \result <= b;
*/
int find_min(int tab[], int a, int b){
  int min = a, i;
  /*@ loop invariant a <= i <= b+1;
      loop invariant a <= min <= b;
      loop invariant is_min(tab,a,i-1,min);
      loop assigns min, i;
      loop variant b - i;
   */
  for(i = a; i <= b; i++){
    if(tab[i] < tab[min]) min = i;
  }
  return min;
}

/*@ requires \valid(x) && \valid(y);
    requires \separated(x,y);
    ensures *x == \old(*y) && *y == \old(*x);
    assigns *x,*y;*/
void swap(int *x, int *y){
  int t = *x;
  * x = *y;
  *y = t;
}

/*@ requires 0 <= n;
    requires \valid(tab+(0..n));
    ensures sorted(tab,n+1);
    ensures same_elements{Pre,Post}(tab,tab,0,n+1);
    assigns tab[0..n];*/
void select_sort(int tab[], int n){
  int i, min;
  /*@ loop invariant 0 <= i <= n+1;
      loop invariant \forall int j,k; 0 <= j < i <= k < n+1 ==> tab[j] <= tab[k];
      loop invariant sorted(tab,i);
      loop invariant same_elements{Pre,Here}(tab,tab,0,n+1);
      loop assigns i, tab[0..n], min;
      loop variant (n+1) -i;
*/
  for (i = 0; i <= n; i++){
    min = find_min(tab,i,n);
    if(min != i) {
    l1:swap(tab+i, tab+min);
      /*@ assert swap{l1,Here}(tab,tab,0,i,min,n+1);*/
    }
  }
  return;
}
