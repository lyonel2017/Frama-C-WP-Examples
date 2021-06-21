// https://www.cs.virginia.edu/luther/DMT1/S2020/bubble.html

/*@ predicate sorted(int* tab, integer begin, integer end) = \forall integer x,y; begin <= x < y < end ==> tab[x] <= tab[y]; */

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

/*@ requires \valid(x) && \valid(y);
   requires \separated(x,y);
   ensures *x == \old(*y) && *y == \old(*x);
   assigns *x,*y;*/
void swap(int *x, int *y){
  int t = *x;
  * x = *y;
  *y = t;
}

/*@ predicate biggers(int* tab, integer begin, integer end, integer i) = \forall integer x,y; begin <= x < i && i <= y < end  ==> tab[x] <= tab[y];*/

/*@ requires 1 < n;
    requires \valid(list+(0..n-1));
    assigns list[0..n-1];
    ensures sorted: sorted(list,0, n);
    ensures same_elements: same_elements{Pre, Post}(list, list, 0, n);
*/
void bubblesort (int list[], int n) {
  int sorted = 0;

  /*@ ghost int  maximal_fixed_tail = n;*/


  /*@ loop invariant 0 <= sorted <= 1;
    @ loop invariant same_elements{Pre, Here}(list,list,0,n);
    @ loop invariant sorted(list,maximal_fixed_tail,n);
    @ loop invariant 0 <= maximal_fixed_tail <= n;
    @ loop invariant biggers(list,0,n,maximal_fixed_tail);
    @ loop invariant sorted == 1 ==> maximal_fixed_tail == 0;
    @ loop invariant sorted == 0 ==> maximal_fixed_tail > 0;
    @ loop assigns sorted,list[0..n-1], maximal_fixed_tail;
    @ loop variant maximal_fixed_tail;
  */
  while(!sorted) {
    sorted=1;
  /*@ ghost int idx = 0;*/

    /*@ loop invariant 0 <= sorted <= 1;
      @ loop invariant 0 <= i <=  n-1;
      @ loop invariant same_elements{Pre, Here}(list,list, 0, n);
      @ loop invariant \forall integer k; 0 <= k < i ==> list[k] <= list[i];
      @ loop invariant \forall integer k; idx <= k < i ==> list[k] <= list[i];
      @ loop invariant biggers(list,0,n,maximal_fixed_tail);
      @ loop invariant sorted(list,maximal_fixed_tail,n);
      @ loop invariant biggers(list,0,i,idx);
      @ loop invariant sorted(list,idx,i);
      @ loop invariant sorted == 1 <==> idx == 0;
      @ loop invariant sorted == 0 <==> idx != 0;
      @ loop invariant 0 <= idx <= i+1;
      @ loop invariant idx < maximal_fixed_tail || idx == maximal_fixed_tail == 0;
      @ loop assigns i, list[0..n-1], sorted, idx;
      @ loop variant n - i;
    */
    for(int i = 0; i < n-1; i++) {
      //@ghost l1:;
      if (list[i] > list[i+1]) {
        swap(list+i, list+(i+1));
        /*@ assert swap{l1,Here}(list,list,0,i,i+1,n);*/
        sorted = 0;
        /*@ ghost idx = i+1;*/
      }
    }
    /*@ ghost maximal_fixed_tail = idx;*/
  }
  return;
}
