/*@ predicate sorted(int* tab, integer idx) = \forall integer x,y; 0 <= x < y < idx ==> tab[x] <= tab[y]; */


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
      case split {L1, L2}: \forall int *a, int *b, integer begin, i, end;
        begin <= i < end ==>
        same_elements{L1,L2}(a, b, begin, i) ==>
        same_elements{L1,L2}(a, b, i, end) ==>
        same_elements{L1,L2}(a, b, begin, end);
}*/

/*@ lemma partition {L1, L2}: \forall int *a, int *b, integer begin, i, j, end;
        begin <= i <= j < end ==>
        same_array{L1,L2}(a, b, begin, i) ==>
        same_elements{L1,L2}(a, b, i, j) ==>
        same_array{L1,L2}(a, b, j, end) ==>
        same_elements{L1, L2}(a, b, begin, end);
*/

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
    requires sorted(tab,n);
    requires \valid(tab+(0..n));
    ensures sorted(tab,n+1);
    ensures same_elements{Pre,Post}(tab,tab,0,n+1);
    assigns tab[0..n];
*/
void decale(int tab[], int n){
  int i = n;
  /*@ loop invariant 0 <= i <= n;
     loop invariant \forall int j; 0 <= j < i ==> tab[j] == \at(tab[j],Pre);
     loop invariant \forall int j; i < j  <= n ==> tab[j] > tab[i];
     loop invariant \forall int j,k; i < j < k <= n ==> tab[j] <= tab[k];
     loop invariant \forall int j,k; 0 <= j  < i < k <= n ==> tab[j] <= tab[k];
     loop invariant \forall int j,k; 0 <= j < k < i ==> tab[j] <= tab[k];
     loop invariant same_elements{Pre,Here}(tab,tab,0,n+1);
     loop assigns i, tab[0..n];
     loop variant i;
   */
  while (i > 0 && tab[i-1] > tab[i]){
  l1:swap(tab+i, tab+(i-1));
    /*@ assert swap{l1,Here}(tab,tab,0,i,i-1,n+1);*/
    i--;
  }
  return;
}

/*@ requires 0 <= n;
    requires \valid(tab+(0..n));
    ensures sorted(tab,n);
    ensures same_elements{Pre,Post}(tab,tab,0,n+1);
    assigns tab[0..n-1];*/
void tri_insertion(int tab[], int n){
  int lim;
  /*@ loop invariant 0 <= lim <= n;
      loop invariant sorted(tab,lim);
      loop invariant same_elements{Pre,Here}(tab,tab,0,n);
      loop assigns tab[0..n-1],lim;
      loop variant n - lim;
   */
  for (lim = 0; lim < n; lim++){
  l1:decale(tab,lim);
    /*@ assert same_elements{l1,Here}(tab,tab,0,n);*/
  }
  return;
}
