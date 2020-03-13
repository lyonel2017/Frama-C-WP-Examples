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

/*@ requires 0 <= n;
    requires sorted(tab,n);
    ensures \forall int j; 0 <= j < \result ==> tab[j] <= val;
    ensures \forall int j; \result <= j < n ==> tab[j] > val;
    ensures 0 <= \result <= n;
    assigns \nothing;
*/
int chercher_limite(int tab[], int n, int val){
  int i;
  /*@ loop invariant 0 <= i <= n;
      loop invariant \forall int j; 0 <= j < i ==> tab[j] <= val;
      loop assigns i;
      loop variant n - i;
   */
  for (i = 0; i < n; i++){
    if(tab[i] > val){
      return i;
    }
  }
  return n;
}

/*@ requires 0 <= idx <= n;
    requires \separated(tab+(0..n),gtab+(0..n));
    requires same_array{Pre, Pre}(tab, gtab, 0, n);
    ensures \forall int j; idx < j <= n ==> tab[j] == \at(tab[j-1],Pre);
    ensures \forall int j; 0 <= j <= idx ==> tab[j] == \at(tab[j],Pre);
    ensures same_elements{Pre, Post}(gtab, gtab, 0, n+1);
    ensures \forall integer k; 0 <= k <= n && k != idx ==> tab[k] == gtab[k];
    ensures \at(gtab[idx],Post) == \at(gtab[n],Pre);
    assigns tab[0..n],gtab[0..n];
*/
void decale(int tab[], int n, int idx) /*@ ghost (int gtab[])*/{
  int i;
  /*@ loop invariant idx <= i <= n;
      loop invariant \forall int j; i < j <= n ==> tab[j] == \at(tab[j-1],Pre);
      loop invariant \forall int j; 0 <= j <= i ==> tab[j] == \at(tab[j],Pre);
      loop invariant same_elements{Pre, Here}(gtab, gtab, 0, n+1);
      loop invariant \forall integer k; i < k <= n ==> tab[k] == gtab[k];
      loop invariant \forall integer k; 0 <= k < i  ==> tab[k] == gtab[k];
      loop invariant \at(gtab[i],Here) == \at(gtab[n],Pre);
      loop assigns i, tab[0..n], gtab[0..n];
      loop variant i;
   */
  for (i = n; i > idx; i--){
    /*@ ghost L1:;*/
    tab[i] = tab[i-1];
    /*@ ghost int temp = gtab[i];*/
    /*@ ghost gtab[i] = gtab[i-1];*/
    /*@ ghost gtab[i-1] = temp;*/
    /*@ assert swap{L1, Here}(gtab, gtab, 0, i-1, i, n+1);*/
  }
  return;
}

/*@ ghost int *t;*/ //use a local array and seach how to handle the case n = 0

/*@ requires 0 <= n;
  requires \separated(tab+(0..n-1),t+(0..n-1));
  requires same_array{Pre, Pre}(tab, t, 0, n);
  ensures sorted(tab,n);
  ensures same_elements{Pre, Post}(tab,tab, 0, n );
  assigns tab[0..n-1],t[0..n-1];*/
void tri_insertion(int tab[], int n){
  int lim;
  /*@ loop invariant 0 <= lim <= n;
      loop invariant sorted(tab,lim);
      loop invariant \forall int j; lim <= j < n ==> tab[j] == \at(tab[j],Pre);
      loop invariant same_array{Here, Here}(tab, t, 0, n);
      loop invariant same_elements{Pre, Here}(t,t, 0, n );
      loop assigns tab[0..n-1],t[0..n-1],lim;
      loop variant n - lim;
   */
  for (lim = 0; lim < n; lim++){
  l1:;
    int val = tab[lim];
    int idx = chercher_limite(tab,lim,val);
    decale(tab,lim,idx)/*@ ghost (t)*/;
    /*@ assert same_elements{l1,Here}(t,t,0,n);*/
    /*@ assert same_elements{Pre, Here}(t,t, 0, n );*/
    tab[idx] = val;
    /*@ assert sorted(tab,lim);*/
    /*@ assert same_elements{Pre, Here}(t,t, 0, n );*/
  }
  return;
}
