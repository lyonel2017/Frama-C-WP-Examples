#include <limits.h>
#include <stdio.h>

/*@ predicate sorted(int* tab, integer first, integer last) =
 \forall integer x,y; first <= x <= y < last ==> tab[x] <= tab[y];
*/

/*@ predicate swap{L1, L2}(int *a, int *b, integer begin, integer i, integer j, integer end) =
      begin <= i < end && begin <= j < end &&
      \at(a[i], L1) == \at(b[j], L2) &&
      \at(a[j], L1) == \at(b[i], L2) &&
      \forall integer k; begin <= k < end && k != i && k != j ==> \at(a[k], L1) == \at(b[k], L2);
*/

/*@ predicate same_array{L1,L2}(int *a, int *b, integer begin, integer end) =
      \forall integer k; begin <= k < end ==> \at(a[k],L1) == \at(b[k],L2);
*/

/*@ predicate partitioned(int *a, integer begin, integer end, integer pivot) =
      (\forall integer k; begin <= k < pivot ==> a[k] <= a[pivot]) &&
      (\forall integer l; pivot < l < end ==> a[pivot] < a[l]);
*/

// When all elements are leq than value at L1, they have to be leq than value at L2
/*@ predicate preserve_upper_bound{L1,L2}(int *a, integer begin, integer end, integer value) =
    (\forall int p; begin <= p < end ==>  \at(a[p],L1) <= value) ==>
      (\forall int p; begin <= p < end ==>  \at(a[p],L2) <= value);
*/

/*@ predicate preserve_all_upper_bounds{L1,L2}(int *a, integer begin, integer end) =
      (\forall integer v; preserve_upper_bound{L1,L2}(a, begin, end, v));
*/

// When all elements are bigger than value at L1, they have to be bigger than value at L2
/*@ predicate preserve_lower_bound{L1,L2}(int *a, integer begin, integer end, integer value) =
   (\forall int p; begin <= p < end ==>  \at(a[p],L1) > value) ==>
      (\forall int p; begin <= p < end ==>  \at(a[p],L2) > value);
*/

/*@ predicate preserve_all_lower_bounds{L1,L2}(int *a, integer begin, integer end) =
      (\forall integer v; preserve_lower_bound{L1,L2}(a, begin, end, v));
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


/*@
 @ requires
 @      \valid(array + i)
 @   ∧  \valid(array + j);
  requires \valid(array + (0 .. upper-1));
  requires i >=0 && i< upper;
    requires j >=0 && j< upper;
    terminates \true;
 @ assigns
 @   array[i], array[j];
 @ ensures
 @      array[i] == \old(array[j])
 @   ∧  array[j] == \old(array[i]);
  @ ensures same_elements{Pre, Post}( array, array, (int)0, upper);
  ensures swap{Pre, Post}(array, array, (int)0, i,j, upper);
 @*/
void swap(int *array, int i, int j,
          /* ghost: */ int upper)
{
  int tmp = array[i];
  array[i] = array[j];
  array[j] = tmp;
}
/*@
  requires
    0 <= l < l + 1 < u;
  requires
    \valid(array + (l .. u - 1));
     terminates \true;
  assigns
    \nothing;
  ensures
    l <= \result < u;
 */
int choose_pivot(int *array, int l, int u)
{
  return l + ((u - l) / 2);
}
/*@
 @ requires
   0 <= l < l + 1 < u;
 requires u <= upper;
  requires
    \valid(array + (0 .. upper - 1));
   terminates \true;
  assigns
    *(array + (l .. u - 1));
    ensures \forall int v; preserve_upper_bound{Pre,Post}(array, l, u, v);
  ensures
    \forall int v; preserve_lower_bound{Pre,Post}(array, l, u, v);
  ensures
    l <= \result < u;
  ensures
    partitioned(array, l, u, \result);


  
    ensures same_elements{Pre, Post}( array, array, 0, upper);
 */
int partition(int *array, int l, int u,
  /* ghost: */ int upper)
{
  int i = l + 1;
  int j = u - 1;
  int m = choose_pivot(array, l, u);
preswap1:
  swap(array, l, m,
       /*ghost: */ upper);
       //@ assert same_elements{Pre, Here}(array, array, 0, upper);
  /*@
    loop invariant
      l < i <= j < u;
    loop invariant
         (\forall int p; l < p < i ==>  array[p] <= array[l])
      &&  (\forall int q; j < q < u ==>  array[l] < array[q]);
    loop invariant
      \forall int v; preserve_upper_bound{Pre,Here}(array, l, u, v);
    loop invariant
      \forall int v; preserve_lower_bound{Pre,Here}(array, l, u, v);
    loop invariant
      same_elements{Pre, Here}(array, array, 0, upper);
    loop assigns
      i, j, *(array + (l .. u - 1));
    loop variant j-i;
   */
  while (i < j)
  {
  scan1:
    /*
      loop invariant
        l < i <= j < u;
      loop invariant
        \forall int p; \at(i, scan1) <= p < i ==>
          array[p] <= array[l];
      loop assigns
        i;
      loop variant j-i;
     */
    while (i < j && array[i] <= array[l])
    {
      i += 1;
    }
    scan2:
    //@ assert \forall int p; l < p < i ==>  array[p] <= array[l];
    /*@
      loop invariant
        l < i <= j < u;
      loop invariant
        \forall int q; j < q <= \at(j, scan2) ==>
          array[l] < array[q];
      loop assigns
        j;
      loop variant j-i;
     */
    while (i < j && array[l] < array[j])
    {
      j -= 1;
    }
    //@ assert \forall int q; j < q < u ==>  array[l] < array[q];
    if (i < j)
    {
      //@ assert array[i] > array[l] >= array[j];
      swap(array, i, j,
           /*ghost: */ upper);
      //@ assert array[i] <= array[l] < array[j];
    }
  }
  if (array[l] < array[i])
  {
    i -= 1;
  }
  swap(array, l, i,
       /*ghost: */ upper);
  return i;
}

/*@
  requires
    0 <= first <= last < INT_MAX;
  requires
    \valid(t + (0 .. upper - 1));
 requires last <= upper;
  assigns
    *(t + (first .. last - 1));
  ensures
    \forall int v; preserve_upper_bound{Pre, Post}(t, first, last, v);
  ensures
    \forall int v; preserve_lower_bound{Pre, Post}(t, first, last, v);
  ensures
    sorted(t, first, last);
  ensures
     	same_elements{Pre, Post}(t, t, 0, upper);
 */
void sort(int *t, int first, int last,
/* ghost: */ int upper)
{
  if (last - first <= 1)
  {
    return;
  }
  //@ assert 1 < last-first;
  //@ assert same_elements{Pre, Here}(t, t, 0, upper);

  int pivot = partition(t, first, last,
  /* ghost: */ upper);
    //@ assert same_elements{Pre, Here}(t, t, 0, upper);
part:
  sort(t, first, pivot,
  /* ghost: */ upper);
    //@ assert same_elements{part, Here}(t, t, 0, upper);
    //@ assert same_elements{Pre, Here}(t, t, 0, upper);
  //@ assert \forall int v; preserve_upper_bound{Pre, Here}(t, first, last, v);
  //@ assert \forall int v; preserve_lower_bound{Pre, Here}(t, first, last, v);
  //@ assert preserve_lower_bound{part, Here}(t, pivot + 1, last, t[pivot]);
  sort(t, pivot + 1, last,
  /* ghost: */ upper);
    //@ assert same_elements{Pre, Here}(t, t, 0, upper);
  //@ assert preserve_upper_bound{part, Here}(t, first, pivot, t[pivot]);
  //@ assert preserve_lower_bound{part, Here}(t, pivot + 1, last, t[pivot]);
}


void main() {

int num[5] = {1, 4, 5, 7, 0}; 


sort(num, 0, 5, 5);

    for(int j = 0; j < 5; j++) {
        printf("%d ", num[j]);
    }
}
