#include <limits.h>

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
    (∀ int p; begin <= p < end ==>  \at(a[p],L1) <= value) ==>
      (∀ int p; begin <= p < end ==>  \at(a[p],L2) <= value);
*/

/*@ predicate preserve_all_upper_bounds{L1,L2}(int *a, integer begin, integer end) =
      (\forall integer v; preserve_upper_bound{L1,L2}(a, begin, end, v));
*/

// When all elements are bigger than value at L1, they have to be bigger than value at L2
/*@ predicate preserve_lower_bound{L1,L2}(int *a, integer begin, integer end, integer value) =
   (∀ int p; begin <= p < end ==>  \at(a[p],L1) > value) ==>
      (∀ int p; begin <= p < end ==>  \at(a[p],L2) > value);
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
 @ logic integer count_elt(int *a, integer l, integer u, int v) =
 @   (l == u) ? 0
 @   : (((v == a[l]) ? 1 : 0) + count_elt(a, l + 1, u, v));
 @*/

// valid hier entfernen, das macht man nicht in predicates
/*@
 @ predicate permutation(int *a, int *b, int l, int u) =
 @   \valid(a + (l .. u - 1)) ∧  \valid(b + (l .. u - 1)) ∧
 @     ∀ int v; count_elt(a, l, u, v) == count_elt(b, l, u, v);
 @*/

/*@
 @ requires
 @      \valid(array + i)
 @   ∧  \valid(array + j);
 @ assigns
 @   array[i], array[j];
 @ ensures
 @      array[i] == \old(array[j])
 @   ∧  array[j] == \old(array[i]);

 @*/
void swap(int *array, int i, int j)
{
  int tmp = array[i];
  array[i] = array[j];
  array[j] = tmp;
}
/*@
 @ requires
 @   0 <= l < l + 1 < u < INT_MAX;
 @ requires
 @   \valid(array + (l .. u - 1));
 @ assigns
 @   \nothing;
 @ ensures
 @   l <= \result < u;
 @*/
int choose_pivot(int *array, int l, int u)
{
  return l + ((u - l) / 2);
}
/*@
 @ requires
 @   0 <= l < l + 1 < u < INT_MAX;
 @ requires
 @   \valid(array + (l .. u - 1));
 @ assigns
 @   *(array + (l .. u - 1));
 @ ensures
 @   l <= \result < u;
 @ ensures
 @   partitioned(array, l, u, \result);
 @ ensures
 @   ∀ int v; preserve_upper_bound{Pre,Post}(array, l, u, v);
 @ ensures
 @   ∀ int v; preserve_lower_bound{Pre,Post}(array, l, u, v);
 @ ensures
 @   permutation(\old(array), array, l, u);
 @*/
int partition(int *array, int l, int u)
{
  int i = l + 1;
  int j = u - 1;
  int m = choose_pivot(array, l, u);
  preswap1: swap(array, l, m);
  /*@
   @ loop invariant
   @   l < i <= j < u;
   @ loop invariant
   @      (∀ int p; l < p < i ==>  array[p] <= array[l])
   @   &&  (∀ int q; j < q < u ==>  array[l] < array[q]);
   @ loop invariant
   @   ∀ int v; preserve_upper_bound{Pre,Here}(array, l, u, v);
   @ loop invariant
   @   ∀ int v; preserve_lower_bound{Pre,Here}(array, l, u, v);
   @ loop invariant
   @   permutation(\at(array, Pre), \at(array, Here), l, u);
   @ loop assigns
   @   i, j, *(array + (l .. u - 1));
   @*/
  while (i < j)
  {
  CurrentOuter:
    /*@
     @ loop invariant
     @   l + 1 <= i <= j < u;
     @ loop invariant
     @   ∀ int p; \at(i, CurrentOuter) <= p < i ==> 
     @     array[p] <= array[l];
     @ loop assigns
     @   i;
     @*/
    while (i < j && array[i] <= array[l])
    {
      i += 1;
    }
    //@ assert ∀ int p; l < p < i ==>  array[p] <= array[l];
    /*@
     @ loop invariant
     @   l + 1 <= i <= j < u;
     @ loop invariant
     @   ∀ int q; j < q <= \at(j, CurrentOuter) ==> 
     @     array[l] < array[q];
     @ loop assigns
     @   j;
     @*/
    while (i < j && array[l] < array[j])
    {
      j -= 1;
    }
    //@ assert ∀ int q; j < q < u ==>  array[l] < array[q];
    if (i < j)
    {
      //@ assert array[i] > array[l] >= array[j];
      swap(array, i, j);
      //@ assert array[i] <= array[l] < array[j];
    }
  }
  if (array[l] < array[i])
  {
    i -= 1;
  }
  swap(array, l, i);
  return i;
}

/*@
 @ requires
 @   0 <= first <= last < INT_MAX;
 @ requires
 @   \valid(t + (first .. last - 1));
 @ assigns
 @   *(t + (first .. last - 1));
 @ ensures
 @   \forall int v; preserve_upper_bound{Pre, Post}(t, first, last, v);
 @ ensures
 @   \forall int v; preserve_lower_bound{Pre, Post}(t, first, last, v);
 @ ensures
 @   sorted(t, first, last);
 @ ensures
 @    	permutation(\old(t), t, first, last);
 @*/
void sort(int *t, int first, int last)
{
  if (last - first <= 1)
  {
    return;
  }
    //@ assert 1 < last-first;
    //@ assert same_elements{Pre, Here}(t, t, first, last);

  int pivot = partition(t, first, last);
part:
  sort(t, first, pivot);
  //@ assert \forall int v; preserve_upper_bound{Pre, Here}(t, first, last, v);
  //@ assert \forall int v; preserve_lower_bound{Pre, Here}(t, first, last, v);
  //@ assert preserve_lower_bound{part, Here}(t, pivot + 1, last, t[pivot]);
  sort(t, pivot + 1, last);
  //@ assert preserve_upper_bound{part, Here}(t, first, pivot, t[pivot]);
  //@ assert preserve_lower_bound{part, Here}(t, pivot + 1, last, t[pivot]);
}
