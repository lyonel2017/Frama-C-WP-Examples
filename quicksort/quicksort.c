#include <limits.h>

/*@ predicate sorted(int* tab, integer first, integer last) =
 \forall integer x,y; first <= x < y < last ==> tab[x] <= tab[y];
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
      (\forall integer k; pivot < k < end ==> a[pivot] < a[k]);
*/

//When all elements are leq than value at L1, they have to be leq than value at L2
/*@ predicate preserve_upper_bound{L1,L2}(int *a, integer begin, integer end, integer value) =
      (\forall integer k; begin <= k < end ==> \at(a[k], L1) <= value) ==>
      (\forall integer k; begin <= k < end ==> \at(a[k], L2) <= value);
*/

/*@ predicate preserve_all_upper_bounds{L1,L2}(int *a, integer begin, integer end) =
      (\forall integer v; preserve_upper_bound{L1,L2}(a, begin, end, v));
*/

//When all elements are bigger than value at L1, they have to be bigger than value at L2
/*@ predicate preserve_lower_bound{L1,L2}(int *a, integer begin, integer end, integer value) =
      (\forall integer k; begin <= k < end ==> \at(a[k], L1) > value) ==>
      (\forall integer k; begin <= k < end ==> \at(a[k], L2) > value);
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
 @   0 <= first < first + 1 < last < INT_MAX;
 @ requires
 @   \valid(t + (first .. last - 1));
 requires first <= pivot < last;
 @ assigns
 @   *(t + (first .. last - 1));
 @ ensures
 @   first <= \result < last;
 @ ensures
 @   partitioned(t, first, last, \result);
 @ ensures
 @   preserve_all_lower_bounds{Pre,Post}(t, first, last);
 @ ensures
 @   preserve_all_upper_bounds{Pre,Post}(t, first, last);
 @ ensures
 @   permutation(\old(t), t, first, last);
 @*/

int partition(int *t, int first, int last, int pivot)
{
  /*@ assert first <= pivot < last; */
  /*@ assert \valid(t+pivot); */
  int pivot_value = t[pivot];
  preswap1:
  swap(t, pivot, first);

  //t[last] now contains the pivot element
  int i = first + 1;
  int j = last - 1;

  /*@
   @ loop invariant
   @   first < i <= j < last;
   @ loop invariant
   @      (\forall int p; first < p < i ==>  t[p] <= pivot_value)
   @   &&  (\forall int q; j < q < last ==>  pivot_value < t[q]);
   @ loop invariant
   @   \forall integer v; preserve_lower_bound{Pre,Here}(t, first, last, v);
   @ loop invariant
   @   \forall integer v; preserve_upper_bound{Pre,Here}(t, first, last, v);
   @ loop invariant
   @    	    permutation(\at(t, Pre), \at(t, Here), first, last);
   @ loop assigns
   @   i, j, *(t + (first .. last - 1));
   @*/
  while (i < j)
  {
    
leftscan: 
    //scan left
    /*@
     @ loop invariant
     @   first + 1 <= i <= j < last;
     @ loop invariant
     @   ∀ int p; \at(i, leftscan) <= p < i ==> 
     @     t[p] <= pivot_value;
     @ loop assigns
     @   i;
     @*/
    while (i < j && t[i] <= pivot_value)
    {

      // t[i] is the leftmost element which is gt pivot_value or i==j
      i += 1;
    }
    //@ assert \forall int p; first < p < i ==>  t[p] <= pivot_value;

    rightscan: 
    /*@
     @ loop invariant
     @   first + 1 <= i <= j < last;
     @ loop invariant
     @   \forall int q; j < q <= \at(j, rightscan) ==> 
     @     pivot_value < t[q];
     @ loop assigns
     @   j;
     @*/
    while (i < j && pivot_value < t[j])
    {

      // t[j] is the rightmost element which is leq pivot_value or i==j
      j -= 1;
    }
    //@ assert \forall int q; j < q < last ==>  pivot_value < t[q];

    // only if i != j
    if (i < j)
    {
      //@ assert t[i] > pivot_value >= t[j];
      preswap2: swap(t, i, j);
       //@ assert t[i] <= pivot_value < t[j];
    }
  }
  //did we walk one step to far? t[i] needs tp ne leq pivot_value, because it gets swapped to the front
  if (pivot_value < t[i])
  {
    i -= 1;
  }
  //swap first (which contains the pivot) to t[i] (which belongs in the lower partiton)
  preswap3: swap(t, first, i);
  return i;

}
/*@ requires first >= 0 && last >= 0 && INT_MAX >= first && INT_MAX >= last ;
    requires last > first;
    assigns \nothing;
    ensures \result >= first;
    ensures last > \result;

*/
int choose_pivot(int *t, int first, int last)
{ //retunr a pivot between first and last
  int dist = (last - first);
  int ret = first + dist / 2;

  return ret;
}

 /*@
  @ requires
  @   0 <= first <= last < INT_MAX;
  @ requires
  @   \valid(t + (first .. last - 1));
  @ assigns
  @   *(t + (first .. last - 1));
  @ ensures
  @   preserve_all_upper_bounds{Pre, Post}(t, first, last);
  @ ensures
  @   preserve_all_lower_bounds{Pre, Post}(t, first, last);
  @ ensures
  @   sorted(t, first, last);
  @ ensures
  @    	permutation(\old(t), t, first, last);
  @*/
void sort(int *t, int first, int last)
{
  if (first < last)
  {
    //@ assert same_elements{Pre, Here}(t, t, first, last);
    int pivot = choose_pivot(t, first, last);
    pivot = partition(t, first, last, pivot);
    part:
    sort(t, first, pivot);
         //@ ghost int mm = pivot + 1;
     //@ assert preserve_all_upper_bounds{Pre, Here}(t, first, last);
     //@ assert preserve_all_lower_bounds{Pre, Here}(t, first, last);
     //@ assert preserve_lower_bound{part, Here}(t, mm, last, t[pivot]);
    sort(t, pivot + 1, last);
         //@ assert preserve_upper_bound{part, Here}(t, first, pivot, t[pivot]);
     //@ assert preserve_lower_bound{part, Here}(t, mm, last, t[pivot]);
  }
  return;
}
