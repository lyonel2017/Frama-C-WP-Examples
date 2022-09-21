
#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <unistd.h>

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

  predicate array_lower_bound{L1}(int* arr, int n, int x, int begin, int *z, int q) =
(\forall int v; 0 <= v < \at(x,L1) ==> \at(arr[begin+\at(z[v], L1)], L1) > q);

  predicate array_upper_bound{L1}(int* arr, int n, int x, int last, int *z, int q) =
(\forall int v; 0 <= v < \at(x,L1) ==> \at(arr[last-\at(z[v], L1)], L1) <= q);

lemma array_lower_bound_next{L1, L2}:
\forall int *arr, n, x, begin, *z, q;
(\at(x, L1) != \at(x, L2) ==> array_lower_bound{L1}(arr, n, x, begin, z, q)) &&
(\at(x, L1) != \at(x, L2) ==> same_array{L1, L2}(arr, arr, 0, n)) &&
(\at(x, L1) != \at(x, L2) ==> same_array{L1, L2}(z, z, 0, \at(x, L1))) &&
(\at(x, L1) != \at(x, L2) ==> \at(x, L1) + 1 == \at(x, L2)) &&
(\at(x, L1) != \at(x, L2) ==> \at(arr[begin+\at(z[x-1], L2)], L2) > q) ==>
(\at(x, L1) != \at(x, L2) ==> array_lower_bound{L2}(arr, n, x, begin, z, q));
*/

/*@

  predicate all_in_block_are_bigger(int* arr, int n, int x, int begin, int *z, int q) =
  \forall int v; 0 <= v < x ==> arr[begin + z[v]] > q;

    predicate all_in_block_are_lower(int* arr, int n, int x, int last, int *z, int q) =
  \forall int v; 0 <= v < x ==> arr[last - z[v]] <= q;

*/
// /*@

// lemma same_array_implication{L1, L2}:
// \forall int q, *arr, n, x, y;
// same_array{L1,L2}(arr, arr, 0, n) &&
// array_upper_bound{L1}(arr, n, x, y, q) ==>
// array_upper_bound{L2}(arr, n, x, y, q);

// */

/*@

lemma swap_compare{L1,L2}:
\forall int *arr, upper, x, y, q;
0<= x <upper &&
0<= y <upper ==>
\at(arr[x],L1) <= q &&
swap{L1,L2}(arr, arr, 0, x, y, upper) ==>
\at(arr[y], L2) <= q;


*/
/*@

  requires i >=0 && i< upper;
    requires j >=0 && j< upper;
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
ensures a <=b ==> \result == a;
ensures a >= b ==> \result == b;
ensures \result <= a;
ensures \result <= b;
assigns \nothing;


*/
int min(int a, int b)
{
  return (a < b ? a : b);
}

/*@
 @ requires
 @   0  <upper;

 @ requires
 @   \valid(arr+(0..upper-1));

ensures \false;
ensures same_elements{Pre, Post}(arr, arr, 0, upper);
 @
 @*/
void test(int *arr, int end, int upper)
{
  return;
}

/*@
 @ requires
 @   0< end < upper;
requires \valid(arr+(0..upper));
requires \valid(arr+(0..upper));




 @*/
void test2(int *arr, int *arr2, int begin, int end, int pivot_position, /* ghost: */ int upper)
{
  arr[1] = 0;
  arr2[end] = 1;
  //@ assert arr[1] == 0;

  return;
}

/*@ requires 0 ≤ begin < begin + 1 < end;
    requires begin ≤ pivot_position < end;

    ensures \false;
 */
int test3(int *arr, int begin, int end,
          int pivot_position, int upper)
{
  int pivot_location = begin;
  int q = arr[pivot_location];

  /*@


  loop invariant all_that_existL:  arr[begin] > q;
  */
  while (end - begin + 1 > 2 * 3)
  {
    end++;
  }
  return 1;
}
/*@
 @ requires
 @   0 <= l < l + 1 < u < INT_MAX;
 requires u <= upper;
   terminates \true;
 @ assigns
 @   *(array + (l .. u - 1));
 @ ensures
 @   l <= \result < u;
 @ ensures
 @   partitioned(array, l, u, \result);
 @ ensures
 @   \forall int v; preserve_upper_bound{Pre,Post}(array, l, u, v);
 @ ensures
 @   \forall int v; preserve_lower_bound{Pre,Post}(array, l, u, v);
 @
 @   ensures same_elements{Pre, Post}( array, array, 0, upper);
 @*/
int partition_pivot(int *array, int l, int u, int pivot_value,
                    /* ghost: */ int upper)
{
  int i = l;
  int j = u - 1;
preswap1:

  //@ assert same_elements{Pre, Here}(array, array, 0, upper);
  /*@
   @ loop invariant
   @   l < i <= j < u;
   @ loop invariant
   @      (\forall int p; l < p < i ==>  array[p] <= pivot_value)
   @   &&  (\forall int q; j < q < u ==>  pivot_value < array[q]);
   @ loop invariant
   @   \forall int v; preserve_upper_bound{Pre,Here}(array, l, u, v);
   @ loop invariant
   @   \forall int v; preserve_lower_bound{Pre,Here}(array, l, u, v);
   @ loop invariant
   @   same_elements{Pre, Here}(array, array, 0, upper);
   @ loop assigns
   @   i, j, *(array + (l+1 .. u - 1));
   @ loop variant j-i;
   @*/
  while (i < j)
  {
  scan1:
    /*@
     @ loop invariant
     @   l < i <= j < u;
     @ loop invariant
     @   \forall int p; \at(i, scan1) <= p < i ==>
     @     array[p] <= pivot_value;
     @ loop assigns
     @   i;
     @ loop variant j-i;
     @*/
    while (i < j && array[i] <= pivot_value)
    {
      i += 1;
    }
  scan2:
    //@ assert \forall int p; l < p < i ==>  array[p] <= pivot_value;
    /*@
     @ loop invariant
     @   l < i <= j < u;
     @ loop invariant
     @   \forall int q; j < q <= \at(j, scan2) ==>
     @     pivot_value < array[q];
     @ loop assigns
     @   j;
     @ loop variant j-i;
     @*/
    while (i < j && pivot_value < array[j])
    {
      j -= 1;
    }
    //@ assert \forall int q; j < q < u ==>  pivot_value < array[q];
    if (i < j)
    {
      //@ assert array[i] > pivot_value >= array[j];
      swap(array, i, j,
           /*ghost: */ upper);
      //@ assert array[i] <= pivot_value < array[j];
    }
  } // End of outer loop
  if (array[i] > pivot_value)
  {
    i -= 1;
  }

  return i;
}
/*@
 @ requires
 @   0 <= begin < begin + 1 < end ;
 requires begin <= pivot_position < end;

 @ assigns
 @   *(arr + (begin .. end - 1));
 @ ensures
 @   begin <= \result < end;
 @ ensures
 @   partitioned(arr, begin, end, \result);
 @ ensures
 @   ∀ int v; preserve_upper_bound{Pre,Post}(arr, begin, end, v);
 @ ensures
 @   ∀ int v; preserve_lower_bound{Pre,Post}(arr, begin, end, v);
 @*/
int block_partition_hoare_finish(int *arr, int begin, int end, int pivot_position, /* ghost: */ int upper)
{
  // print_array(arr + begin, end - begin);
  int last = end - 1;

  swap(arr, pivot_position, begin, upper);
  //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
  int pivot_location = begin;
  int q = arr[pivot_location];
  begin++;
  // printf("block_partition: ");

  // printf("pivot: %i\n", q);
  int temp;
  int iL = 0;
  int iR = 0;
  int sL = 0;
  int sR = 0;
  int j;
  int num;

  int indexL1[3] = {0}, indexR1[3] = {0};
  int *indexL = indexL1;
  int *indexR = indexR1;
  // //@ assert \separated(arr+(0..upper-1), indexL+(0..3));
  /*@
  loop invariant same_elements{Pre, Here}(arr, arr, 0, upper);

  loop invariant indexL_bounds: \forall int v; 0<=v<3 ==> 0<=indexL[v]<3;
  loop invariant indexR_bounds: \forall int v; 0<=v<3 ==> 0<=indexR[v]<3;

  loop invariant \forall int v; \at(begin, Pre) <= v < begin ==> arr[v] <= q;  //0-begin are smaller
  loop invariant \forall int v; last <= v < end ==> arr[v] > q;  //last-end are bigger

  loop invariant all_that_existL: \forall int v; 0 <= v < 3 ==> ((\exists int i; 0<=i<iL ==> indexL[i] == v) ==> arr[begin+v] > q);
  loop invariant all_that_dont_existL: \forall int v; 0 <= v < 3 ==> ((!\exists int i; 0<=i<iL ==> indexL[i] == v) ==> arr[begin+v] <= q);
  loop invariant all_that_existR: \forall int v; 0 <= v < 3 ==> ((\exists int i; 0<=i<iR ==> indexR[i] == v) ==> arr[last-v] <= q);
  loop invariant all_that_dont_existR: \forall int v; 0 <= v < 3 ==> ((!\exists int i; 0<=i<iR ==> indexR[i] == v) ==> arr[last-v] > q);
  */
  while (last - begin + 1 > 2 * 3)
  {
    // //print_array(arr, upper);

    //@ assert begin + 3-1 <upper;

    if (iL == 0)
    {
      sL = 0;
      /*@
      loop invariant 0<= j <= 3;
      loop invariant 0 <= iL <= j;
      loop invariant \forall int v; \at(begin, Pre) <= v < begin ==> arr[v] <= q;  //0-begin are smaller

      loop invariant indexL_unchanged: same_array{LoopCurrent, Here}(indexL, indexL, 0, iL-1);

      //bounds on the contents of indexL
      loop invariant indexL_bounds: \forall int v; 0<=v<3 ==> 0<=indexL[v]<3;

      loop invariant all_that_exist: \forall int v; 0 <= v < 3 ==> ((\exists int i; 0<=i<iL ==> indexL[i] == v) ==> arr[begin+v] > q);
      loop invariant all_that_dont_exist: \forall int v; 0 <= v < 3 ==> ((!\exists int i; 0<=i<iL ==> indexL[i] == v) ==> arr[begin+v] <= q);

      loop invariant array_lower_bound(arr, upper, iL, begin, indexL, q);
      loop assigns indexL[0..3-1];
      loop assigns iL, j;
      */
      for (j = 0; j < 3; j++)
      {

        //@ assert same_array{LoopCurrent, Here}(arr, arr, 0, upper);
        //@ assert 0<= iL <3;
        indexL[iL] = j;

        // bounds on the members of indexL
        //@ assert 0<=indexL[iL]<3;
        // @ assert array_upper_bound(arr, upper, iL, begin, indexL, q);
        iL += !(arr[begin + j] <= q);

        //@ assert \at(iL, LoopCurrent) != iL ==> arr[begin + j] > q && \at(iL, LoopCurrent) +1 == iL;

        //@ assert \separated(arr+(0..upper-1), indexL+(0..3));

        // force lemma
        //@ assert (\at(iL, LoopCurrent) != \at(iL, Here) ==> array_lower_bound{LoopCurrent}(arr, upper, iL, begin, indexL, q));
        //@ assert (\at(iL, LoopCurrent) != \at(iL, Here) ==> same_array{LoopCurrent, Here}(arr, arr, 0, upper));
        //@ assert (\at(iL, LoopCurrent) != \at(iL, Here) ==> same_array{LoopCurrent, Here}(indexL, indexL, 0, \at(iL, LoopCurrent)));
        //@ assert (\at(iL, LoopCurrent) != \at(iL, Here) ==> \at(iL, LoopCurrent) + 1 == \at(iL, Here));
        //@ assert (\at(iL, LoopCurrent) != \at(iL, Here) ==> \at(arr[begin+\at(indexL[iL-1], Here)], Here) > q);

        //@ assert \at(iL, LoopCurrent) != iL ==> array_lower_bound(arr, upper, iL, begin, indexL, q);

        //@ assert \at(iL, LoopCurrent) == iL ==> arr[begin + j] <= q;
        //@ assert array_lower_bound(arr, upper, iL, begin, indexL, q);
      }
    }
    if (iR == 0)
    {
      sR = 0;
      /*@
      loop invariant 0<= j <= 3;
      loop invariant 0 <= iR <= j;
      loop invariant \forall int v; last <= v < end ==> arr[v] > q;  //last-end are bigger

      loop invariant indexL_unchanged: same_array{LoopCurrent, Here}(indexR, indexR, 0, iR-1);

      //bounds on the contents of indexR
      loop invariant indexR_bounds: \forall int v; 0<=v<3 ==> 0<=indexR[v]<3;

      loop invariant all_that_exist: \forall int v; 0 <= v < 3 ==> ((\exists int i; 0<=i<iR ==> indexR[i] == v) ==> arr[last-v] <= q);
      loop invariant all_that_dont_exist: \forall int v; 0 <= v < 3 ==> ((!\exists int i; 0<=i<iR ==> indexR[i] == v) ==> arr[last-v] > q);

      loop invariant array_lower_bound(arr, upper, iR, last, indexR, q);
      loop assigns indexR[0..3-1];
      loop assigns iR, j;
      */
      for (j = 0; j < 3; j++)
      {
        //@ assert same_array{LoopCurrent, Here}(arr, arr, 0, upper);
        //@ assert 0<= iR <3;
        indexR[iR] = j;

        // bounds on the members of indexR
        //@ assert 0<=indexR[iR]<3;
        // @ assert array_lower_bound(arr, upper, iR, last, indexR, q);
        iR += !(q < arr[last - j]);

        //@ assert \at(iR, LoopCurrent) != iR ==> arr[last - j] > q && \at(iR, LoopCurrent) +1 == iR;

        // //@ assert \separated(arr+(0..upper-1), indexR+(0..3-1));

        // force lemma
        //@ assert array_lower_bound{LoopCurrent}(arr, upper, iR, last, indexR, q);
        //@ assert same_array{LoopCurrent, Here}(arr, arr, 0, upper);
        //@ assert same_array{LoopCurrent, Here}(indexR, indexR, 0, \at(iR, LoopCurrent));
        //@ assert \at(iR, LoopCurrent) != iR ==> \at(iR, LoopCurrent) + 1 == \at(iR, Here);
        //@ assert \at(iR, LoopCurrent) != iR ==> \at(arr[last-\at(indexL[iR-1], Here)], Here) > q ;

        //@ assert \at(iR, LoopCurrent) != iR ==> array_lower_bound(arr, upper, iR, last, indexL, q);

        //@ assert \at(iR, LoopCurrent) == iR ==> arr[last - j] > q;
        //@ assert array_lower_bound(arr, upper, iL, last, indexR, q);
      }
    }

    num = min(iL, iR);
    if (num != 0)
    {

      //@ assert array_upper_bound(arr, upper, num, begin, indexL, q);
      //@ assert array_lower_bound(arr, upper, num, last, indexR, q);

      /*@

      loop invariant lower: \forall int v; 0 <= v < j ==> arr[begin+indexL[sL+v]] > q;
      loop invariant upper: \forall int v; 0 <= v < j ==> arr[last-indexR[sR+v]] <= q;

      loop invariant lower: \forall int v; j <= v < num ==> arr[begin+indexL[sL+v]] <= q;
      loop invariant upper: \forall int v; 0 <= v < num ==> arr[last-indexR[sR+v]] > q;

      loop assigns arr[begin..last];

*/
      for (j = 0; j < num; j++)
      {
        int x = begin + indexL[sL + j];
        int y = last - indexR[sR + j];

      // //@ assert \separated(arr+(0..upper-1), indexR+(0..3-1));
      // //@ assert \separated(arr+(0..upper-1), indexL+(0..3-1));
      //@ assert arr[x] > q;
      //@ assert arr[y] <= q;
      preswap:
        swap(arr, x, y, upper);
        //@ assert arr[x] <= q;
        //@ assert arr[begin + indexL[sL + j]] <= q;
        //@ assert arr[y] > q;
        //@ assert arr[last - indexR[sR + j]] > q;
      }
      // printf("swapping result: ");
      // print_array(arr, end);
    }
    iL -= num;
    iR -= num;
    sL += num;
    sR += num;
    if (iL == 0)
      begin += 3;
    if (iR == 0)
      last -= 3;
    //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
  } // end main loop
  last++;
  int mid = partition_pivot(arr, begin, last, q, upper);
  swap(arr, pivot_location, mid, upper);
  //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);

  return mid;
}

/*@
 @ requires
 @   0 <= l < l + 1 < u < INT_MAX;

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
 @   0 <= first <= last < INT_MAX;

 requires last <= upper;
 @ assigns
 @   *(t + (first .. last - 1));
 @ ensures
 @   \forall int v; preserve_upper_bound{Pre, Post}(t, first, last, v);
 @ ensures
 @   \forall int v; preserve_lower_bound{Pre, Post}(t, first, last, v);
 @ ensures
 @   sorted(t, first, last);
 @ ensures
 @    	same_elements{Pre, Post}(t, t, 0, upper);
 @*/
void sort(int *t, int first, int last, int upper)
{
  if (last - first <= 1)
  {
    return;
  }

  //@ assert 1 < last-first;
  //@ assert same_elements{Pre, Here}(t, t, 0, upper);
  // sleep(1);
  int pivot = block_partition_hoare_finish(t, first, last, choose_pivot(t, first, last), last);
  //@ assert same_elements{Pre, Here}(t, t, 0, upper);
part:
  // printf("leftsort(arr,%i,%i,%i)", first, pivot, upper);
  sort(t, first, pivot, upper);
  //@ assert same_elements{part, Here}(t, t, 0, upper);
  //@ assert same_elements{Pre, Here}(t, t, 0, upper);
  //@ assert \forall int v; preserve_upper_bound{Pre, Here}(t, first, last, v);
  //@ assert \forall int v; preserve_lower_bound{Pre, Here}(t, first, last, v);
  //@ assert preserve_lower_bound{part, Here}(t, pivot + 1, last, t[pivot]);
  // printf("rightsort(arr,%i,%i,%i)", pivot + 1, last, upper);
  sort(t, pivot + 1, last, upper);
  //@ assert same_elements{Pre, Here}(t, t, 0, upper);
  //@ assert preserve_upper_bound{part, Here}(t, first, pivot, t[pivot]);
  //@ assert preserve_lower_bound{part, Here}(t, pivot + 1, last, t[pivot]);
}
