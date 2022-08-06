#include <limits.h>
#include <stdio.h>
#include <assert.h>

#define BLOCKSIZE 2
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
 @ logic integer count_elt{L1}(int *a, integer l, integer u, int v) =
 @   (l == u) ? 0
 @   : (((v == \at(a[l], L1)) ? 1 : 0) + count_elt{L1}(a, l + 1, u, v));
 @*/

// valid hier entfernen, das macht man nicht in predicates
/*@
 @ predicate permutation{L1, L2}(int *a, int *b, int l, int u) =
 @     \forall int v; count_elt{L1}(a, l, u, v) == count_elt{L2}(b, l, u, v);
 @*/

int min(int a, int b)
{
  return (a < b ? a : b);
}

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
 @ requires
 @   0 <= l < l + 1 < u < INT_MAX;
 @ requires
 @   \valid(array + (l .. u - 1));
     terminates \true;
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
 requires u <= upper;
 @ requires
 @   \valid(array + (0 .. upper - 1));
   terminates \true;
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
 @
 @   ensures same_elements{Pre, Post}( array, array, 0, upper);
 @*/
int block_partition(int *array, int l, int u,
                    /* ghost: */ int upper)
{
  int block_l[BLOCKSIZE] = {0};
  int block_r[BLOCKSIZE] = {0};
  int i = l;
  int j = u - 1;
  int m = choose_pivot(array, l, u);
  printf("pivot: %i\n", m);

  int num_left = 0; // elements in block
  int num_right = 0;

  int start_left = 0;
  int start_right = 0;

preswap1:
  swap(array, j, m,
       /*ghost: */ upper);
  m = j;
  print_array(array, upper);
  printf("pivot value: %i\n", array[m]);
  //@ assert same_elements{Pre, Here}(array, array, 0, upper);
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
   @   same_elements{Pre, Here}(array, array, 0, upper);
   @ loop assigns
   @   i, j, *(array + (l .. u - 1));
   @ loop variant j-i;
   @*/

  while (j - i + 1 > 2 * BLOCKSIZE)
  {
    printf("main loop. num_left: %i, num_right: %i, start_left: %i, start_right: %i\n", num_left, num_right, start_left, start_right);

  CurrentOuter:

    //@ assert ∀ int p; l < p < i ==>  array[p] <= array[l];
    /*@
     @ loop invariant
     @   l + 1 <= i <= j < u;
     @ loop invariant
     @   ∀ int q; j < q <= \at(j, CurrentOuter) ==>
     @     array[l] < array[q];
     @ loop assigns
     @   j;
     @ loop variant j-i;
     @*/
    if (num_left == 0)
    { // only fill blocks when they are empty

      start_left = 0;
      for (int a = 0; a < BLOCKSIZE; a++)
      {
        if (array[a + i] >= (array[m]))
        {
          printf("store %i in block_l[%i]\n", a + 1, num_left);
          // store in block
          block_l[num_left] = a;
          num_left++;
        }
      }
    }

    if (num_right == 0)
    { // only fill blocks when they are empty

      start_right = 0;
      for (int a = 0; a < BLOCKSIZE; a++)
      {
        if (array[j - a] <= (array[m]))
        {
          printf("store %i in block_r[%i]\n", j - a, num_right);
          // store in block
          block_r[num_right] = a;
          num_right++;
        }
      }
    }
    // rearange
    int num_min = min(num_left, num_right);
    printf("num_min: %i\n", num_min);

    for (int a = 0; a < num_min; a++)
    {
      swap(array, i + block_l[start_left + a], j - block_r[start_right + a], upper);
    }
    num_left -= num_min;
    num_right -= num_min;
    start_left += num_min;
    start_right += num_min;
    i += (num_left == 0) ? BLOCKSIZE : 0;
    j -= (num_right == 0) ? BLOCKSIZE : 0;
    // end rearrange
  }

  // end main loop
  // now the gap between l and u is smaller than 2*BLOCKSIZE

  int shiftR = 0;
  int shiftL = 0;

  if (num_right == 0 && num_left == 0)
  {
    shiftL = ((j - i) + 1) / 2;
    shiftR = (j - i) + 1 - shiftL;
    // midpoint or midpoints (even length)
    assert(shiftL >= 0);
    assert(shiftL <= BLOCKSIZE);
    assert(shiftR >= 0);
    assert(shiftR <= BLOCKSIZE);

    start_left = 0;
    start_right = 0;

    for (int a = 0; a < shiftL; a++)
    {
      if (array[a + i] >= (array[m]))
      {
        // store in block
        block_l[num_left] = a;
        num_left++;
      }
      if (array[j - a] <= (array[m]))
      {
        // store in block
        block_r[num_right] = a;
        num_right++;
      }
    }

    if (shiftL < shiftR)
    {
      assert(shiftL + 1 == shiftR);
      if (array[j - shiftR] <= (array[m]))
      {
        // store in block
        block_r[num_right] = shiftR - 1;
        num_right++;
      }
    }
  }
  else if (num_right != 0)
  {
    shiftL = (j - i) - BLOCKSIZE + 1;
    shiftR = BLOCKSIZE;
    assert(shiftL >= 0);
    assert(shiftL <= BLOCKSIZE);
    assert(num_left == 0);

    start_left = 0;
    for (int a = 0; a < shiftL; j++)
    {
      if (array[a + i] >= (array[m]))
      {
        // store in block
        block_l[num_left] = a;
        num_left++;
      }
    }
  }
  else
  {
    shiftL = BLOCKSIZE;
    shiftR = (j - i) - BLOCKSIZE + 1;
    assert(shiftR >= 0);
    assert(shiftR <= BLOCKSIZE);
    assert(num_right == 0);
    start_right = 0;
    for (int a = 0; a < shiftR; a++)
    {
      if (array[j - shiftR] <= (array[m]))
      {
        // store in block
        block_r[num_right] = a;
        num_right++;
      }
    }
  }

  // rearange final
  int num_min = min(num_left, num_right);

  for (int a = 0; a < num_min; a++)
  {
    swap(array, l + block_l[start_left + a], u - block_r[start_right + a], upper);
  }
  num_left -= num_min;
  num_right -= num_min;
  start_left += num_min;
  start_right += num_min;
  i += (num_left == 0) ? shiftL : 0;
  j -= (num_right == 0) ? shiftR : 0;
  // end rearrange final

  // one of the two buffers might still contain elements

  if (num_left != 0)
  {

    assert(num_right == 0);
    int lowerI = start_left + num_left - 1;
    int up = j - i;

    while (lowerI >= start_left && block_l[lowerI] == up)
    {
      upper--;
      lowerI--;
    }
    while (lowerI >= start_left)
      swap(array, i + up--, i + block_l[lowerI--], upper);
    swap(array, m, i + up + 1, upper);
    return i + up + 1;
  }
  else if (num_right != 0)

  {
    assert(num_left == 0);
    int lowerI = start_right + num_right - 1;
    int up = j - i;

    while (lowerI >= start_right && block_r[lowerI] == up)
    {

      upper--;
      lowerI--;
    }
    while (lowerI >= start_left)
      swap(array, j - up--, j - block_r[lowerI--], upper);

    swap(array, m, j - up, upper);
    return j - up;
  }
  else
  {
    // no remaining elements

    assert(j + 1 == i);
    swap(array, m, i, upper);
    return i;
  }
}

/*@
 @ requires
 @   0 <= first <= last < INT_MAX;
 @ requires
 @   \valid(t + (0 .. upper - 1));
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
void sort(int *t, int first, int last,
          /* ghost: */ int upper)
{
  if (last - first <= 1)
  {
    return;
  }
  //@ assert 1 < last-first;
  //@ assert same_elements{Pre, Here}(t, t, 0, upper);

  int pivot = block_partition(t, first, last,
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

void print_array(int *arr, int len)
{
  for (int j = 0; j < len; j++)
  {
    printf("%d ", arr[j]);
  }
  printf("\n");
}

