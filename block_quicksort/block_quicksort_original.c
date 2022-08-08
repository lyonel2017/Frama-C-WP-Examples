
#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <unistd.h>

#define BLOCKSIZE 3
/*@
assigns \nothing;
*/
void print_array(int *arr, int len)
{
  for (int j = 0; j < len; j++)
  {
    printf("%d ", arr[j]);
  }
  printf("\n");
}

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
 @ requires
 @      \valid(array + i)
 @   ∧  \valid(array + j);
  requires \valid(array + (0 .. upper-1));
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
assigns \nothing;


*/
int min(int a, int b)
{
  return (a < b ? a : b);
}

// /*@
//  @ requires
//  @   0 <= begin < begin + 1 < end < INT_MAX;
//  requires end <= upper;
//  requires begin <= pivot_position < end;
//  @ requires
//  @   \valid(arr + (0 .. upper-1));
//  @ assigns
//  @   *(arr + (begin .. end - 1));
//  @ ensures
//  @   begin <= \result < end;
//  @ ensures
//  @   partitioned(arr, begin, end, \result);
//  @ ensures
//  @   ∀ int v; preserve_upper_bound{Pre,Post}(arr, begin, end, v);
//  @ ensures
//  @   ∀ int v; preserve_lower_bound{Pre,Post}(arr, begin, end, v);
//  @
//  @   ensures same_elements{Pre, Post}( arr, arr, 0, upper);
//  @*/
// int block_partition(int *arr, int begin, int end,
//                     int pivot_position,
//                     /* ghost: */ int upper)
// {
//   int blocksize = BLOCKSIZE;
//   int indexL[BLOCKSIZE], indexR[BLOCKSIZE];

//   int last = end - 1;
//   int first = begin;
//   swap(arr, pivot_position, last, end);
//   //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
//   const int pivot = arr[last];
//   pivot_position = last;
//   last--;

//   int num_left = 0;
//   int num_right = 0;
//   int start_left = 0;
//   int start_right = 0;
//   int num;

//   // main loop
//   /*@
//  @ loop invariant
//  @   begin <= first <= last < end ;
//  @ loop invariant
//  @      (∀ int p; begin < p < first ==>  arr[p] < pivot)
//  @   &&  (∀ int q; last < q < end ==>  pivot <= arr[q]);
//  @ loop invariant
//  @   ∀ int v; preserve_upper_bound{Pre,Here}(arr, begin, end, v);
//  @ loop invariant
//  @   ∀ int v; preserve_lower_bound{Pre,Here}(arr, begin, end, v);
//  @ loop invariant
//  @   same_elements{Pre, Here}(arr, arr, 0, upper);
//  @ loop assigns
//  @   first, last, *(arr + (last .. begin - 1)), num_left, num_right, start_left, start_right;
//  @ loop variant last-first;
//  @*/
//   while (last - first + 1 > 2 * BLOCKSIZE)
//   {
//     // Compare and store in buffers
//     if (num_left == 0)
//     {
//       start_left = 0;

//       /*@

// @ loop invariant
// @   \forall int v; 0<=v < num_left  ==> arr[first + indexL[v]] >= pivot;
// @ loop invariant
// @   \forall int v; 0<=v < j &&
// ! ( \exists int w; 0 <=w < num_left ==> indexL[w] == v) ==> arr[first+v] < pivot;
//  @ loop invariant
//  @   same_elements{Pre, Here}(arr, arr, 0, upper);
// @ loop assigns num_left, indexL[0..blocksize-1], j;
//       */
//       for (int j = 0; j < BLOCKSIZE; j++)
//       {
//         if (!(arr[first + j] < pivot))
//         {
//           indexL[num_left] = j;

//           //@ assert arr[first + indexL[num_left]] >= pivot;
//           //@ assert \forall int v; 0<=v < num_left  ==> arr[first + indexL[v]] >= pivot;
//           num_left += 1;
//         }
//         else
//         {
//           //@ assert arr[first + j] < pivot;
//         }
//         //@ assert  (\exists int w; 0<=w<num_left && indexL[w] == j) ==> arr[first+j] >= pivot;
//         //@ assert ( !(\exists int w; 0<=w<num_left-1 && indexL[w] == j)) ==> arr[first+j] < pivot;
//       }
//     }

//     //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
//     if (num_right == 0)
//     {
//       start_right = 0;
//       /*@
//             @ loop invariant
//       @   \forall int v; 0<=v < num_right  ==> arr[last - indexR[v]] <= pivot;
//        @ loop invariant
//  @   same_elements{Pre, Here}(arr, arr, 0, upper);
//       @ loop assigns num_right, indexR[0..blocksize-1], j;
//       */
//       for (int j = 0; j < BLOCKSIZE; j++)
//       {
//         if (!(pivot < arr[last - j]))
//         {
//           indexR[num_right] = j;
//           //@ assert arr[last - indexR[num_right]] <= pivot;
//           //@ assert \forall int v; 0<=v < num_right  ==> arr[last - indexR[v]] <= pivot;
//           num_right += 1;
//         }
//       }
//     }

//     //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
//     // rearrange elements
//     num = min(num_left, num_right);
//     /*@
//      @ loop invariant
//  @   same_elements{Pre, Here}(arr, arr, 0, upper);
//  */
//     for (int j = 0; j < num; j++)
//     {
//       swap(arr, first + indexL[start_left + j], last - indexR[start_right + j], upper);

//       //@ assert same_elements{LoopCurrent, Here}(arr, arr, 0, upper);
//       //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
//     }

//     num_left -= num;
//     num_right -= num;
//     start_left += num;
//     start_right += num;
//     first += (num_left == 0) ? BLOCKSIZE : 0;
//     last -= (num_right == 0) ? BLOCKSIZE : 0;

//   } // end main loop

//   print_array(arr, upper);
//   printf("\n");
//   printf("first: %i\n", first);
//   printf("last: %i\n", last);
//   printf("begin: %i\n", begin);
//   printf("end: %i\n", end);

//   // Compare and store in buffers final iteration
//   int shiftR = 0, shiftL = 0;
//   if (num_right == 0 && num_left == 0)
//   { // for small arrays or in the unlikely
//     // case that both buffers are empty
//     shiftL = ((last - begin) + 1) / 2;
//     shiftR = (last - begin) + 1 - shiftL;
//     assert(shiftL >= 0);
//     assert(shiftL <= BLOCKSIZE);
//     assert(shiftR >= 0);
//     assert(shiftR <= BLOCKSIZE);
//     start_left = 0;
//     start_right = 0;
//     for (int j = 0; j < shiftL; j++)
//     {
//       indexL[num_left] = j;
//       num_left += (!(arr[begin + j] < pivot));
//       indexR[num_right] = j;
//       num_right += !(pivot < arr[last - j]);
//     }
//     if (shiftL < shiftR)
//     {
//       assert(shiftL + 1 == shiftR);
//       indexR[num_right] = shiftR - 1;
//       num_right += !(pivot < arr[last - shiftR + 1]);
//     }
//   }
//   else if (num_right != 0)
//   {
//     shiftL = (last - begin) - BLOCKSIZE + 1;
//     shiftR = BLOCKSIZE;
//     assert(shiftL >= 0);
//     assert(shiftL <= BLOCKSIZE);
//     assert(num_left == 0);
//     start_left = 0;
//     for (int j = 0; j < shiftL; j++)
//     {
//       indexL[num_left] = j;
//       num_left += (!(arr[begin + j] < pivot));
//     }
//   }
//   else
//   {
//     shiftL = BLOCKSIZE;
//     shiftR = (last - begin) - BLOCKSIZE + 1;
//     assert(shiftR >= 0);
//     assert(shiftR <= BLOCKSIZE);
//     assert(num_right == 0);
//     start_right = 0;
//     for (int j = 0; j < shiftR; j++)
//     {
//       indexR[num_right] = j;
//       num_right += !((pivot < arr[last - j]));
//     }
//   }

//   // rearrange final iteration
//   num = min(num_left, num_right);
//   for (int j = 0; j < num; j++)
//     swap(arr, begin + indexL[start_left + j], last - indexR[start_right + j], end);

//   num_left -= num;
//   num_right -= num;
//   start_left += num;
//   start_right += num;
//   begin += (num_left == 0) ? shiftL : 0;
//   last -= (num_right == 0) ? shiftR : 0;
//   // end final iteration

//   // rearrange elements remaining in buffer
//   if (num_left != 0)
//   {

//     assert(num_right == 0);
//     int lowerI = start_left + num_left - 1;
//     int upper = last - begin;
//     // search first element to be swapped
//     while (lowerI >= start_left && indexL[lowerI] == upper)
//     {
//       upper--;
//       lowerI--;
//     }
//     while (lowerI >= start_left)
//       swap(arr, begin + upper--, begin + indexL[lowerI--], end);

//     swap(arr, pivot_position, begin + upper + 1, end); // fetch the pivot
//     return begin + upper + 1;
//   }
//   else if (num_right != 0)
//   {
//     assert(num_left == 0);
//     int lowerI = start_right + num_right - 1;
//     int upper = last - begin;
//     // search first element to be swapped
//     while (lowerI >= start_right && indexR[lowerI] == upper)
//     {
//       upper--;
//       lowerI--;
//     }

//     while (lowerI >= start_right)
//       swap(arr, last - upper--, last - indexR[lowerI--], end);

//     swap(arr, pivot_position, last - upper, end); // fetch the pivot
//     return last - upper;
//   }
//   else
//   { // no remaining elements
//     assert(last + 1 == begin);
//     swap(arr, pivot_position, begin, end); // fetch the pivot
//     return begin;
//   }
// }

/*@
 @ requires
 @   0 <= begin < begin + 1 < end < INT_MAX;
 requires end <= upper;
 requires begin <= pivot_position < end;
 @ requires
 @   \valid(arr + (0 .. upper-1));
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
 @
 @   ensures same_elements{Pre, Post}( arr, arr, 0, upper);
 @*/
int block_partition_hoare_finish(int *arr, int begin, int end, int pivot_position, /* ghost: */ int upper)
{

  const int blocksize = BLOCKSIZE;
  Blocksize:

  print_array(arr + begin, end - begin);
  int last = end - 1;
  int indexL[BLOCKSIZE] = {0}, indexR[BLOCKSIZE] = {0};
  print_array(indexL, BLOCKSIZE);
  //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
  swap(arr, pivot_position, begin, upper);
  //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
  int pivot_location = begin;
  int q = arr[pivot_location];
  printf("block_partition: ");

  printf("pivot: %i\n", q);
  int temp;
  int iL = 0;
  int iR = 0;
  int sL = 0;
  int sR = 0;
  int j;
  int num;
  /*@
  loop invariant same_elements{Pre, Here}(arr, arr, 0, upper);
  loop invariant \forall int v; \at(begin, Pre) <= v < begin ==> arr[v] <= q;  //0-begin are smaller
  loop invariant \forall int v; last <= v < end ==> arr[v] > q;  //last-end are bigger
  */
  while (last - begin + 1 > 2 * BLOCKSIZE)
  {
    printf("Main loop\n");
    print_array(arr, upper);
    if (iL == 0)
    {
      sL = 0;
      //@ assert iL == 0;
      //@ assert blocksize >0 ;
      /*@
      loop invariant 0 <= iL < blocksize;
      loop invariant same_elements{Pre, Here}(arr, arr, 0, upper);
      loop invariant \forall int v; \at(begin, Pre) <= v < begin ==> arr[v] <= q;  //0-begin are smaller
      loop invariant \forall int v; 0 <= v < iL ==> arr[begin + indexL[v]] > q;
      loop invariant same_array{LoopCurrent, Here}(&indexL[0], &indexL[0], 0, iL-1);
      loop invariant same_array{LoopCurrent, Here}(arr, arr, 0, upper);
      loop assigns indexL[0..blocksize-1], iL;
      */
      for (j = 0; j < BLOCKSIZE; j++)
      {
      prelscan:
        if (!(arr[begin + j] <= q))
        {
          indexL[iL] = j;
          //@ assert arr[begin + indexL[iL]] > q;
          iL += 1;
          //@ assert (\forall int v; 0 <= v < \at(iL,LoopCurrent) ==> arr[begin + indexL[v]] > q) ==> (\forall int v; 0<= v < iL ==> arr[begin + indexL[v]] > q);
        }
        //@ assert same_array{LoopCurrent, Here}(&indexL[0], &indexL[0], 0, iL-1);
        //@ assert (\forall int v; 0 <= v < \at(iL,LoopCurrent) ==> arr[begin + \at(indexL[v],LoopCurrent)] > q) ==> (\forall int v; 0<= v < iL ==> arr[begin + indexL[v]] > q);

        //@ assert (iL > 0) ==> arr[begin + indexL[iL-1]] >q;

        //@ assert \forall int v; \at(begin, Pre) <= v < begin ==> arr[v] <= q;
        // printf("left scan: j=%i, iL=%i ", j, iL);
        // print_array(indexL, BLOCKSIZE);
      }
    }
    if (iR == 0)
    {
      sR = 0;
      /*@
      loop invariant same_elements{Pre, Here}(arr, arr, 0, upper);
      loop invariant \forall int v; last < v < end ==> arr[v] > q;  //0-begin are smaller

      */
      for (j = 0; j < BLOCKSIZE; j++)
      {
        if (!(q < arr[last - j]))
        {
          indexR[iR] = j;
          //@ assert arr[last - indexR[iR]] <= q;
          iR += 1;
        }
        printf("right scan: j=%i, iR=%i ", j, iR);
        print_array(indexR, BLOCKSIZE);
      }
    }
    printf("indexL: ");
    print_array(indexL, BLOCKSIZE);
    printf("indexR: ");
    print_array(indexR, BLOCKSIZE);
    num = min(iL, iR);
    if (num != 0)
    {
      // printf("Swapping: ");

      /*@
loop invariant same_elements{Pre, Here}(arr, arr, 0, upper);

*/
      for (j = 0; j < num; j++)
      {
        swap(arr, begin + indexL[sL + j], last - indexR[sR + j], upper);
      }
      printf("swapping result: ");
      print_array(arr, end);
    }
    iL -= num;
    iR -= num;
    sL += num;
    sR += num;
    if (iL == 0)
      begin += BLOCKSIZE;
    if (iR == 0)
      last -= BLOCKSIZE;
    //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
  } // end main loop
  begin--;
  last++;
  /*@
  loop invariant same_elements{Pre, Here}(arr, arr, 0, upper);

  */
  do
  {
    /*@

      loop invariant same_elements{Pre, Here}(arr, arr, 0, upper);
    */
    do
    {
    } while (arr[++begin] <= q);
    /*@
      loop invariant same_elements{Pre, Here}(arr, arr, 0, upper);
    */
    do
    {
    } while (q < arr[--last]);
    if (begin <= last)
    {
      swap(arr, begin, last, upper);
      //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
    }
  } while (begin <= last);
  swap(arr, pivot_location, last, upper);
  //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
  printf("Partitioning result: ");
  print_array(arr, end);
  printf("demarcation line: %i\n\n", last);
  //@ assert same_elements{Pre, Here}(arr, arr, 0, upper);
  return last;
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
  printf("leftsort(arr,%i,%i,%i)", first, pivot, upper);
  sort(t, first, pivot, upper);
  //@ assert same_elements{part, Here}(t, t, 0, upper);
  //@ assert same_elements{Pre, Here}(t, t, 0, upper);
  //@ assert \forall int v; preserve_upper_bound{Pre, Here}(t, first, last, v);
  //@ assert \forall int v; preserve_lower_bound{Pre, Here}(t, first, last, v);
  //@ assert preserve_lower_bound{part, Here}(t, pivot + 1, last, t[pivot]);
  printf("rightsort(arr,%i,%i,%i)", pivot + 1, last, upper);
  sort(t, pivot + 1, last, upper);
  //@ assert same_elements{Pre, Here}(t, t, 0, upper);
  //@ assert preserve_upper_bound{part, Here}(t, first, pivot, t[pivot]);
  //@ assert preserve_lower_bound{part, Here}(t, pivot + 1, last, t[pivot]);
}

int main()
{

  printf("\n\n\n\n\n\n\nNEW RUN\n\n\n");
  int arr[10] = {1, 5, 2, 4, 8, 7, 5, 6, 9, 0};

  // int loc = block_partition_hoare_finish(arr, 0, 10, 5, 10);
  // printf("return value: %i\n", loc);

  sort(arr, 0, 10, 10);

  print_array(arr, 10);

  return 0;
}