#include "Heap.acsl"
#include "MultisetOperations.acsl"
#include "MultisetRetainRest.acsl"
#include "MultisetParity.acsl"
#include "MultisetUpdate.acsl"
#include "IncreasingLemmas.acsl"
#include "ArrayBounds.acsl"
#include "WeaklyIncreasingLemmas.acsl"
#include "../../typedefs.h"

/*@
   assigns           \nothing;
   ensures  parent:  \result == HeapParent(child);
 */
size_type
heap_parent(size_type child)
{
  return (0u < child) ? (child - 1u) / 2u : 0u;
}

/*@
   requires bounds:  0 <= p < n;
   requires valid:   \valid(a + (0..n-1));
   assigns           \nothing;
   ensures  bounds:  p < \result <= n;
   ensures  parent:  \result < n       ==>  p == HeapParent(\result);
   ensures  parent:  \result < n-1     ==>  HeapLeft(p)  < n-1;
   ensures  parent:  \result < n-1     ==>  HeapRight(p) < n;
   ensures  left:    HeapLeft(p)  < n  ==>  \result < n;
   ensures  right:   HeapRight(p) < n  ==>  \result < n;
   ensures  max:     HeapLeft(p)  < n  ==>  a[HeapLeft(p)]  <= a[\result];
   ensures  max:     HeapRight(p) < n  ==>  a[HeapRight(p)] <= a[\result];
   ensures  none:    \result == n      ==>  n <= HeapLeft(p);
   ensures  none:    \result == n      ==>  n <= HeapRight(p);
*/
size_type
heap_child(const value_type *a, size_type n, size_type p)
{
  if (p + 1u <= n - p - 1u) {
    const size_type left = 2u * p + 1u;
    const size_type right = left + 1u;

    if (right < n) {
      // case of two children: select child with maximum value
      return a[right] <= a[left] ? left : right;
    }
    else {
      // at most one child that comes before n-1 can exist
      return left;
    }
  }
  else {
    return n;
  }
}

/*@
   requires valid: \valid_read(a + (0..n-1));
   assigns         \nothing;
   ensures bound:  0 <= \result <= n;
   ensures heap:   Heap(a, \result);
   ensures last:   \forall integer i; \result < i <= n ==> !Heap(a, i);
*/
size_type
is_heap_until(const value_type *a, size_type n)
{
  size_type parent = 0u;

  /*@
    loop invariant bound:    0 <= parent < child <= n+1;
    loop invariant parent:   parent == HeapParent(child);
    loop invariant heap:     Heap(a, child);
    loop invariant not_heap: a[parent] < a[child] ==> \forall integer i; child < i <= n ==> !Heap(a, i);

    loop assigns child, parent;
    loop variant n - child;
  */
  for (size_type child = 1u; child < n; ++child) {
    if (a[parent] < a[child]) {
      return child;
    }

    if ((child % 2u) == 0u) {
      // right child
      ++parent;
    }
  }

  return n;
}

/*@
   requires valid: \valid_read(a +(0..n-1));
   assigns         \nothing;
   ensures heap:   \result <==> Heap(a, n);
*/
bool
is_heap(const value_type *a, size_type n)
{
  return is_heap_until(a, n) == n;
}
/*@
   requires nonempty:   0 < n;
   requires valid:      \valid(a + (0..n-1));
   requires heap:       Heap(a, n-1);
   requires n2 >= n;
   assigns              a[0..n-1];
   ensures  heap:       Heap(a, n);
   ensures MultisetReorder{Pre, Post}(a, n2);
*/
void
push_heap(value_type *a, size_type n) /*@ ghost(size_type n2) */ // Everything is a heap, except for the very last element
{
  if (n <= 1) {
    return;
  }

  size_type child = n - 1; // element to be pushed in
  size_type parent = heap_parent(child);

  // Check if parent is smaller than child

  if (a[child] > a[parent]) {

    // Swap the parent element down but store the child element in temp
    value_type temp = a[child];
    a[child] = a[parent];

    //@ assert Heap(a, n);

    // only one spot in the array was updated
    //@ assert ArrayUpdate{Pre, Here}(a, n, child, a[parent]);

    // If temp would be at a[parent], the multiset would be unchanged
    //@ assert MultisetParity{Pre, Here}(a, n, a[parent], temp);

    // Shift all the smaller ancestors down until we find the perfect spot for temp

    child = parent;
    parent = heap_parent(child);

    /*@
      loop invariant 0<= child <n-1;
      loop invariant a[child] < temp;
      loop invariant parent == HeapParent(child);

      loop invariant MultisetParity{Pre, Here}(a, n, a[child], temp);
      loop invariant Unchanged{Pre, Here}(a, child);

      loop invariant Heap(a, n);
      loop invariant Unchanged{Pre, Here}(a, n, n2);
      loop assigns child, parent, a[0..n-1];
      loop variant child;
    */
    while (0u < child && a[parent] < temp)

    {

      //@ assert 0<= child <n;

      //@ ghost value_type old_child = a[child];

      // push the parent down
      a[child] = a[parent];
      //@ assert ArrayUpdate{LoopCurrent, Here}(a, n, child, a[parent]) || Unchanged{LoopCurrent, Here}(a, 0, n);
      //@ assert MultisetUpdate{LoopCurrent, Here}(a, n, child, a[parent]) || Unchanged{LoopCurrent, Here}(a, 0, n);
      // if a[child] was temp, the multiset would be unchanged
      //@ assert MultisetParity{Pre, Here}(a, n, a[child], temp);

      //@ assert a[child] < temp;
      //@ assert 0 <= child <n;
      //@ assert old_child < a[child] < temp || Unchanged{LoopCurrent, Here}(a, 0, n);

      child = parent;
      parent = heap_parent(child);
    }

    // temp either belongs to the root or has a parent which is larger
    //@ ghost value_type old_temp = a[child];

    // temp is either the root or leq than its parent
    //@ assert temp <= a[HeapParent(child)] || child == 0;

    //@ assert MultisetParity{Pre,Here}(a, n, old_temp, temp);

AfterLoop:
    a[child] = temp; // finally reinsert temp at the perfect location

    // only one spot changed
    //@ assert ArrayUpdate{AfterLoop,Here}(a, n, child, temp);
    //@ assert MultisetUpdate{AfterLoop,Here}(a, n, child, temp);

    // old_temp was replaced with temp
    //@ assert MultisetParity{AfterLoop, Here}(a,n, temp, old_temp);

    //@ assert MultisetReorder{Pre,Here}(a, n);

    //@ assert HeapCompatible(a, n, child, temp);
    //@ assert Heap(a, n);
  }

  //@ assert  MultisetReorder{Pre, Here}(a, n);
  //@ assert Unchanged{Pre, Here}(a, n, n2);
}

/*@
  requires \valid(a+(0..n-1));
  requires n >=1;
  requires Heap(a, n);

  ensures Heap(a, n-1);
  ensures MultisetReorder{Old,Here}(a, n);

  ensures a[n-1] == \old(a[0]);
  ensures MaxElement(a, n, n-1);


*/
void
pop_head(value_type *a, size_type n) // Move the head to the back and fix the heap 0..n-1

{
  if (n == 1 || a[n - 1] == a[0]) {
    return;
  }

  size_type parent = 0u;
  size_type child = heap_child(a, n - 1u, parent); // biggest child
  size_type temp = a[n - 1u];

  // swap head with tail

  a[n - 1u] = a[parent];

  //@ assert ArrayUpdate{Pre,Here}(a, n, n-1, a[parent]);

  // if a[p] was temp, the multiset would be equal

  //@ assert Heap(a, n-1);

  while (temp < a[child] && child < n - 1u) {
    // while the perfect spot was not found and the end of the array was not reached

    // pull the child up
    a[parent] = a[child];
    //@ assert ArrayUpdate{LoopCurrent,Here}(a, n, parent, a[child]) || Unchanged{LoopCurrent, Here}(a, 0, n);
    //@ assert MultisetUpdate{LoopCurrent, Here}(a, n, parent, a[child]) || Unchanged{LoopCurrent, Here}(a, 0, n);

    // if a[child] was temp, the multiset would be unchanged

    //

    parent = child;
    child = heap_child(a, n - 1u, parent);
  }

  // the
}

/*@
    requires \valid(a + (0..n-1));
  ensures Heap(a, n);
  ensures MultisetReorder{Pre,Post}(a, n);
  ensures Unchanged{Pre, Post}(a, n, n2);
  assigns a[0..n-1];

*/
void
heapify(value_type *a, size_type n) /*@ ghost(size_type n2) */

{
  if (n <= 1) {
    return;
  }

  /*@
  loop invariant Heap(a, i);
  loop invariant MultisetReorder{Pre,Here}(a, n);
  loop assigns a[0..n-1], i;
  loop invariant Unchanged{Pre, Here}(a, i + 1, n);

  loop invariant 1 <=i<=n;

  */
  for (size_type i = 1u; i < n; i++) {
    push_heap(a, i + 1u) /*@ ghost(n) */;
  }
}
/*@
 requires \valid(a+(0..n-1));
requires n>0;
assigns a[0..n-1];
ensures MultisetReorder{Pre, Post}(a, n);
ensures Increasing(a, n);

*/
void
sort(value_type *a, size_type n)
{
  if (n == 1) {
    return;
  }

  heapify(a, n) /*@ ghost(n) */;

  /*@
    loop invariant 0u<i;
    loop invariant i<= n;

    loop invariant Heap(a, i);

    loop invariant MultisetReorder{Pre, Here}(a, n);


    loop invariant LowerBound(a, i, n, a[i]);
    loop invariant LowerBound(a, i, n, a[0]);

    loop invariant WeaklyIncreasing(a, i, n);

  loop assigns i, a[0..n-1];
  loop variant i;

  */
  for (size_type i = n; i > 1; i--) {

    if (a[0] == a[i - 1]) {

      //@ assert Heap(a, i-1);
      //@ assert UpperBound(a, i, a[i-1]);
      //@ assert MultisetReorder{Pre, Here}(a, n);
      //@ assert LowerBound(a, i-1, n, a[i-1]);
      continue;
    }

    //@ assert Heap(a, i);
    //@ assert MaxElement(a, i, 0);
    value_type temp = a[0];

    a[0] = a[i - 1u];
    //@ assert ArrayUpdate{LoopCurrent, Here}(a, n, 0, a[i-1]);
    //@ assert MultisetUpdate{LoopCurrent, Here}(a, n, 0, a[i-1]);

    //@ assert MultisetParity{LoopCurrent, Here}(a, n, a[i-1u],temp);

    //@ assert Unchanged{LoopCurrent, Here}(a, i, n);

    //@ ghost L: ;
    //@ assert a[i-1] != temp;
    a[i - 1u] = temp;

    //@ assert ArrayUpdate{L, Here}(a, n, i-1, temp) ;
    //@ assert MultisetUpdate{L, Here}(a, n, i-1, temp);

    //@ assert MultisetReorder{LoopCurrent, Here}(a, n);
    //@ assert Unchanged{LoopCurrent, Here}(a, i, n);
    //@ assert MaxElement(a, i, i-1);

    heapify(a, i - 1u) /*@ ghost(n) */;
    //@ assert Heap(a, i-1);
    //@ assert MaxElement(a, i, i-1);
    //@ assert MultisetReorder{Pre, Here}(a, n);
    //@ assert LowerBound(a, i-1, n, a[i-1]);
  }

  //@ assert Increasing(a, n);
}
