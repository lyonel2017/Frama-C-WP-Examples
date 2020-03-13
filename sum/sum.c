
/*@ axiomatic Sum {
  @   logic integer sum{L}(int *t, integer i, integer j)
  @        reads t[..] ;
  @   axiom sum1{L} :
  @     \forall int *t, integer i, j; i >= j ==> sum(t,i,j) == 0;
  @   axiom sum2{L} :
  @     \forall int *t, integer i, j; i <= j ==>
  @       sum(t,i,j+1) == sum(t,i,j) + t[j];
  @   lemma sum3{L} :
  @     \forall int *t, integer i, j, k;
  @       0 <= i <= j <= k ==>
  @         sum(t,i,k) == sum(t,i,j) + sum(t,j,k);
  @   lemma sum_4{L1,L2} :
  @     \forall int *t, integer i, j; 
  @       (\forall integer k; i <= k < j ==> \at(t[k],L1) == \at(t[k],L2)) ==>
  @       \at(sum(t,i,j),L1) == \at(sum(t,i,j),L2);
  @ }
  @*/


/*@ requires n >= 1 && \valid(t+(0..n-1)) ;
  @ ensures \result == sum(t,0,n);
  @ assigns \nothing;*/
int sum(int t[],int n) {
  int i,s = 0;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant s == sum(t,0,i);
    @ loop assigns s,i;
    @ loop variant n-i;
  */
  for(i=0; i < n; i++)
  {
    s += t[i];
  }
  return s;
}

/*@ requires n >= 1;
  @ requires \valid(t+(0..n-1));
  @ requires \separated(t+(0..n-1));
  @ assigns t[0..n-1];
  @ ensures sum(t,0,n) == \old(sum(t,0,n))+n;
  @ ensures \forall int k; 0 <= k < n ==> t[k] == \at(t[k],Pre) + 1;
  @*/
void add_one(int t[],int n) {
  int i;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant \forall int k; 0 <= k < i ==> t[k] == \at(t[k],Pre) + 1;
    @ loop invariant \forall int k; i <= k < n ==> t[k] == \at(t[k],Pre);
    @ loop invariant \let k = i; sum(t,k,n) == \at(sum(t,k,n),Pre);
    @ loop invariant \let k = i; sum(t,0,k) == \at(sum(t,0,k),Pre) + k;
    @ loop assigns t[0..n-1],i;
    @ loop variant n-i;*/
  for(i=0; i < n; i++) {
    t[i] += 1;
   }
}
