/*@ axiomatic Sum {
  @   logic integer sum{L}(int** t, integer i, integer j, integer c)
  @        reads t[..][c] ;
  @   axiom sum1{L} :
  @     \forall int** t, integer i, j, c; i >= j ==> sum(t,i,j,c) == 0;
  @   axiom sum2{L} :
  @     \forall int** t, integer i, j, c; i <= j ==> sum(t,i,j+1,c) == sum(t,i,j,c) + t[j][c];
  @ }
  @*/


/** number of voters */
int V;

/** number of candidates */
int C;

/*@ requires C > 0 && V > 0;
  @ requires 0 <= c < C;
  @ requires \valid(votes+(0..V-1));
  @ requires \forall integer k; 0 <= k < V ==> \valid(votes[k]+(0..C-1));
  @ requires \forall integer i;
        0 <= i < V ==> -2147483648 <= sum(votes,0,i,c) + votes[i][c] <= 2147483647;
  @ ensures \result == sum(votes,0,V,c);
  @ assigns \result;*/
int sum(int** votes, int c){
  int i = 0;
  int res = 0;
  /*@ loop invariant 0 <= i <= V;
    @ loop invariant res == sum(votes,0,i,c);
    @ loop assigns i,res;
    @ loop variant V-i;
  */
  while (i < V ) {
    res += votes[i][c];
    i++;
  }
  return res;
}

/*@ requires C > 0 && V > 0;
  @ requires \valid(votes+(0..V-1));
  @ requires \forall integer k; 0 <= k < V ==> \valid(votes[k]+(0..C-1));
  @ requires \forall integer i,c;
        0 <= i < V && 0 <= c < C ==>
        -2147483648 <= sum(votes,0,i,c) + votes[i][c] <= 2147483647;
  @ ensures \result != C ==> (\forall integer k; 0 <= k < C &&
            k != \result ==> sum(votes,0,V,\result) > sum(votes,0,V,k));
  @ ensures \result == C ==> (\exists integer i,j; sum(votes,0,V,j) == sum(votes,0,V,i));
  @ assigns \result;
*/
int bordaCountVoting(int** votes) {
  int max = sum(votes,0);
  int elect = 0;
  int i = 1;
  int inter = 0;

  /*@ loop invariant 0 <= i <= C;
    @ loop invariant \forall integer k; 0 <= k < i && k != elect ==> sum(votes,0,V,elect) > sum(votes,0,V,k);
    @ loop invariant max == sum(votes,0,V,elect);
    @ loop assigns i,max,inter,elect;
    @ loop variant C - i;*/
  while(i < C) {
    inter = sum(votes,i);
    if(max < inter) {
      max = inter;
      elect = i;
    } else if(max == inter) {
      return C;
    }
    i++;
  }
  return elect;
}

/*@ predicate same_array{L1,L2}(int* a, int* b, integer begin, integer end) =
      \forall integer k; begin <= k < end ==> \at(a[k],L1) == \at(b[k],L2);
*/

/*@ predicate same_array_e{L1,L2}(int** a, int** b, integer begin, integer end, integer count) =
      \forall integer k; begin <= k < end ==> same_array{L1,L2}(\at(a[k],L1), \at(b[k],L2), 0, count);
*/

/*@ predicate swap{L1, L2}(int** a, int** b, integer begin, integer i, integer j, integer end, integer count) =
      begin <= i < end && begin <= j < end &&
      same_array{L1,L2}(\at(a[i],L1), \at(b[j],L2), 0, count) &&
      same_array{L1,L2}(\at(a[j],L1), \at(b[i],L2), 0, count) &&
      \forall integer k; begin <= k < end && k != i && k != j ==> same_array{L1,L2}(\at(a[k],L1), \at(b[k],L2), 0, count);
*/

/*@ inductive same_elements{L1, L2}(int** a, int** b, integer begin, integer end, integer count) {
      case refl{L1, L2}:
        \forall int** a, int** b, integer begin, end, count;
        same_array_e{L1,L2}(a, b, begin, end, count) ==>
        same_elements{L1,L2}(a, b, begin, end, count);
      case swap{L1, L2}: \forall int** a, int** b, integer begin, i, j, end, count;
        swap{L1, L2}(a, b, begin, i, j, end, count) ==>
        same_elements{L1, L2}(a, b, begin, end, count);
      case trans{L1, L2, L3}: \forall int** a, int** b, int** c, integer begin, end, count;
        same_elements{L1, L2}(a, b, begin, end, count) ==>
        same_elements{L2, L3}(b, c, begin, end, count) ==>
        same_elements{L1, L3}(a, c, begin, end, count);
}*/


/*@ lemma sum3{L} :
       \forall int** t, integer i, j, k, c;
         0 <= i <= j <= k ==>
         sum(t,i,k,c) == sum(t,i,j,c) + sum(t,j,k,c);
*/

/*@   lemma sum_4 {L1,L2}:
       \forall int** t1, int** t2, integer i, j, c;
         (\forall integer k; i <= k < j ==> \at(t1[k][c],L1) == \at(t2[k][c],L2)) ==>
         sum{L1}(t1,i,j,c) == sum{L2}(t2,i,j,c);
*/

// relational property we want for sum
/*@   lemma sum_ext{L1,L2} :
  @     \forall int** f, int** g, integer i, j, c, count;
  @     0 <= c < count ==>
  @     0 <= i <= j ==>
  @     same_elements{L1,L2}(f,g,i,j,count) ==>
  @     sum{L1}(f, i, j, c) == sum{L2}(g, i, j, c);
*/
