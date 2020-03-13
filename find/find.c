/*@ requires \valid(t+(0 .. n-1));
  @ requires n >= 0;
  @ assigns \nothing;
  @ behavior some:
	assumes \exists integer i; 0 <= i < n && t[i] == val;
	ensures 0 <= \result < n;
	ensures t[\result] == val;
	ensures \forall integer i; 0 <= i < \result ==> t[i] != val;
  @ behavior none:
	assumes \forall integer i; 0 <= i < n ==> t[i] != val;
	ensures \result == n;
  @ complete behaviors;
  @ disjoint behaviors;
*/
int find(int * t, int n, int val){
	int i = 0;
	
	/*@ loop invariant 0 <= i <= n;
	  @ loop invariant \forall integer k; 0 <= k < i ==> t[k] != val;
	  @ loop assigns i;
	  @ loop variant n-i;
	*/
	for(i = 0; i < n; i++){
		if(t[i] == val){
			return i;		
		}
	}
	return n;
}
