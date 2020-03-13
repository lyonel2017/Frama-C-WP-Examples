/*@ requires \valid_read(s + (0 .. n - 1));
  @ requires n >= 0 && n % 4 == 0;
  @ assigns \nothing;
  @ ensures 0 <= \result <= n;
  @ ensures 0 <= \result < n ==> s[\result] == '\0';
  @ ensures \forall integer i; 0 <= i < \result ==> s[i] != '\0';*/
int strnlen_ref (char *s, int n){
  int i = 0;
  /*@ ghost int p = 0;*/
  /*@ loop invariant i == p*4;
    @ loop invariant 0 <= i <= n;
    @ loop invariant \forall integer k; 0 <= k < i ==> s[k] != '\0';
    @ loop assigns i,p;
    @ loop variant n - i;
  */
 while (i < n) {
   if (s[i] == '\0') return i; i++;
   if (s[i] == '\0') return i; i++;
   if (s[i] == '\0') return i; i++;
   if (s[i] == '\0') return i; i++;
   /*@ ghost p = p + 1;*/
  }
  return n;
}
