void swap(int* x, int* y){
  int t = *x;
  * x = *y;
  *y = t;
}

int partitionner(int* t, int premier, int dernier, int pivot){
  swap(t+pivot,t+dernier);
  int j = premier;
  for(int i = premier; i < dernier; i++){
    if(t[i] <=t[dernier]){
      swap(t+i,t+j);
      j++;
    }
  }
  swap(t+dernier,t+j);
  return j;
}

int choix_pivot(int* t, int premier, int dernier);   //retunr a pivot between premier and dernier

void tri_rapide(int* t, int premier, int dernier){
  if (premier < dernier){
    int pivot = choix_pivot(t, premier, dernier);
    pivot = partitionner(t, premier, dernier, pivot);
    tri_rapide(t, premier, pivot-1);
    tri_rapide(t,pivot+1, dernier);
  }
  return;
}
