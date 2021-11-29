void swap(int* x, int* y){
  int t = *x;
  * x = *y;
  *y = t;
}

void tamiser(int* arbre, int nœud, int n){
  int k = nœud;
  int j = 2k;
  while(j ≤ n){
    if (j < n && arbre[j] < arbre[j+1])
    j := j+1;
    else if(arbre[k] < arbre[j]){
      swap(arbre+k, arbre+j);
      k = j;
      j = 2k;
    }
    else
    j := n+1;
  }
  return;
}

void triParTas(int* arbre, int longueur){
  for(int i = longueur/2; i < 0; i--){
    tamiser(arbre, i, longueur);
  }
  for(int i = longueur-1; i <= 1; i--){
    swap(arbre+i, arbre+1);
    tamiser(arbre, 0, i-1);
  }
  return;
}
