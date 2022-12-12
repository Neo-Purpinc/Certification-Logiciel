/*@
  requires \valid(&a[0..n-1]) && n >= 0;
  assigns a[0..n-1];
  ensures (\forall integer i; 0 <= i < n ==> a[i] == k);
*/
void array_fill(int* a, int n, int k){
    int i;
    /*@
    loop invariant 0 <= i <= n;
    loop invariant (\forall integer j; 0 <= j < i ==> a[j] == k);
    loop assigns i;
    loop assigns a[0..n-1];
    loop variant n-i;
    */
    for (i = 0; i < n; i++){
        a[i] = k;
    }
}