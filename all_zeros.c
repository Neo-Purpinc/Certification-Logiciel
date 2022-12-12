/*@
requires \valid(&a[0..n-1]) && n >= 0;
assigns \nothing;
ensures \result == 1 <==> (\forall integer i; 0 <= i < n ==> a[i] == 0);
*/
int all_zeros(int* a, int n){
    int i;
    /*@
    loop invariant 0 <= i <= n;
    loop invariant (\forall integer j; 0 <= j < i ==> a[j] == 0);
    loop assigns i;
    loop variant n-i;
    */
    for (i = 0; i < n; i++){
        if (a[i] != 0) return 0;
    }
    return 1;
}