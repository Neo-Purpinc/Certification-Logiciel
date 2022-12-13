
/*@
requires n > 0;
requires \valid(&a[0..n-1]);
assigns \nothing;
ensures \result == -1 <==> (\forall integer i; 0 <= i < n ==> a[i] != x);
ensures 0 <= \result < n <==> (\exists integer i; 0 <= i < n && a[i] == x);
*/
int get_element_index(int* a, int n, int x){
    int i;
    /*@
    loop invariant 0 <= i <= n;
    loop invariant (\forall integer j; 0 <= j < i ==> a[j] != x);
    loop assigns i;
    loop variant n-i;
    */
    for (i = 0; i < n; i++){
        if (a[i] == x) return i;
    }
    return -1;
}