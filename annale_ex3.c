/*@
requires \valid(a + (0..size-1));
requires size >= 0;
assigns \nothing;
ensures \result == 1 || \result == 0;
*/
int array_parity(int* a, int size){
    int i;
    /*@
    loop invariant 0 <= i <= size;
    loop invariant (\forall integer j; 0 <= j < i ==> (j % 2 == 0 ==> a[j] % 2 == 0) && (j % 2 == 1 ==> a[j] % 2 == 1));
    loop assigns i;
    loop variant size-i;
    */
    for (i = 0; i < size; i++){
        if (i % 2 == 0 && a[i] % 2 != 0) return 0;
        if (i % 2 == 1 && a[i] % 2 != 1) return 0;
    }
    return 1;
}