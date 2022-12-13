/*@
requires \valid(a+(0..size-1));
requires size >= 0;
assigns \nothing;
ensures \result == 1 || \result == 0;
*/
int is_array_palindrome(int* a, int size){
    int i;
    /*@
    loop invariant 0 <= i <= size/2;
    loop invariant (\forall integer j; 0 <= j < i ==> a[j] == a[size-1-j]);
    loop assigns i;
    loop variant size/2-i;
    */
    for (i = 0; i < size/2; i++){
        if (a[i] != a[size-1-i]) return 0;
    }
    return 1;
}