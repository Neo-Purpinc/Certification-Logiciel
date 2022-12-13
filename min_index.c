
#include "stdlib.h"

/*@
requires INT_MAX > n > 0;
requires \valid(&a[0..n-1]);
assigns \nothing;
ensures 0 <= \result < n;
ensures \forall integer i; 0 <= i < n ==> a[i] >= a[\result];
*/
int min_index(int* a, int n){
    int i, min = 0;
    /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0 <= j < i ==> a[j] >= a[min];
    loop assigns i, min;
    loop variant n-i;
    */
    for (i = 0; i < n; i++){
        if (a[i] < a[min]) min = i;
    }
    return min;
}