#include "stdlib.h"

/*@
    requires 0 < n;
    requires \valid(a+(0..n-1));
    requires \valid(b+(0..n-1));
    requires \valid(sum+(0..n-1));
    requires \separated(a+(0..n-1),b+(0..n-1),sum+(0..n-1));
    requires \forall integer i; 0 <= i < n ==> a[i] + b[i] < INT_MAX && a[i] + b[i] > INT_MIN;
    assigns sum[0..n-1];
    ensures \forall integer i; 0 <= i < n ==> sum[i] == a[i] + b[i];
*/
void sum_array(int* a, int* b, int* sum, int n){
    int i;
    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer j; 0 <= j < i ==> sum[j] == a[j] + b[j];
        loop assigns i, sum[0..n-1];
        loop variant n-i;
    */
    for (i = 0; i < n; i++){
        sum[i] = a[i] + b[i];
    }
    return;
}