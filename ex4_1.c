#include "stdlib.h"

/*@
requires size_a > 0;
requires size_b > 0;
requires size_a + size_b <= INT_MAX;
requires \valid(&a[0..size_a-1]);
requires \valid(&b[0..size_b-1]);
requires \valid(&concat[0..size_a+size_b-1]);
requires \separated(&a[0..size_a-1], &b[0..size_b-1], &concat[0..size_a+size_b-1]);
assigns concat[0..size_a+size_b-1];
ensures \forall integer i; 0 <= i < size_a ==> concat[i] == a[i];
ensures \forall integer i; 0 <= i < size_b ==> concat[size_a+i] == b[i];
*/
void concat(int* a, int* b, int* concat, int size_a, int size_b){
    int i;
    /*@
    loop invariant 0 <= i <= size_a;
    loop invariant \forall integer j; 0 <= j < i ==> concat[j] == a[j];
    loop assigns i, concat[0..size_a-1];
    loop variant size_a-i;
    */
    for (i = 0; i < size_a; i++){
        concat[i] = a[i];
    }
    /*@
    loop invariant 0 <= i <= size_b;
    loop invariant \forall integer j; 0 <= j < i ==> concat[size_a+j] == b[j];
    loop assigns i, concat[size_a..size_a+size_b-1];
    loop variant size_b-i;
    */
    for (i = 0; i < size_b; i++){
        concat[size_a+i] = b[i];
    }
    return;
}