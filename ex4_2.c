#include "stdlib.h"
#include "stdio.h"
#include "limits.h"
/*@
requires size >= 2;
requires \valid(&tab[0..size-1]);
requires \forall int i; 0 <= i < size ==> \forall int j; 0 <= j < size ==> -INT_MAX <= tab[i] - tab[j] <= INT_MAX;
assigns \nothing;
ensures \forall int i; 0 <= i < size ==> \forall int j; 0 <= j < size ==> i != j ==> \result <= \abs(tab[i] - tab[j]);
ensures \exists int i; 0 <= i < size && \exists int j; 0 <= j < size && i != j && \result == \abs(tab[i] - tab[j]);
*/
int min_diff(int tab[], int size) {
    int i, j;
    int min = INT_MAX;
    /*@
    loop invariant 0 <= i <= size;
    loop invariant \forall int k; 0 <= k < i ==> \forall int l; 0 <= l < size ==> k != l ==> min <= \abs(tab[k] - tab[l]);
    loop assigns i, min;
    loop variant size-i;
    */
    for (i = 0; i < size; i++) {
        /*@
        loop invariant 0 <= j <= size;
        loop invariant \forall int l; 0 <= l < j ==> j != l ==> min <= \abs(tab[i] - tab[l]);
        loop assigns j, min;
        loop variant size-j;
        */
        for (j = 0; j < size; j++) {
            if (i != j && abs(tab[i] - tab[j]) < min) {
                min = abs(tab[i] - tab[j]);
            }
        }
    }
    return min;
}