#include "stdlib.h"
/*@
    requires \valid(a);
    requires \valid(b);
    requires \separated(a, b);
    assigns *a, *b;
    ensures *a == \old(*b);
    ensures *b == \old(*a);
*/
void swap(int* a, int* b){
    *a = *a + *b;
    *b = *a - *b;
    *a = *a - *b;
    return;
}