/*@
requires \valid(&s[0..size-1]) && \valid(&t[0..size-1]) && size >= 0;
requires \separated(&s[0..size-1], &t[0..size-1]);
assigns t[0..size-1];
ensures (\forall integer i; 0 <= i < size ==> t[i] == s[i]);
*/
void array_copy(int* s, int* t, int size){
    int i;
    /*@
    loop invariant 0 <= i <= size;
    loop invariant (\forall integer j; 0 <= j < i ==> t[j] == s[j]);
    loop assigns i;
    loop assigns t[0..size-1];
    loop variant size-i;
    */
    for (i = 0; i < size; i++){
        t[i] = s[i];
    }
}