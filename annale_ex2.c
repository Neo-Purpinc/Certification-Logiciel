/*@
requires \valid(t+(0..size-1));
requires size >= 0;
assigns \nothing;
ensures \result == 1 || \result == 0;
*/
int up_and_down(int* t, int size, int u){
    // verify if t is sorted from t[0] to t[u] and reverse sorted from t[u] to t[size-1]
    int i;
    /*@
    loop invariant 0 <= i <= size;
    loop invariant (\forall integer j; 0 <= j < i ==> (j < u ==> t[j] <= t[j+1]) && (j >= u ==> t[j] >= t[j+1]));
    loop assigns i;
    loop variant size-i;
    */
    for (i = 0; i < size; i++){
        if (i < u){
            if (t[i] > t[i+1]) return 0;
        } else {
            if (t[i] < t[i+1]) return 0;
        }
    }
    return 1;
}