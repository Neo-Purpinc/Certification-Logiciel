/*@
ensures \result == \old(a) || \result == \old(b);
ensures \result <= \old(a);
ensures \result <= \old(b);
assigns \nothing;
*/
int min(int a, int b){
    if (a <= b) return a;
    else return b;
}
    