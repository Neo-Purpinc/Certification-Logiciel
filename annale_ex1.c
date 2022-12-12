/*@
ensures \result == \old(a) || \result == \old(b);
ensures \result <= \old(a);
ensures \result <= \old(b);
assigns \nothing;
*/
int min2(int a, int b){
    if (a <= b) return a;
    else return b;
}

/*@
ensures \result == \old(a) || \result == \old(b) || \result == \old(c);
ensures \result <= \old(a);
ensures \result <= \old(b);
ensures \result <= \old(c);
assigns \nothing;
*/
int min3(int a, int b, int c){
    return min2(min2(a, b), c);
}

/*@
ensures \result == \old(a) || \result == \old(b) || \result == \old(c) || \result == \old(d);
ensures \result <= \old(a);
ensures \result <= \old(b);
ensures \result <= \old(c);
ensures \result <= \old(d);
assigns \nothing;
*/
int min4(int a, int b, int c, int d){
    return min2(min2(a, b), min2(c, d));
}