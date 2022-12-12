/*@
    requires 0 <= n <= 1000;
    assigns \nothing;
    ensures 2*\result == n*(n+1);
*/
int sum(int n){
    int s = 0;
    int i;
    /*@
        loop invariant 0 <= i <= n+1;
        loop invariant 2*s == i*(i-1);
        loop assigns i, s;
        loop variant n-i;
    */
    for (i = 0; i <= n; i++){
        s += i;
    }
    return s;
}