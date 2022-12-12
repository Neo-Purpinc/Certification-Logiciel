 /*@
requires \valid(p);
requires \valid(q);
assigns *p;
assigns *q;
ensures *p == \old(*q);
ensures *q == \old(*p);
 */
void swap(int* p, int* q){
  int tmp = *p;
  *p=*q;
  *q=tmp;
  return;
}
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
    

/*@
requires \valid(&a[0..n-1]) && n >= 0;
assigns \nothing;
ensures \result == 1 <==> (\forall integer i; 0 <= i < n ==> a[i] == 0);
*/
int all_zeros(int* a, int n){
    int i;
    /*@
    loop invariant 0 <= i <= n;
    loop invariant (\forall integer j; 0 <= j < i ==> a[j] == 0);
    loop assigns i;
    loop variant n-i;
    */
    for (i = 0; i < n; i++){
        if (a[i] != 0) return 0;
    }
    return 1;
}

/*@
  requires \valid(&a[0..n-1]) && n >= 0;
  assigns a[0..n-1];
  ensures (\forall integer i; 0 <= i < n ==> a[i] == k);
*/
void array_fill(int* a, int n, int k){
    int i;
    /*@
    loop invariant 0 <= i <= n;
    loop invariant (\forall integer j; 0 <= j < i ==> a[j] == k);
    loop assigns i;
    loop assigns a[0..n-1];
    loop variant n-i;
    */
    for (i = 0; i < n; i++){
        a[i] = k;
    }
}

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

/*@
requires \valid(&s[0..size-1]) && \valid(&t[0..size-1]) && size >= 0;
requires \separated(&s[0..size-1], &t[0..size-1]);
assigns \nothing;
ensures \result == 1 <==> (\forall integer i; 0 <= i < size ==> s[i] == t[i]);
*/
int array_equals(int *s, int* t, int size){
  int i;
  /*@
  loop invariant 0 <= i <= size;
  loop invariant (\forall integer j; 0 <= j < i ==> t[j] == s[j]);
  loop assigns i;
  loop variant size-i;
  */
  for (i = 0; i < size; i++){
    if (s[i] != t[i]) return 0;
  }
  return 1;
}

/*@

*/
int array_palindrome(int* a, int n){
  int i;
  /*@
  loop invariant 0 <= i <= n;
  loop invariant (\forall integer j; 0 <= j < i ==> a[j] == a[n-1-j]);
  loop assigns i;
  loop variant n-i;
  */
  for (i = 0; i < n; i++){
    if (a[i] != a[n-1-i]) return 0;
  }
  return 1;
}