/*@
requires \valid(&s[0..size-1]) && \valid(&t[0..size-1]) && size >= 0;
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