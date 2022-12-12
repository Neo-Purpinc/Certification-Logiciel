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
requires \valid(a);
requires \valid(b);
requires \separated(a,b);
assigns *a;
assigns *b;
ensures *a <= *b;
ensures {*a,*b} == \old({*a,*b});
*/
void order2(int* a, int* b){
  if (*a > *b) {
    swap(a,b);
  }
  return;
}

/*@
requires \valid(a);
requires \valid(b);
requires \valid(c);
requires \separated(a,b,c);
assigns *a;
assigns *b;
assigns *c;
ensures (*b == \old(*a) <==> \old(*b <= *a <= *c || *c <= *a <= *b));
ensures (*b == \old(*b) <==> \old(*a <= *b <= *c || *c <= *b <= *a));
ensures (*b == \old(*c) <==> \old(*a <= *c <= *b || *b <= *c <= *a));
ensures (*a <= *b);
ensures (*b <= *c);
*/
void order3(int* a, int* b, int* c){
    order2(a,b);
    order2(b,c);
    order2(a,b);
    return;
}

//@ assigns \nothing;
void test(){
    int a = 1, b = 3, c = 2;
    order3(&a,&b,&c);
    //@ assert a == 1 && b == 2 && c == 3;

    a = 2, b = 1, c = 0;
    order3(&a,&b,&c);
    //@ assert a == 0 && b == 1 && c == 2;

    a = 2, b = 2, c = 1;
    order3(&a,&b,&c);
    //@ assert a == 1 && b == 2 && c == 2;

    a = 1, b = 2, c = 1;
    order3(&a,&b,&c);
    //@ assert a == 1 && b == 1 && c == 2;
}