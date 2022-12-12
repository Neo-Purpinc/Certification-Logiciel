/*@
assigns \nothing;
ensures \result <==> c \in ('a' .. 'z');
*/
int is_lower_alpha(char c) {
    return c >= 'a' && c <= 'z';
}
/*@
assigns \nothing;
ensures \result <==> c \in ('A' .. 'Z');
*/
int is_upper_alpha(char c) {
    return c >= 'A' && c <= 'Z';
}
/*@
assigns \nothing;
ensures \result <==> c \in ('0' .. '9');
*/
int is_digit(char c) {
    return c >= '0' && c <= '9';
}

enum kind { LOWER, UPPER, DIGIT, OTHER };

/*@
assigns \nothing;
ensures \result == LOWER <==> c \in ('a' .. 'z');
ensures \result == UPPER <==> c \in ('A' .. 'Z');
ensures \result == DIGIT <==> c \in ('0' .. '9');
ensures \result == OTHER <==> !(c \in \union(('a' .. 'z'), ('A' .. 'Z'), ('0' .. '9')));
*/
enum kind get_char_kind(char c) {
    if (is_lower_alpha(c)) {
        return LOWER;
    } else if (is_upper_alpha(c)) {
        return UPPER;
    } else if (is_digit(c)) {
        return DIGIT;
    } else {
        return OTHER;
    }
}

/*@
assigns \nothing;
*/
void test() {
    enum kind k = get_char_kind('h');
    //@ assert k == LOWER;
    k = get_char_kind('T');
    //@ assert k == UPPER;
    k = get_char_kind('5');
    //@ assert k == DIGIT;
    k = get_char_kind('#');
    //@ assert k == OTHER;
}