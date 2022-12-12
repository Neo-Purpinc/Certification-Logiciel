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
/*@
assigns \nothing;
ensures \result <==> c \in \union(('a' .. 'z'), ('A' .. 'Z'), ('0' .. '9'));
*/
int is_alpha_num(char c) {
    return is_lower_alpha(c) || is_upper_alpha(c) || is_digit(c);
}
