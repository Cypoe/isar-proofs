// kemit.k — the C99 compiler as a koru program (generated)
// arg-less invoke refuses: `src` unbound; the emit leg
// supplies it via --emit (quote of the source program)
tor emit { src: program } -> string
emit -> if(((src.tag == 30) && ((len(src.kids) == 3) && ((len(src.kids[0]) == 1) && ((src.kids[0][0].name == "main") && ((src.kids[1] == "main") && ((len(src.kids[2]) == 0) && ((src.kids[0][0].v.tag == 27) && ((len(src.kids[0][0].v.kids) == 1) && ((src.kids[0][0].v.kids[0].tag == 8) && ((len(src.kids[0][0].v.kids[0].kids) == 1) && ((src.kids[0][0].v.kids[0].kids[0].tag == 1) && (len(src.kids[0][0].v.kids[0].kids[0].kids) == 1))))))))))))) ("int main(void) { return " ++ (intToString(src.kids[0][0].v.kids[0].kids[0].kids[0]) ++ "; }")) else (0).x
