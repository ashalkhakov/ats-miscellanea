(* translated from SML by Artyom Shalkhakov (and specialized to characters)
** (original SML implementation is by John Reppy, http://www.cs.uchicago.edu/~jhr/)
*)

#define ATS_STALOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

abstype charset

(* ****** ****** *)

fun charset_is_empty (x: charset):<> bool
fun charset_is_universe (x: charset):<> bool

fun charset_empty ():<> charset
fun charset_universe ():<> charset

fun charset_sing (x: char):<> charset
fun charset_range {a,b:char | a <= b} (a: char a, b: char b):<> charset

// yields an arbitrary character drawn from [x] provided that [x] is not empty
fun charset_extract (x: charset, y: &char? >> char c):<> #[c:char] bool (c <> NUL)

fun charset_test (x: charset, y: char):<> bool

(* ****** ****** *)

fun charset_complement (x: charset):<> charset
fun charset_union (x: charset, y: charset):<> charset
fun charset_intersect (x: charset, y: charset):<> charset
fun charset_difference (x: charset, y: charset):<> charset

(* ***** ***** *)

fun compare_charset_charset (x: charset, y: charset):<> Sgn
overload compare with compare_charset_charset

(* ****** ****** *)

fun print_charset (x: charset): void
overload print with print_charset

(* ****** ****** *)
