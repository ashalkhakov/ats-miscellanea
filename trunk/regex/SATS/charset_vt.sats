(* linear character set (experimental code)
** Written by Artyom Shalkhakov on Apr 3, 2011.
*)

(* ****** ****** *)

absviewtype charset_vt

(* ****** ****** *)

fun charset_vt_empty ():<> charset_vt
fun charset_vt_universe ():<> charset_vt
fun charset_vt_sing (x: char):<> charset_vt
fun charset_vt_range {a,b:char | a <= b} (a: char a, b: char b):<> charset_vt
fun charset_vt_free (x: charset_vt):<> void

(* ****** ****** *)

fun charset_vt_complement (x: charset_vt):<> charset_vt
fun charset_vt_union (x: charset_vt, y: charset_vt):<> charset_vt
fun charset_vt_intersect (x: charset_vt, y: charset_vt):<> charset_vt

(* ****** ****** *)

fun print_charset (x: !charset_vt): void
overload print with print_charset

(* ****** ****** *)
