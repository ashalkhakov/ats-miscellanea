staload "SATS/charset.sats"
staload "SATS/linset.sats"

#define ATS_STALOADFLAG 0

abstype RE

// doesn't match anything at all
fun re_phi ():<> RE
// matches the empty string
fun re_emp ():<> RE

// any single character
fun re_any ():<> RE
fun re_lit (c: c1har):<> RE
fun re_rng {c1,c2:char | c1 <> NUL; c2 <> NUL; c1 <= c2} (c1: char c1, c2: char c2):<> RE

fun re_alt (r1: RE, r2: RE):<> RE
fun re_int (r1: RE, r2: RE):<> RE
fun re_cat (r1: RE, r2: RE):<> RE
fun re_clo (r: RE):<> RE
fun re_opt (r: RE):<> RE
fun re_neg (r: RE):<> RE

(* ****** ****** *)

fun re_is_emp (r: RE):<> bool
fun re_is_phi (r: RE):<> bool
fun re_factoring (r: RE):<> List_vt charset // actually a set
fun re_deriv (r: RE, c: c1har):<> RE

// does the string match the regexp?
fun re_match {n,k:nat} (r: RE, s: &strbuf (n, k)):<> bool

fun print_re (r: RE): void
overload print with print_re

fun compare_re_re (r1: RE, r2: RE):<> Sgn
overload compare with compare_re_re

(*
fun prerr_re (r: RE): void
*)

(* ****** ****** *)

(*

// vector of regular expressions
absviewtype REvec (int)
fun revec_of_list_vt {n:nat} (x: list_vt (RE, n)):<> REvec n
fun revec_deriv {n:nat} (rv: REvec n, c: c1har):<> REvec n
fun revec_is_emp {n:nat} (rv: !REvec n):<> bool
fun revec_is_phi {n:nat} (rv: !REvec n):<> bool
fun revec_factoring {n:nat} (rv: !REvec n):<> List_vt charset

*)
