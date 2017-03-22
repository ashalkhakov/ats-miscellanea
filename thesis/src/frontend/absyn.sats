(* abstract syntax *)
staload "parcomb/posloc.sats"

typedef loc_t = location_t

datatype TY0_node =
  | TY0int
  | TY0fun of (TY0, TY0)

where TY0 = '{
  ty0_loc= location_t, ty0_node= TY0_node
} // end of [TY0]

fun print_ty0 (t: TY0): void
overload print with print_ty0

fun show_ty0 (t: TY0):<> string

fun ty0_int (loc: loc_t):<> TY0
fun ty0_fun (loc: loc_t, f: TY0, x: TY0):<> TY0

(* ****** ****** *)

// a raw term as we get it from our parser
// contains position info
datatype EXP0_node =
  | EXP0var of string
//  | EXP0let of (string, TY0, EXP0) // let binding form
  | EXP0lam of (string, TY0, EXP0)
  | EXP0app of (EXP0, EXP0)

where EXP0 = '{
  exp0_loc= location_t, exp0_node= EXP0_node
} // end of [EXP0]

fun print_exp0 (e: EXP0): void
overload print with print_exp0

fun show_exp0 (e: EXP0):<> string

fun exp0_var (loc: loc_t, name: string):<> EXP0
// fun exp0_let (loc: loc_t, name: string, t: TY0, b: EXP0):<> EXP0
fun exp0_lam (loc: loc_t, x: string, t: TY0, b: EXP0):<> EXP0
fun exp0_app (loc: loc_t, f: EXP0, x: EXP0):<> EXP0
