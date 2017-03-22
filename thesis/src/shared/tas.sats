(* typed abstract syntax (our intermediate representation) *)
#include "shared/types.hats"
staload "shared/types.sats"

// a variable has type t in context G (in our case, variables
// appear at most once in a context), see also rules for |-0
// FIXME: figure a way to make use of an abstract datatype here?
typedef var_t (G:env, t:ty, n:int) = (VAR (G, t, n) | int n)
typedef var0_t (G:env, t:ty) = [n:nat] var_t (G, t, n)

// NOTE: we don't have a case for integers!
// see also rules for |-
datatype EXP1 (G:env, ty, int) =
// TODO: add these
//  | EXPint (G, int) of int
//  | EXPadd (G, int) of (EXP (G, int), EXP (G, int))
  | {t:ty} {n:nat} EXPvar (G, t, n+1) of var_t (G, t, n)
  | {t1,t2:ty} {n:nat} EXPlam (G, t1 ->> t2, n+1) of EXP1 (t1 :: G, t2, n)
  | {t1,t2:ty} {n1,n2:nat}
    EXPapp (G, t2, n1+n2+1) of (EXP1 (G, t1 ->> t2, n1), EXP1 (G, t1, n2))
  | EXPtrue (G, tybool, 0)
  | EXPfalse (G, tybool, 0)
  | {t:ty} {n1,n2,n3:nat}
    EXPif (G, t, n1+n2+n3+1) of
      (EXP1 (G, tybool, n1), EXP1 (G, t, n2), EXP1 (G, t, n3))
typedef EXP (G:env, t:ty) = [n:nat] EXP1 (G, t, n)

(* ****** ****** *)

fun var_one {G:env} {t:ty} ():<> var_t (t :: G, t, 0)
fun var_shi {G:env} {t1,t2:ty} {n:nat}
  (v: var_t (G, t1, n)):<> var_t (t2 :: G, t1, n+1)

// FIXME: the signature is not strong enough, we should
// also show that G = t :: G' for some G'
fun var_is_one {G:env} {t:ty} {n:nat}
  (v: var_t (G, t, n)):<> bool (n == 0)

// FIXME: the signature is not strong enough, we should
// also show that G = t' :: G' for some G' and t'
fun var_is_shi {G:env} {t:ty} {n:nat}
  (v: var_t (G, t, n)):<> bool (n > 0)

fun var_unshi {G:env} {t1,t2:ty} {n:pos}
  (v: var_t (t2 :: G, t1, n)):<> var_t (G, t1, n-1)

(* ****** ****** *)

// fun show_ty {t:ty} (t: TY t): string
fun show_exp {G:env} {t:ty} (e: EXP (G, t)): string
