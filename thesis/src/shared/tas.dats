(* typed abstract syntax *)
#include "shared/types.hats"
staload "shared/types.sats"
staload "shared/tas.sats"

#define ATS_DYNLOADFLAG 0 // no dynamic loading

implement var_one {G} {t} () = (VARone () | 0)

implement var_shi {G} {t1,t2} {n} (v) = let
  val+ (pf | v) = v
in (VARshi pf | v+1) end

implement var_is_one {G} {t} {n} (v) = let
  val+ (pf | v) = v
in v = 0 end

implement var_is_shi {G} {t} {n} (v) = let
  val+ (pf | v) = v
in v > 0 end

implement var_unshi {G} {t1,t2} {n} (v) = let
  val+ (pf | v) = v
  prval VARshi pf = pf
in (pf | v-1) end

(* ****** ****** *)

fun show_var {G:env} {t:ty} {n:nat} (v: var_t (G, t, n)): string = let
  val+ (pf | v) = v
in "var(" + (tostring v + ")") end

// FIXME: all names are lost...
implement show_exp {G} {t} (e) = case+ e of
  | EXPvar v => show_var v
  | EXPlam e => "lam(" + (show_exp e + ")")
  | EXPapp (e1, e2) => "app(" + (show_exp e1 + (", " + (show_exp e2 + ")")))
