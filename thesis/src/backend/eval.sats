(* evaluation *)
#include "shared/types.hats"
staload "shared/types.sats"
staload "shared/tas.sats"

abstype val_t (ty)
abstype env_t (env)

fun env_empty ():<> env_t (nil)
fun env_cons {G:env} {t:ty} (v: val_t t, e: env_t G):<> env_t (t :: G)

fun print_val {t:ty} (v: val_t t): void
overload print with print_val

fun eval {G:env} {t:ty} (env: env_t G, e: EXP (G, t)): val_t t
fun evalZ {t:ty} (e: EXP (nil, t)): val_t t
