(* type checking *)
#include "shared/types.hats"
staload "shared/types.sats"
staload "shared/disj.sats"
staload "shared/tas.sats"
staload "frontend/absyn.sats"

// type language reified as a datatype
datatype TY (ty) =
  | TYint (int)
  | {t1,t2:ty} TYfun (t1 ->> t2) of (TY t1, TY t2)

(* typing context *)

abstype ctx_t (env)

// yields an empty context
fun ctx_empty ():<> ctx_t (nil)

// add an annotation to the context
fun ctx_extend {G:env} {t:ty}
  (id: string, t: TY t, env: ctx_t G):<> ctx_t (t :: G)

// lookup a type in the context (will fail if [id] is free)
fun ctx_lookup {G:env}
  (id: string, env: ctx_t G)
  :<> Option_vt ([t:ty] @(TY t, var0_t (G, t)))

(* the type-checking function *)

// check type for well-formedness
fun tywf (x: TY0): Option_vt ([t:ty] TY t)

// check the type of [e] in context [env]
fun tycheck {G:env} (e: EXP0, env: ctx_t G)
  : Error_vt ([t:ty] @(TY t, EXP (G, t)))

// check the type of [e] in an empty context
fun tycheckZ (e: EXP0)
  : Error_vt ([t:ty] @(TY t, EXP (nil, t)))
