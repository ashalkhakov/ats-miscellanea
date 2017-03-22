(* type-checking *)
#include "shared/types.hats"
staload "shared/types.sats"
staload "shared/disj.sats"
staload "shared/tas.sats"
staload "frontend/absyn.sats"
staload "frontend/trans.sats"

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

// equality on types (reflexivity)
dataprop TYEQ (ty, ty, bool) =
  | {t1,t2:ty} TYEQnone (t1, t2, false)
  | {t:ty} TYEQsome (t, t, true)

fun eq_ty_ty {t1,t2:ty} (a: TY t1, b: TY t2)
  : [b:bool] (TYEQ (t1, t2, b) | bool b) = case+ (a, b) of
  | (TYint (), TYint ()) => (TYEQsome () | true)
  | (TYfun (a1, a2), TYfun (b1, b2)) => begin
    case+ (eq_ty_ty (a1, b1), eq_ty_ty (a2, b2)) of
    | ((TYEQsome () | true), (TYEQsome () | true)) => (TYEQsome () | true)
    | (_, _) => (TYEQnone () | false)
    end
  | (_, _) => (TYEQnone () | false)

(* ****** ****** *)

datatype CTX (env, int) =
  | CTXnil (nil, 0)
  | {t:ty} {G:env} {n:nat} CTXcons (t :: G, n+1)
    of (string, TY t, CTX (G, n))
assume ctx_t (G:env) = [n:nat] CTX (G, n)

implement ctx_empty () = CTXnil ()
implement ctx_extend (id, t, e) = CTXcons (id, t, e)
implement ctx_lookup (id, e) = let
  fun loop {G:env} {n:nat} .<n>.
    (id: string, env: CTX (G, n)):<> Option_vt ([t:ty] @(TY t, var0_t (G, t))) =
    case+ env of
    | CTXnil () => None_vt ()
    | CTXcons (x, t, env) => if id = x then Some_vt @(t, var_one ())
      else let val l = loop (id, env)
      in case+ l of
        | ~Some_vt @(t, v) => Some_vt @(t, var_shi v)
        | None_vt () => (fold@ l; l)
      end
in
  loop (id, e)
end

(* ****** ****** *)

fun show_ty {t:ty} (a: TY t): string = case+ a of
  | TYint () => "int"
  | TYfun (t1, t2) => "fun(" + (show_ty t1 + (", " + (show_ty t2 + ")")))

(* ****** ****** *)

// TODO: we need two functions actually:
// - typecheck (exp, type, env): check that
//   [exp] can be assigned [type] in [env]
// - typeForExp (exp, env)

// to cut down some repetition
viewdef res_vt (G:env) = Error_vt ([t:ty] @(TY t, EXP (G, t)))

fun tywf_imp (x: TY0): Option_vt ([t:ty] TY t) =
  case+ x.ty0_node of
  | TY0int () => Some_vt (TYint ())
  | TY0fun (a, b) => let
      val ta = tywf_imp a
    in case+ ta of
      | ~Some_vt a => let
        val tb = tywf_imp b
      in case+ tb of
        | ~Some_vt b => Some_vt (TYfun (a, b))
        | None_vt _ => (fold@ tb; tb)
      end
      | None_vt _ => (fold@ ta; ta)
    end

fun tycheck_imp {G:env} (exp: EXP0, env: ctx_t G): res_vt G
  = case+ exp.exp0_node of
// if [t] is well-formed, then check that it is equal
// to the inferred type
// two functions:
// auxExp (ctx, exp0): exp
// auxExpCK (ctx, exp0, ty): exp <-- checks the type of
// expression that auxExp yields against ty
//  | EXP0ann (e, t) =>
//  | EXP0int i => check_int (i, env)
  | EXP0var id => check_var (id, env)
  | EXP0lam (id, t, b) => check_lam (id, t, b, env)
  | EXP0app (e1, e2) => check_app (e1, e2, env)

and check_var {G:env} (id: string, env: ctx_t G): res_vt G = let
  val v = ctx_lookup (id, env)
in case+ v of
  | ~Some_vt @(t, v) => InsRight_vt @(t, EXPvar v)
  | ~None_vt _ => InsLeft_vt ("identifier " + id + " is unbound")
end

and check_lam {G:env} (id: string, t: TY0, b: EXP0, env: ctx_t G)
  : res_vt G = let
  val wf = tywf t
in case+ wf of
  // type is well-formed
  | ~Some_vt t => let
    // check the body in the extended environment
    val tp = tycheck (b, ctx_extend (id, t, env))
  in case+ tp of
    | ~InsRight_vt @(t', b) => InsRight_vt @(TYfun (t, t'), EXPlam b)
    | InsLeft_vt _ => (fold@ tp; tp)
  end
  | ~None_vt _ => InsLeft_vt ("type [" + show_ty0 t + "] is not well-formed")
end

and check_app {G:env} (e1: EXP0, e2: EXP0, env: ctx_t G): res_vt G = let
  val tp1 = tycheck (e1, env)
in case+ tp1 of
  // make sure that the types match
  | ~InsRight_vt @(TYfun (t1, tb), e1) => let
      val tp2 = tycheck (e2, env)
    in case+ tp2 of
    | ~InsRight_vt @(t2, e2) => let
        val (pf | v) = eq_ty_ty (t1, t2)
      in
        if v then let
          prval TYEQsome () = pf
        in InsRight_vt @(tb, EXPapp (e1, e2)) end
        else let
          prval TYEQnone () = pf
        in InsLeft_vt ("type mismatch in application:" + show_ty t1 + " does not match " + show_ty t2) end
      end
      | InsLeft_vt _ => (fold@ tp2; tp2) // type error in e2
    end
  | ~InsRight_vt _ => InsLeft_vt "left-hand side operand is not a function"
  | _ => tp1 // type error in e1
end

// is the type well-formed?
// this is actually a total function at the moment
implement tywf (x) = tywf_imp x

// what we need here is essentially to build a typing derivation
// for [exp] in [env]
// fun tycheck {G:env}
//  (exp: EXP0, env: ctx_t G): res_vt G
implement tycheck (exp, env) = tycheck_imp (exp, env)

implement tycheckZ (exp) = tycheck_imp (exp, ctx_empty ())
