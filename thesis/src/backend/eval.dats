(* evaluation *)
#include "shared/types.hats"
staload "shared/types.sats"
staload "shared/tas.sats"
staload "backend/eval.sats"

#define ATS_DYNLOADFLAG 0 // no dynamic loading

datatype VAL1 (ty, int) =
//  | VALint (int) of int
  | VALtrue (tybool, 0)
  | VALfalse (tybool, 0)
  | {G:env} {t1,t2:ty} {n,m:nat}
    VALclo (t1 ->> t2, m+1) of (ENV (G, n), EXP1 (t1 :: G, t2, m))

and ENV (env, int) =
  | ENVnil (nil, 0)
  | {G:env} {t:ty} {m,n:nat}
    ENVcons (t :: G, n+1) of (VAL1 (t, m), ENV (G, n))
typedef ENV (G:env) = [n:nat] ENV (G, n)
typedef VAL (t:ty) = [n:nat] VAL1 (t, n)

assume val_t (t:ty) = VAL t
assume env_t (G:env) = ENV G

implement env_empty () = ENVnil ()
implement env_cons (v, e) = ENVcons (v, e)

(* ****** ****** *)

(* evaluationn: env1, e1 --> env1, e2
 * that is, e1 in env1 evaluates to e2 in env1
 * env ::= 0 | x=e; env
 * where 0 is the nil environment, x ranges over variables,
 * e over terms
 *
 * values are constants, lambdas and closures
 * a closure is a pair, (env, term) where
 * term may involve free variables that are
 * bound in env
 *
 * here we show that evaluation is a relation
 * between environment+term and values (the arrow
 * denoting evaluation is decorated with the
 * number of "steps" we need to take):
 *
 *    env(x) = e
 * -----------------(red-var)
 * env, x -->1 e
 *
 * {E:ctx} {t:trm} REDvar (E, t, t, 0) of IN (E, t)
 *
 * ------------------------(red-bool1)
 * env, true -->1 true
 *
 * {E:ctx} REDbool1 (E, true, true, 0)
 *
 * --------------------------(red-bool2)
 * env, false -->1 false
 *
 * {E:ctx} REDbool2 (E, false, false, 0)
 *
 * -----------------------(red-lam)
 * env, \x.t -->1 \x.t
 *
 * {E:ctx} {e:trm} REDlam (E, lm e, lm e, 0)
 *
 *    env, e1 -->n e1'
 * --------------------------(red-app1)
 * env, e1 e2 -->(n+1) e1' e2
 *
 * {E:ctx} {e1, e2, e1':trm} {n:nat}
 *    REDapp1 (E, app(e1, e2), app(e1', e2), n+1) of
 *      RED (E, e1, e1', n)
 *
 *    env, e2 -->n e2'
 * -------------------------(red-app2)
 * env, e1 e2 -->(n+1) e1 e2'
 *
 * {E:ctx} {e1, e2, e2':trm} {n:nat}
 *   REDapp2 (E, app(e1, e2), app(e1, e2'), n+1) of
 *     RED (E, e2, e2', n)
 *
 * ----------------------------------(red-app3)
 * env, (\x.e1) e2 -->1 (env;x=e2, e1) -- closure is a value too
 *
 * {E:ctx} {e1, e2:trm} {n:nat}
 *   REDapp3 (E, app(lm e1, e2), e3, n+1) of
 *     RED (e2 :: E, e2)
 *
 * env, e1 -->n true
 * ----------------------(if1)
 * env, if e1 then e2 else e3 -->(n+1) e2
 *
 * env, e1 -->n false
 * -----------------------(if2)
 * env, if e1 then e2 else e3 -->(n+1) e3
 *
 * TODO: sample derivations
 * FIXME: can we capture this relation in ATS?
 *)

(* more traditional (?)
 * we view evaluation as a relation between two terms (contexts are implicit)
 *
 * eval (term a, term a, int)
 *   forall e1:term (term a->term b), e2:term (term a),
 *     f:term a->term b, v2:term a, v: term b, n1,n2,n3:nat.
 *     evalapp (app(e1, e2), v, n1+n2+n3+1)
 *       of evalapp (e1, f, n1), evalapp (e2, v2, n2),
 *            evalapp (app(f1,v2), v, n3)
 *
 *   forall e:term a->term b. evallam (e, e, 0)
 *
 *   evaltrue (true, true, 0)
 *   evalfalse (false, false, 0)
 *
 *   forall a:term bool,b,c:term a, n:nat.
 *     evalif1 (if(a,b,c),b,n+1) of eval (a, true, n)
 *   forall a:term bool,b,c:term a, n:nat.
 *     evalif2 (if(a,b,c),c,n+1) of eval (a, false, n)
 *
 * big-step operational semantics show how a term
 * is evaluated to a value in context
 * - values are lambdas and booleans
 * - every value has a "size" (?)
 *
 * p ::= nil | p,x=v
 *
 * ---------------(eval-var)
 * p |- v ==> p(v)
 *
 * ------------(eval-const)
 * p |- c ==> c
 *
 * p |- e1 ==> true    p |- e2 ==> w
 * ---------------------------------(if1)
 * p |- if(e1, e2, e3) ==> w
 *
 * p |- e1 ==> false   p |- e3 ==> w
 * ---------------------------------(if2)
 * p |- if(e1, e2, e3) ==> w
 *
 * p |- e1 ==> \x.e  p |- e2 ==> w   p, x=w |- e ==> r
 * --------------------------------------------------(app)
 *    p |- e1 e2 ==> r
 *
 * ------------------(lam)
 * p |- \x.e ==> \x.e
 *)

(* ****** ****** *)

fun evalVar {G:env} {t:ty} {n,m:nat} .<m>.
  (env: ENV (G, n), x: var_t (G, t, m))
  :<> VAL t = if var_is_one x then let
  val (VARone () | _) = x
  val ENVcons (v, _) = env
in v end
else let
  val (VARshi pf | _) = x
  val ENVcons (_, env) = env
in evalVar (env, var_unshi x) end

(*
 * the size of a term in an environment
 *
 * size : (env, exp) -> nat
 * size(env,EXPtrue ()) = 0
 * size(env,EXPfalse ()) = 0
 * size(env,EXPif (a,b,c)) = size(env, a) + size(env, b) + size(env, c) + 1
 * size(env,EXPlam e) = size(e)+1
 * size(env,EXPvar x) = size_val(lookup (env, x))+1
 * size(env,EXPapp (e1, e2)) = size (env, e1) + size (env, e2) + 1
 *
 * size_val : val -> int
 * size_val(VALtrue ()) = 0
 * size_val(VALfalse ()) = 0
 * size_val(VALclo (env, e)) = size (env, e)+1
 *
 * lookup : env, nat -> val
 * lookup(cons(x,xs),0) = x
 * lookup(cons(x,xs),n+1) = lookup(xs,n)
 *
 * the stumbling block is the expression of size()
 * in ATS
 *)

// we can't do it this way because
// termination depends on the size
// of the derivation
// when we invoke the application rule,
// the term grows bigger because we
// substitute the actual parameter for the formal one.
// so giving the size of the term as a termination
// metric won't suffice.
// what can we do?

fun eval' {G:env} {t:ty} {m:nat}
  (env: ENV G, e: EXP1 (G, t, m))
  : VAL t = case+ e of
  | EXPvar x => evalVar (env, x)
  | EXPlam e => VALclo (env, e)
  | EXPapp (e1, e2) => let
      val VALclo (env', body) = eval' (env, e1)
      val v = eval (env, e2)
    in eval' (ENVcons (v, env'), body) end
  | EXPtrue () => VALtrue ()
  | EXPfalse () => VALfalse ()
  | EXPif (a, b, c) => let
      val v = eval (env, a)
    in case+ v of
      | VALtrue () => eval (env, b)
      | VALfalse () => eval (env, c)
    end

(* ****** ****** *)

implement eval (env, e) = eval' (env, e)
implement evalZ (e) = eval' (ENVnil, e)

(* ****** ****** *)

implement print_val (v) = case+ v of
  | VALtrue () => print "true"
  | VALfalse () => print "false"
  | VALclo (_, _) => print "<closure>"
