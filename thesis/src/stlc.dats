// see also:
// 1) Statically Verified Type-Preserving Code Transformations
// in Haskell, Louis-Julien Guillemette, Stefan Monnier
// 2) Typed Transformations of Typed Abstract Syntax,
// Arthur Baars, S. Doaitse Swierstra, Marcos Viera
(*
 * syntax
 * base type b ::= unit
 * types t ::= b | t1 -> t2
 * terms e ::= x | \x.e | e1(e2)
 * values v ::= x | \x.e
 * contexts G ::= 0 | G,x:t
 * (we use x for variables)
 *
 * the typing rules
 * ------------(type-one)
 * G,x:t |-0 x:t
 *
 *   G |-0 e:t
 * ------------(type-shift)
 * G,x:t |-0 e:t
 *
 * G |-0 e:t
 * ---------(var)
 * G |- e:t
 *
 * FIXME: where is the exchange rule? we'll assume it is nonexistent
 * (but I think it is implicit in |-0 rules)
 *
 * G, x:t1 |- e:t2
 * ---------------(type-lambda)
 * G |- \x.e:t1->t2
 *
 * G |- e1:t1->t2  G |- e2:t1
 * --------------------------(type-application)
 * G |- e1(e2):t2
 *
 * example derivations using the typing rules above
 * ------------(type-one)
 * 0,x:t |-0 x:t
 * -------------(var)
 * 0,x:t |- x:t
 * --------------(type-lambda)
 * 0 |- \x.x:t->t
 *
 * -----------------------(type-one)       -----------------------(type-one)
 * 0,x:t1->t2 |-0 x:t1->t2                 0,x:t1->t2,y:t1 |-0 y:t1
 * -----------------------(type-shift)     -----------------------(var)
 * 0,x:t1->t2,y:t1 |-0 x:t1->t2            0,x:t1->t2,y:t1 |- y:t1
 * ----------------------------(var)
 * 0,x:t1->t2,y:t1 |- x:t1->t2
 * ----------------------------------------------------------------(type-applic)
 * 0,x:t1->t2,y:t1 |- (x)y:t2
 * --------------------------(type-lambda)
 * 0,x:t1->t2 |- \y:t1.(x)y:t1->t2
 * -------------------------------(type-lambda)
 * 0 |- \x:t1->t2.\y:t1.(x)y:(t1->t2)->t1->t2
 *
 * natural operational semantics
 * ------------(eval-lambda)
 * \x.e => \x.e
 *
 * e1 => \x.e  e2 => v1   e[x/v1] => v2
 * ------------------------------------(eval-application)
 *           e1(e2) => v2
 *)

// TODO:
// + deal with substitution
// - formal specification in ATS/LF (more dataprops!)
// - interpreter in CPS (as an optimization,
//   as a way to show that implementation need
//   not duplicate specification)
// - add more base types (booleans at least),
//   perhaps even conjuction and disjunction
// - write a parser/type-checker/type inferencer
//   (this is not top-priority, but would be nice to have
//   to make things more realistic)
// - a number of program transformations?
//   (CPS, closure conversion, defunctionalization, etc.)
// future work:
// - more language features (mutability and polymorphism)
// - compilation to byte-code (abstract machine) or even raw assembly
// - relation to SSA
// - practical opportunity: an LLVM-like project with type safety!
//   another would be typed compiler to JS (for neat web programming)
//   see "the essense of javascript" by arjun guha

(* file structure of the project:
 * specs -- specifications
 * absyn -- abstract syntax (this is what our parser spits out)
 *  exp0 datatype, typ0 datatype
 * interp -- interpreter
 *  value datatype, interp function
 * parser -- parser
 *  string -> abstract syntax
 * trans -- type checker (and other transformations?)
 *  exp datatype, typ datatype
 *  tycheck: exp0 -> option exp
 *
 * dependencies:
 * trans, interp, parser -> absyn
 * interp -> trans
 *
 * front-end: absyn, parser, trans
 * back-end: interp
 *)

infixr :: ->>
datasort ty = int | ->> of (ty, ty)
datasort env = nil | :: of (ty, env)

// see the rules for |-0
dataprop VAR (G:env, ty, int) =
  | {t:ty} VARone (t :: G, t, 0)
  | {t1,t2:ty} {n:nat} VARshi (t2 :: G, t1, n+1) of VAR (G, t1, n)

(* ****** ***** *)

// a variable has type t in context G (in our case, variables
// appear at most once in a context), see also rules for |-0
typedef var_t (G:env, t:ty, n:int) = (VAR (G, t, n) | int n)
typedef var0_t (G:env, t:ty) = [n:nat] var_t (G, t, n)

// NOTE: we don't have a case for integers!
// see also rules for |-
datatype EXP (G:env, ty) =
//  | EXPint (G, int) of int
  | {t:ty} {n:nat} EXPvar (G, t) of var_t (G, t, n)
  | {t1,t2:ty} EXPlam (G, t1 ->> t2) of EXP (t1 :: G, t2)
  | {t1,t2:ty} EXPapp (G, t2) of (EXP (G, t1 ->> t2), EXP (G, t1))

(*
 * sample derivations.
 * 1. \x:int.x:int->int = \1 = EXPlam (EXPvar VARone): EXP (nil, int ->> int)
 * ------------------------
 * VARone (int :: nil, int)
 * ------------------------
 * EXPvar (int :: nil, int)
 * ------------------------
 * EXPlam (nil, int ->> int)
 *
 * 2. \x:int->int.\y:int.xy = \:int->int\:int((2)1):int
 * VARone (int->>int::nil,int->>int)        VARone (int::int->>int::nil,int)
 * VARshi (int::int->>int::nil,int->>int)   EXPvar (int::int->>int::nil,int) =1
 * EXPvar (int::int->>int::nil,int->>int) =2
 * -------------------------------------------------------------------------
 * EXPapp (int::int->>int::nil,int) = (2) 1
 * EXPlam (int->>int::nil,int->>int) = \(2) 1
 * EXPlam (nil,(int->>int)->>int->>int) = \\(2) 1
 * we get: EXPlam (EXPlam (EXPapp (EXPvar (VARshi VARone), EXPvar VARone)))
 *
 * some context things.
 * 0, x:int |-_0 x:int (type-one) --> VARone (int::nil, int)
 * ---------------------------------------------------------
 * 0, x:int, y:int |-_0 x:int (type-shift) --> VARshift (int::int::nil, int)
 *
 * 0, x:int, y:int |-_0 y:int (type-one) --> VARone (int::int::nil,int)
 * --------------------------------------------------------------------
 * 0, x:int, y:int, z:int |-_0 y: int (type-shift) -->
 *        VARshift (int::int::int::nil, int)
 *
 * 0,x:int->int,y:int |-_0 y:int (type-one) --> VARone (int::int->>int::nil,int)
 * -----------------------------------------------------------------------------
 * 0,x:int->int,y:int,z:int->int |-_0 y:int (type-shift) -->
 *        VARshift (int->>int::int::int->int::nil, int)
 *)

// test
// \x:int.\y:int->int.y(x)
// val appl = EXPlam (EXPlam (EXPapp (EXPvar (VARone), EXPvar (VARshi (VARone)))))

fn var_one {G:env} {t:ty} ():<> var_t (t :: G, t, 0) = (VARone () | 0)

fn var_shi {G:env} {t1,t2:ty} {n:nat}
  (v: var_t (G, t1, n)):<> var_t (t2 :: G, t1, n+1) = let
  val+ (pf | v) = v
in (VARshi pf | v+1) end

// FIXME: the signature is not strong enough, we should
// also show that G = t :: G' for some G'
fn var_is_one {G:env} {t:ty} {n:nat}
  (v: var_t (G, t, n)):<> bool (n == 0) = let
  val+ (pf | v) = v
in v = 0 end

// FIXME: the signature is not strong enough, we should
// also show that G = t' :: G' for some G' and t'
fn var_is_shi {G:env} {t:ty} {n:nat}
  (v: var_t (G, t, n)):<> bool (n > 0) = let
  val+ (pf | v) = v
in v > 0 end

fn var_unshi {G:env} {t1,t2:ty} {n:pos}
  (v: var_t (t2 :: G, t1, n)):<> var_t (G, t1, n-1) = let
  val+ (pf | v) = v
  prval VARshi pf = pf
in (pf | v-1) end

(* ****** ****** *)
(* substitution *)

// FIXME: study substitutions with deBruijn indices,
// then study lambda-sigma calculus (calculus of explicit substitutions),
// then figure out how to apply this here

// a substitution is a mapping from variables to terms
typedef SUB (G1:env, G2:env) = {t:ty} var0_t (G1, t) -> EXP (G2, t)

// substitutions standard in the study of explicit substitutions
// (lambda-sigma calculus)
val id = (lam x => EXPvar x): {G:env} SUB (G, G)
val shift = (lam x => EXPvar (var_shi x)): {G:env} {t:ty} SUB (G, t :: G)

// derived from untyped version
// prefix a term to a substitution
fun pre {G1,G2:env} {t:ty}
  (e: EXP (G2, t), s: SUB (G1, G2))
  : SUB (t :: G1, G2) = lam x => let
  val (pf | x) = x
in if x = 0
  then let prval VARone () = pf in e end
  else let prval VARshi pf' = pf in s @(pf' | x-1) end
end

// from the paper
fun subst1 {G1,G2:env} {t:ty}
  (sub: SUB (G1, G2)) (e: EXP (G1, t)): EXP (G2, t) = case+ e of
//  | EXPint x => EXPint x
  | EXPvar x => sub x
  | EXPlam e => EXPlam (subst1 (subLam sub) e)
  | EXPapp (e1, e2) => EXPapp (subst1 sub e1, subst1 sub e2)

and subLam {G1,G2:env} {t:ty}
  (sub: SUB (G1, G2)): SUB (t :: G1, t :: G2) = lam v => let
  val (pf | v) = v
in
  if v = 0 then let
    prval VARone () = pf
  in EXPvar (var_one ()) end
  else let
    prval VARshi pf' = pf
  in subst1 (shift {..} {..}) (sub @(pf' | v-1)) end
end

// derived from untyped version (which is derived from mathematical
// formulae directly)

// compose two substitutions
fun comp {G1,G2,G3:env}
  (s1: SUB (G1, G2), s2: SUB (G2, G3))
  : SUB (G1, G3) = lam x => subst (s1 x, s2)

// apply substitution [s] to a term [e]
and subst {G1,G2:env} {t:ty}
  (e: EXP (G1, t), s: SUB (G1, G2)): EXP (G2, t)
  = case+ e of
//  | EXPint x => EXPint x
  | EXPvar n => s n
  | EXPapp (e1, e2) => EXPapp (subst (e1, s), subst (e2, s))
  | EXPlam e1 => EXPlam (subst (e1, pre (EXPvar (var_one ()), comp (s, shift {..} {..}))))

(* ****** ****** *)
(* normalization by substitution (very naive) *)

// normal form
// FIXME: gives two strange errors, but a "typechecking successful" message
fun nf {G:env} {t:ty} (e: EXP (G, t)): EXP (G, t) = case+ e of
  | EXPvar _ => e
  | EXPlam e => EXPlam (nf e)
  | EXPapp (e1, e2) => (case+ (nf e1) of
    | EXPlam e => nf (subst (e, pre (e2, id)))
    | e1 => EXPapp (e1, nf e2))

// TODO: is it possible to prove that [eval] is the
// same as [whnf]?
// FIXME: gives two strange errors as well
fun whnf {G:env} {t:ty} (e: EXP (G, t)): EXP (G, t) = case+ e of
  | EXPvar _ => e
  | EXPlam _ => e
  | EXPapp (e1, e2) => (case+ (whnf e1) of
    | EXPlam e => whnf (subst (e, pre (e2, id)))
    | e1 => EXPapp (e1, whnf e2))

(* ****** ****** *)
(* normalization by evaluation (more efficient) *)

// FIXME: how to prove the following theorem?
// i suppose we would have to specify the behaviour of both
// with dataprops, and then provide a proof function
// for all expressions, eval e = whnf e

datatype VAL (ty) = {G:env} {t1,t2:ty}
  VALclo (t1 ->> t2) of (ENV G, EXP (t1 :: G, t2))

and ENV (env) =
  | ENVnil (nil)
  | {G:env} {t:ty} ENVcons (t :: G) of (VAL t, ENV G)

extern fun eval {G:env} {t:ty} (env: ENV G, e: EXP (G, t)): VAL t
extern fun evalZ {t:ty} (e: EXP (nil, t)): VAL t

local

fun evalVar {G:env} {t:ty}
  (env: ENV G, x: var0_t (G, t)): VAL t = if var_is_one x then let
  val (VARone () | _) = x
  val ENVcons (v, _) = env
in v end
else let
  val (VARshi pf | _) = x
  val ENVcons (_, env) = env
in evalVar (env, var_unshi x) end

in // of [local]

implement eval (env, e) =
  case+ e of
  | EXPvar x => evalVar (env, x)
  | EXPlam e => VALclo (env, e)
  | EXPapp (e1, e2) => let
      val VALclo (env', body) = eval (env, e1)
      val v = eval (env, e2)
    in eval (ENVcons (v, env'), body) end

implement evalZ (e) = eval (ENVnil, e)

end // of [local]

(* ****** ****** *)
(* abstract syntax *)

datatype TY0 =
  | TY0int
  | TY0fun of (TY0, TY0)

(*
typedef location_t = '{loc_line=Nat, loc_column=Nat}

// terms annotated with locations in source code
// FIXME: we can as well save "chunks" for each exp,
// so we don't have to pretty-print
datatype EXP0node =
  | EXP0ann of (TYP0, exp0) // type annotation
  | EXP0var of string
  | EXP0lam of (string, exp0)
  | EXP0app of (exp0, exp0)
where EXP0 = '{
  EXP0_loc= location_t, EXP0_node= EXP0node
}
*)

// this is what we get from our parser:
// a lambda-term in traditional notation
datatype EXP0 =
//  | EXP0ann of (EXP0, TY0) // type annotation
  | EXP0var of string
  | EXP0lam of (string, TY0, EXP0)
  | EXP0app of (EXP0, EXP0)

// type language reified as a datatype
datatype TY (ty) =
  | TYint (int)
  | {t1,t2:ty} TYfun (t1 ->> t2) of (TY t1, TY t2)

(* ****** ****** *)
(* type checking *)

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

(*
 * state: level
 * when we encounter a binder, we increment level by 1 and then record
 * at which level the bound identifier is (in our environment)
 * we then proceed recursively with new level.
 * when we encounter a variable, we just look it up in our data
 * structure, and the resulting index is the difference between
 * the level and what we have looked up!
 *
 * env ::= nil | (id, level, env)
 * (lm) s, t ::= id | \x.s | s t where id = x, x0, x1, ...
 * (db) s, t ::= n | \s | s t where n = 1,2,...
 * lookup: id * env -> level
 * f: env * lm * level -> db
 * f e id n = n - lookup id e
 * f e (\x.s) n = f (x, n, e) s n' where n' = n+1
 * f e (s t) n = (f e s n) (f e t n)
 *
 * f nil (\x.x) 1 = \ (f (x, 1, nil) x 2) = \ (2 - 1) = \1
 * f nil (\x.\y.xy) 1 = \ (f (x, 1, nil) (\y.xy) 2) =
 *   \\(f (y, 2, (x, 1, nil)) (xy) 3)) =
 *   \\(f (y, 2, (x, 1, nil)) x 3) (f (y, 2, (x, 1, nil)) y 3) =
 *   \\(3-1) (3-2) = \\21
 *
 * there's another version of this algorithm, but it requires
 * a lot of munging...
 * shift: env -> env
 * shift nil = nil
 * shift (x, level, env) = (x, level+1, shift env)
 *
 * f2: env * lm -> db
 * f2 e id = lookup id e
 * f2 e (\x.s) = \ (f2 (x, 1, shift e) s)
 * f2 e (s t) = (f2 e s) (f2 e t)
 *
 * f2 nil (\x.x) = \ (f2 (x, 1, nil) x) = \ (lookup x (x, 1, nil)) = \1
 * f2 nil (\x.\y.xy) = \ (f2 (x, 1, nil) (\y.xy)) =
 *   \ (\ (f2 (y, 1, (x, 2, nil)) (xy))) =
 *   \\ (f2 (y,1,(x,2,nil)) x) (f2 (y,1,(x,2,nil)) y)
 *   \\ (lookup x (y,1,(x,2,nil))) (lookup y (y,1,(x,2,nil))) =
 *   \\ 2 1
 *
 * and yet another version! first redefine the environment
 * env ::= nil | (id, env)
 *
 * this function starts at 1, and increments the level upon descending
 * into the environment.
 * lookup: id * env * level -> db
 * lookup x nil lvl = error "internal"
 * lookup x cons(y,env) lvl = if x = y then lvl else lookup x env (lvl+1)
 *
 * f3: env * lm -> db
 * f3 e id = lookup id e 1
 * f3 e (\x.s) = \ (f3 (x, e) s)
 * f3 e (s t) = (f3 e s) (f3 e t)
 *
 * f3 nil (\x.x) = \ (f3 (x,nil) x) = \ (lookup x (x, nil) 1) = \1
 * f3 nil (\x.\y.xy) = \ (f3 (x, nil) (\y.xy)) = \ \ (f3 (y, (x, nil)) (xy)) =
 *   \\ (f3 (y, (x, nil)) x) (f3 (y, (x, nil)) y) =
 *   \\ (lookup x (y, (x, nil)) 1) (lookup y (y, (x, nil)) 1) =
 *   \\ (lookup (x, nil) 2) 1 = \\ 2 1
 *
 * it seems as if three versions are identical. but are they?
 *
 * FIXME: does [f] work for open terms? we don't want open terms!
 * FIXME: how to translate the subtraction to our case?
 * FIXME: how does this interoperate with environments?
 *)

(* typing context *)

abstype ctx_t (env)

extern fun ctx_empty ():<> ctx_t (nil)
extern fun ctx_extend {G:env} {t:ty}
  (id: string, t: TY t, env: ctx_t G):<> ctx_t (t :: G)
extern fun ctx_lookup {G:env}
  (id: string, env: ctx_t G)
  :<> Option_vt ([t:ty] @(TY t, var0_t (G, t)))

local

datatype CTX (env, int) =
  | CTXnil (nil, 0)
  | {t:ty} {G:env} {n:nat} CTXcons (t :: G, n+1)
    of (string, TY t, CTX (G, n))
assume ctx_t (G:env) = [n:nat] CTX (G, n)

in // of [local]

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

end // of [local]

(* the type-checking function *)

// extern fun tywf (x: TY0): Option ([t:ty] TY t)
extern fun tywf (x: TY0): Option_vt ([t:ty] TY t)
extern fun tycheck {G:env} (e: EXP0, env: ctx_t G)
  : Option_vt ([t:ty] @(TY t, EXP (G, t)))
extern fun tycheckZ (e: EXP0)
  : Option_vt ([t:ty] @(TY t, EXP (nil, t)))

local

// TODO: we need two functions actually:
// - typecheck (exp, type, env): check that
//   [exp] can be assigned [type] in [env]
// - typeForExp (exp, env)

// to cut down some repetition
viewdef res_vt (G:env) = Option_vt ([t:ty] @(TY t, EXP (G, t)))

fun tywf_imp (x: TY0): Option_vt ([t:ty] TY t) =
  case+ x of
  | TY0int () => Some_vt (TYint ())
  | TY0fun (a, b) => let
      val ta = tywf_imp a
    in case+ ta of
      | ~Some_vt a => let
        val tb = tywf_imp b
      in case+ tb of
        | ~Some_vt b => Some_vt (TYfun (a, b))
        | None_vt () => (fold@ tb; tb)
      end
      | None_vt () => (fold@ ta; ta)
    end

fun tycheck_imp {G:env} (exp: EXP0, env: ctx_t G): res_vt G
  = case+ exp of
// if [t] is well-formed, then check that it is equal
// to the inferred type
// two functions:
// auxExp (ctx, exp0): exp
// auxExpCK (ctx, exp0, ty): exp <-- checks the type of
// expression that auxExp yields against ty
//  | EXP0ann (e, t) =>
  | EXP0var id => check_var (id, env)
  | EXP0lam (id, t, b) => check_lam (id, t, b, env)
  | EXP0app (e1, e2) => check_app (e1, e2, env)

and check_var {G:env} (id: string, env: ctx_t G): res_vt G = let
  val v = ctx_lookup (id, env)
in case+ v of
  | ~Some_vt @(t, v) => Some_vt @(t, EXPvar v)
  | None_vt () => (fold@ v; v) // unbound variable
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
    | ~Some_vt @(t', b) => Some_vt @(TYfun (t, t'), EXPlam b)
    | None_vt () => (fold@ tp; tp)
  end
  // type is not well-formed
  | None_vt () => (fold@ wf; wf)
end

and check_app {G:env} (e1: EXP0, e2: EXP0, env: ctx_t G): res_vt G = let
  val tp1 = tycheck (e1, env)
in case+ tp1 of
  // make sure that the types match
  | ~Some_vt @(TYfun (t1, tb), e1) => let
      val tp2 = tycheck (e2, env)
    in case+ tp2 of
    | ~Some_vt @(t2, e2) => let
        val (pf | v) = eq_ty_ty (t1, t2)
      in
        if v then let
          prval TYEQsome () = pf
        in Some_vt @(tb, EXPapp (e1, e2)) end
        else let
          prval TYEQnone () = pf
        in None_vt () end
      end
      | None_vt () => (fold@ tp2; tp2) // type error in e2
    end
  | _ => tp1 // type error in e1
end

in // of [local]

// is the type well-formed?
// this is actually a total function at the moment
implement tywf (x) = tywf_imp x

// what we need here is essentially to build a typing derivation
// for [exp] in [env]
// fun tycheck {G:env}
//  (exp: EXP0, env: ctx_t G): res_vt G
implement tycheck (exp, env) = tycheck_imp (exp, env)

implement tycheckZ (exp) = tycheck_imp (exp, ctx_empty ())

end // end of [local]

// TODO: parsing

// TODO: tests
implement main (argc, argv) = print "hello, world"