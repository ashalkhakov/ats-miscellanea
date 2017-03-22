(* various things related to untyped lambda calculus,
 * mainly intended for experiments
 *)

(* syntax: M,N ::= x | \x.M | MN
 * FV : lambda-expression -> set of variables
 * FV(x) = {x}
 * FV(\x.M) = FV(M) - {x}
 * FV(MN) = union(FV(M), FV(N))
 *
 * substitution, written M[x := N] (replacing
 * all free occurences of the variable x by
 * the expression N in M):
 * x[x:=N] == N
 * y[x:=N] == y, if x /= y
 * (M1 M2)[x:=N] == (M1[x:=N]) (M2[x:=N])
 * (\y.M)[x:=N] == \y.(M[x:=N]), if x /= y and y not in FV(N)
 *
 * now that we have substitution, beta-reduction can be stated thus:
 * (\x.M) N --> M[x:=N]
 *
 * ---------------------------------------------------------------
 * let's try to derive the rules for capture-avoiding substitution
 * in a lambda-calculus in the de Bruijn notation.
 * the syntax is as follows:
 * M, N ::= n | \M | MN where n ::= 0 | n+1
 * where [n] (a de Bruijn index) represents an occurrence of a variable
 * in a \-term, and denotes the number of binders that are in scope
 * between that occurrence and its corresponding binder.
 * for example, \\1 means \xy.y whereas \\2 means \xy.x
 * \\\\3 means \xyzw.y etc.
 *
 * \0
 * \\10
 * \\\312 = \xyz.xzy
 * \\12 = \xy.yx
 *
 * \s.\z.s (s z) = \\1(1 0)
 * \x.\y.y (\z.x z) = \\0 (\2 0)
 *
 * how do we turn one into the other?
 * exp ::= var | (exp_1) exp_2 | \var.exp (where var = x,y,z,...)
 * exp' ::= nat | (exp'_1) exp'_2 | \exp' (where nat = 0,1,2,...)
 * ctx ::= nil | cons(var=nat, ctx)
 *
 * on closed terms, the only way to introduce a variable is via lambda.
 * when introducing new variable, all others currently in the context
 * must be shifted (incremented) appropriately, to avoid capture.
 * even if the context contains free variables, they must be shifted
 * as well!
 *
 * so the general pattern is this:
 * when moving a variable under a binder (by wrapping it inside a lambda),
 * increment it; when moving a variable over a binder (by removing an
 * outer lambda), decrement it.
 *
 * f : term * context -> debruijn
 * f(x, c) = lookupCtx (x, c)
 * f(\x.b, c) = \. f (b, shiftAddCtx (x, c))
 * f((m)n, c) = (f (m, c)) (f (n, c))
 *
 * lookupCtx : var * context -> debruijn
 * lookupCtx x nil = error "variable not in context!"
 * lookupCtx x cons(y=m, ctx) = m, if x=y
 *                              lookupCtx (x, ctx), otherwise
 *
 * shiftCtx : context -> context
 * shiftCtx nil = nil
 * shiftCtx cons(x=n, c) = cons(x=n+1, shiftCtx c)
 *
 * shiftAddCtx : var * context -> context
 * shiftAddCtx (x, c) = cons(x=0, shiftCtx c)
 *
 * f(\x.x, nil) = \.f (x, shiftAddCtx x nil)
 *              = \.lookupCtx (cons(x=0,nil))
 *              = \.0
 * f(\x.\y.xy, nil) = \.f (\.y.xy, shiftAddCtx x nil)
 *                  = \.f (\.y.xy, cons(x=0,nil))
 *                  = \.\.f (xy, shiftAddCtx y (cons(x=0,nil)))
 *                  = \.\.f (xy, cons(y=0,cons(x=1,nil)))
 *                  = \.\.(f (x, cons(y=0,cons(x=1,nil)))) (f (y, cons(....)))
 *                  = \.\.1 0
 * f(\x.yx, cons(y=0,nil)) = \.f (yx, shiftAddCtx x cons(y=0,nil))
 *                         = \.f (yx, cons(x=0,cons(y=1,nil)))
 *                         = \.(f y (cons(x=0,cons(y=1,nil)))) (f x (....))
 *                         = \.1 0
 *
 * substitution. we need to define it, but first, lets deal with free/bound
 * variables.
 * in \1, 1 is bound, but in \12 2 is not
 * how to determine if the variable is bound in a given term?
 *
 * FV(n) = {n}
 * FV((M)N) = union(FV(M),FV(N))
 * FV(\M) = FV(M) - {1}
 *
 * so FV(\\1) = {}, FV(\\12) = {2}, FV(1) = {1}, FV((\\12)1) = {1,2}
 *
 * we shall note that it is important to distinguish bound and free
 * *occurrences* of a variable, since it is legitimate to use the same
 * name (number) to denote different things. also, from this distinction
 * useful invariants follow.
 *
 * "term in context": a representation that associates to each term [t]
 * a context that contains information about free variables in [t].
 * so we can say that (\21 is a term with a context 2=\1
 * context is simply a function: nat -> term
 *
 * formally, a substitution is a list of term replacements for the free
 * variables, written M1.M2...., where Mi is the replacement for the ith
 * free variable.
 *
 * the application of substitution s to a term M is written M[s],
 * the composition of two substitutions s1 and s2 is written s1 s2 and
 * defined by
 *   M[s1 s2] = (M[s1])[s2]
 * and the rules for application are:
 * n[N1...Nn...] = Nn (a variable "indexes into" the list of substitutions)
 * (M1 M2)[s] = (M1[s])(M2[s]) (propagate down)
 * the rule for application is:
 * (\M)[s] = \(M[1.1[s'].2[s'].3[s']...]) where s' = shift(s)
 * as you can see, we cons 1 onto the list, and then substitute 
 *
 * with substitution defined, the beta-reduction rule becomes:
 *
 * (\M)N --> M[N.1.2.3...]
 *
 * neat, eh? TODO: implement substitution on a computer
 *)

// substitution is a function which maps indexes n to expressions N.
// we use "shift" for substitution that maps each index n to n + 1.
// given a substitution sigma and an expression N, we write N[sigma] for
// the result of applying the substitution sigma to N.

// TODO: write a parser

// TODO: it is perfectly reasonable to implement VAR as an ADT,
// then select a representation that employs machine integers
datatype VAR = VARone | VARshi of VAR
datatype EXP = EXPvar of VAR | EXPapp of (EXP, EXP) | EXPlam of EXP

typedef SUB = VAR -<cloref1> EXP

fn id (x: VAR):<cloref1> EXP = EXPvar x
fn shift (x: VAR):<cloref1> EXP = EXPvar (VARshi x)

// prefix a term to a substitution
fun pre (e: EXP, s: SUB): SUB = lam x => case+ x of
  | VARone () => e
  | VARshi x => s x

// compose two substitutions
fun comp (s1: SUB, s2: SUB):<cloref1> SUB = lam x => subst (s1 x, s2)

// apply substitution [s] to a term [e]
and subst (e: EXP, s: SUB):<cloref1> EXP = case+ e of
  | EXPvar n => s n
  | EXPapp (e1, e2) => EXPapp (subst (e1, s), subst (e2, s))
  | EXPlam e1 => EXPlam (subst (e1, pre (EXPvar VARone, comp (s, shift))))

(* ****** ****** *)

fun nf (e: EXP): EXP = case+ e of
  | EXPvar _ => e
  | EXPlam e => EXPlam (nf e)
  | EXPapp (e1, e2) => (case+ (nf e1) of
      | EXPlam e => nf (subst (e, pre (e2, id)))
      | e1 => EXPapp (e1, nf e2))

(* ****** ****** *)

fun print_var (v: VAR): void = let
  fun int_of_var (v: VAR, c: int): int = case+ v of
    | VARone () => c
    | VARshi v => int_of_var (v, c+1)
in printf ("%d", @(int_of_var (v, 1))) end
overload print with print_var

fun print_exp (e: EXP): void = case+ e of
  | EXPvar n => print_var n
  | EXPapp (e1, e2) => begin
      print "(";
      print "("; print_exp e1; print ") ";
      print_exp e2;
      print ")"
    end
  | EXPlam e1 => begin
      print "("; print "\\"; print_exp e1; print ")"
    end
overload print with print_exp

(* ****** ****** *)

implement main (argc, argv) = let
  // variables for easier reference
  val one = EXPvar VARone
  val two = EXPvar (VARshi VARone)
  val three = EXPvar (VARshi (VARshi VARone))
  val four = EXPvar (VARshi (VARshi (VARshi VARone)))
  val five = EXPvar (VARshi (VARshi (VARshi (VARshi VARone))))
  // closed terms
  val test00 = EXPlam one // \1
  // \\12
  val test01 = EXPlam (EXPlam (EXPapp (one, two)))
  // open terms
  val test10 = three // 3
  val test11 = EXPlam (EXPapp (one, two)) // \12
  // (\\4 2 (\1 3)) (\5 1)
  val test12 = EXPapp (x, y) where {
    val x = EXPlam (EXPlam (EXPapp (EXPapp (four, two),
            EXPlam (EXPapp (one, three)))))
    val y = EXPlam (EXPapp (five, one))
  }
  // (\1)2
  val test13 = EXPapp (EXPlam one, two)
  // output function
  fun outp (e: EXP): void = begin
    print "--------\n";
    print "before: "; print e; print_newline ();
    print "after: "; print_exp (nf e); print_newline ()
  end
in
  outp test00; outp test01; outp test10;
  outp test11; outp test11; outp test12;
  outp test13
end
