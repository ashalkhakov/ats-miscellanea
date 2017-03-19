// compile with:
// atscc -D_GC_GCATS interp.dats
staload _ = "prelude/DATS/option.dats"

datasort tp = tpbool | tpnat // base types
  | tpfun of (tp, tp)
  | tpcon of (tp, tp) // conjunction
  | tpdis of (tp, tp) // disjunction
//  | forall of (tp -> tp)
datasort tps = tpsnil | tpsmore of (tps, tp)

dataprop TPI (int, tp, tps) =
  | {T:tp} {G:tps} TPIone (0, T, tpsmore (G, T))
  | {T1,T2:tp} {G:tps} {n:nat}
    TPIshi (n+1, T1, tpsmore (G, T2)) of TPI (n, T1, G)

(* ****** ****** *)
// internal representation

datatype EXP (G:tps, tp, int) =
  // core
  | {i:nat} {T:tp} EXPvar (G, T, 0) of (TPI (i, T, G) | int i)
  | {T1,T2:tp} {n1,n2:nat}
      EXPapp (G, T2, n1+n2+1) of
        (EXP (G, tpfun (T1, T2), n1), EXP (G, T1, n2))
  | {T1,T2:tp} {n:nat}
      EXPlam (G, tpfun (T1, T2), n+1) of
        EXP (tpsmore (G, T1), T2, n)
  // extensions
  // general recursion
  | {T:tp} {n:nat}
      EXPfix (G, T, n+1) of EXP (tpsmore (G, T), T, n)
  // booleans
  | EXPtrue (G, tpbool, 0)
  | EXPfalse (G, tpbool, 0)
  | {n1,n2,n3:nat} {T:tp}
      EXPif (G, T, n1+n2+n3+1) of
        (EXP (G, tpbool, n1), EXP (G, T, n2), EXP (G, T, n3))
  // naturals
  | EXPzero (G, tpnat, 0)
  | {n:nat} EXPsucc (G, tpnat, n+1) of EXP (G, tpnat, n)
  | {T:tp} {n1,n2,n3:nat}
      EXPcase (G, T, n1+n2+n3+1) of
        (EXP (G, tpnat, n1), EXP (G, T, n2),
         EXP (tpsmore (G, tpnat), T, n3))
  // conjunction
  | {T1,T2:tp} {n1,n2:nat}
      EXPcon (G, tpcon (T1, T2), n1+n2+1) of
        (EXP (G, T1, n1), EXP (G, T2, n2))
  | {T1,T2:tp} {n:nat}
      EXPfst (G, T1, n+1) of EXP (G, tpcon (T1, T2), n)
  | {T1,T2:tp} {n:nat}
      EXPsnd (G, T2, n+1) of EXP (G, tpcon (T1, T2), n)
  // disjunction
  | {T1,T2:tp} {n:nat}
      EXPinl (G, tpdis (T1, T2), n+1) of EXP (G, T1, n)
  | {T1,T2:tp} {n:nat}
      EXPinr (G, tpdis (T1, T2), n+1) of EXP (G, T2, n)
  | {T1,T2,T3:tp} {n1,n2,n3:nat}
      EXPdis (G, T3, n1+n2+n3+1) of
        (EXP (G, tpdis (T1, T2), n1), EXP (tpsmore (G, T1), T3, n2),
         EXP (tpsmore (G, T2), T3, n3))
  // quantification
(*
  | {G:tps} {f:tp->tp} {n:nat} EXPtlam (G, forall f, n+1) of
      ({t:tp} EXP (G, f t, n))
  | {G:tps} {f:tp->tp} {t:tp} {n:nat} EXPtapp (G, f t, n+1) of
      EXP (G, forall f, n)
*)

typedef EXP0 (G:tps, T:tp) = [n:nat] EXP (G, T, n)

(* ****** ****** *)
// type checking

// singleton type for tp
datatype TP (tp) =
  | TPbool (tpbool)
  | TPnat (tpnat)
  | {T1,T2:tp} TPcon (tpcon (T1, T2)) of (TP T1, TP T2)
  | {T1,T2:tp} TPdis (tpdis (T1, T2)) of (TP T1, TP T2)
  | {T1,T2:tp} TPfun (tpfun (T1, T2)) of (TP T1, TP T2)

// equality on types
dataprop TPEQ (tp, tp, bool) =
  | {T1,T2:tp} TPEQnone (T1, T2, false)
  | {T:tp} TPEQsome (T, T, true)

fun eq_tp_tp {T1,T2:tp} (a: TP T1, b: TP T2)
  : [b:bool] (TPEQ (T1, T2, b) | bool b) = case+ (a, b) of
  | (TPbool (), TPbool ()) => (TPEQsome () | true)
  | (TPnat (), TPnat ()) => (TPEQsome () | true)
  | (TPfun (a1, a2), TPfun (b1, b2)) => begin
      case+ (eq_tp_tp (a1, b1), eq_tp_tp (a2, b2)) of
      | ((TPEQsome () | true), (TPEQsome () | true)) => (TPEQsome () | true)
      | (_, _) => (TPEQnone () | false)
      end
  | (TPcon (a1, a2), TPcon (b1, b2)) => begin
      case+ (eq_tp_tp (a1, b1), eq_tp_tp (a2, b2)) of
      | ((TPEQsome () | true), (TPEQsome () | true)) => (TPEQsome () | true)
      | (_, _) => (TPEQnone () | false)
      end
  | (TPdis (a1, a2), TPdis (b1, b2)) => begin
      case+ (eq_tp_tp (a1, b1), eq_tp_tp (a2, b2)) of
      | ((TPEQsome () | true), (TPEQsome () | true)) => (TPEQsome () | true)
      | (_, _) => (TPEQnone () | false)
      end
  | (_, _) => (TPEQnone () | false)

datatype CTX (tps) =
  | CTXnil (tpsnil)
  | {T:tp} {G:tps} CTXcons (tpsmore (G, T)) of (string, TP T, CTX G)

fun ctx_lookup {G:tps} (id: string, c: CTX G)
  : Option ([T:tp] [i:nat] @(TPI (i, T, G) | int i, TP T))
  = case+ c of
  | CTXnil () => None ()
  | CTXcons (x, t, c) => if id = x then Some @(TPIone () | 0, t)
    else case+ ctx_lookup (id, c) of
      | Some @(pf | v, t) => Some @(TPIshi pf | v+1, t)
      | None () => None ()

// this is what we get from our parser
datatype EXP0 =
  | EXP0var of string
  | {T:tp} EXP0lam of (string, TP T, EXP0)
  | EXP0app of (EXP0, EXP0)
  | {T:tp} EXP0fix of (string, TP T, EXP0)
  | EXP0false | EXP0true
  | EXP0if of (EXP0, EXP0, EXP0)
  | EXP0zero | EXP0succ of EXP0
  | EXP0case of (EXP0, EXP0, string, EXP0)
  | EXP0con of (EXP0, EXP0)
  | EXP0fst of EXP0 | EXP0snd of EXP0
  | EXP0inl of EXP0 | EXP0inr of EXP0
  | {T:tp} EXP0inl of (TP T, EXP0)
  | {T:tp} EXP0inr of (TP T, EXP0)
  | EXP0dis of (EXP0, string, EXP0, string, EXP0)

fun typecheck {G:tps} (e: EXP0, c: CTX G)
  : Option ([T:tp] @(TP T, EXP0 (G, T))) = case+ e of
  | EXP0var x => (case+ ctx_lookup (x, c) of
    | Some @(pf | v, t) => Some @(t, EXPvar (pf | v))
    | None () => None ())
  | EXP0lam (x, t, b) => (case+ typecheck (b, CTXcons (x, t, c)) of
    | Some @(t', b) => Some @(TPfun (t, t'), EXPlam b)
    | None () => None ())
  | EXP0app (e1, e2) =>
    begin case+ typecheck (e1, c) of
    | Some @(TPfun (t1, t2), e1) =>
      begin case+ typecheck (e2, c) of
        | Some @(t1', e2) => let
            val (pf | r) = eq_tp_tp (t1, t1')
          in
            if r then let
              prval TPEQsome () = pf
            in
              Some @(t2, EXPapp (e1, e2))
            end else let
              prval TPEQnone () = pf
            in None () end
          end
        | None () => None ()
      end
    | _ => None ()
    end
  | EXP0fix (x, t, b) => (case+ typecheck (b, CTXcons (x, t, c)) of
    | Some @(t', b) => let
        val (pf | r) = eq_tp_tp (t, t')
      in
        if r then let
          prval TPEQsome () = pf
        in Some @(t, EXPfix b) end else let
          prval TPEQnone () = pf
        in None () end
      end
    | _ => None ())
  | EXP0false () => Some @(TPbool (), EXPfalse ())
  | EXP0true () => Some @(TPbool (), EXPtrue ())
  | EXP0if (a,e1,e2) => (case+ typecheck (a, c) of
    | Some @(t, a) => let
        val (pf | r) = eq_tp_tp (t, TPbool ())
      in
        if r then let
          prval TPEQsome () = pf
        in
          case+ (typecheck (e1, c), typecheck (e2, c)) of
          | (Some @(t1, e1), Some @(t2, e2)) => let
              val (pf | r) = eq_tp_tp (t1, t2)
            in
              if r then let
                prval TPEQsome () = pf
              in
                Some @(t1, EXPif (a, e1, e2))
              end else let
                prval TPEQnone () = pf
              in None () end
            end
          | (_, _) => None ()
        end else let
          prval TPEQnone () = pf
        in None () end
      end
    | None () => None ())
  | EXP0zero () => Some @(TPnat (), EXPzero ())
  | EXP0succ e => (case+ typecheck (e, c) of
    | Some @(t, e) => let
        val (pf | r) = eq_tp_tp (t, TPnat ())
      in
        if r then let
          prval TPEQsome () = pf
        in Some @(t, EXPsucc e) end else let
          prval TPEQnone () = pf
        in None () end
      end
    | None () => None ())
  // case x of z => foo | s(x) => baz
  | EXP0case (a, e1, x2, e2) => (case+ typecheck (a, c) of
    | Some @(t, a) => let
        val (pf | r) = eq_tp_tp (t, TPnat ())
      in
        if r then let
          prval TPEQsome () = pf
        in
          case+ typecheck (e1, c) of
          | Some @(t1, e1) => begin
            case+ typecheck (e2, CTXcons (x2, TPnat (), c)) of
            | Some @(t2, e2) => let
                val (pf | r) = eq_tp_tp (t1, t2)
              in
                if r then let
                  prval TPEQsome () = pf
                in
                  Some @(t1, EXPcase (a, e1, e2))
                end else let
                  prval TPEQnone () = pf
                in
                  None ()
                end
              end
            | None () => None ()
            end
          | None () => None ()
        end else let
          prval TPEQnone () = pf
        in None () end
      end
    | None () => None ())
  | EXP0con (e1, e2) => (case+ (typecheck (e1, c), typecheck (e2, c)) of
    | (Some @(t1, e1), Some @(t2, e2)) =>
        Some @(TPcon (t1, t2), EXPcon (e1, e2))
    | (_, _) => None ())
  | EXP0fst e => (case+ typecheck (e, c) of
    | Some @(TPcon (t1, t2), e) => Some @(t1, EXPfst e)
    | _ => None ())
  | EXP0snd e => (case+ typecheck (e, c) of
    | Some @(TPcon (t1, t2), e) => Some @(t2, EXPsnd e)
    | _ => None ())
  | EXP0inl (TPdis (t1, t2), e) => (case+ typecheck (e, c) of
    | Some @(t1', e) => let
        val (pf | r) = eq_tp_tp (t1, t1')
      in
        if r then let
          prval TPEQsome () = pf
        in Some @(TPdis (t1, t2), EXPinl e) end else let
          prval TPEQnone () = pf
        in None () end
      end
    | None () => None ())
  | EXP0inr (TPdis (t1, t2), e) => (case+ typecheck (e, c) of
    | Some @(t2', e) => let
        val (pf | r) = eq_tp_tp (t2, t2')
      in
        if r then let
          prval TPEQsome () = pf
        in Some @(TPdis (t1, t2), EXPinr e) end else let
          prval TPEQnone () = pf
        in None () end
      end
    | None () => None ())
  | EXP0dis (e, x1, f1, x2, f2) => (case+ typecheck (e, c) of
    | Some @(TPdis (t1, t2), e) => begin
        case+ (typecheck (f1, CTXcons (x1, t1, c)), typecheck (f2, CTXcons (x2, t2, c))) of
        | (Some @(t1', f1), Some @(t2', f2)) => let
            val (pf | r) = eq_tp_tp (t1', t2')
          in
            if r then let
              prval TPEQsome () = pf
            in Some @(t1', EXPdis (e, f1, f2)) end else let
              prval TPEQnone () = pf
            in None () end
          end
        | (_, _) => None ()
      end
    | _ => None ())
  | _ => None ()
//  | EXP0dis (e, t, f1, f2) => (case+ typecheck (e, c) of
//    | Some @(TPdis (t1, t2), e) => (case+ (typecheck (f1, c)

(* ****** ****** *)
// big-step interpreter

datatype either (a:t@ype, b:t@ype) =
  | inleft (a, b) of a
  | inright (a, b) of b

datatype VAL (tp) =
  | VALtrue (tpbool)
  | VALfalse (tpbool)
  | VALzero (tpnat)
  | VALsucc (tpnat) of VAL (tpnat)
  | {t1,t2:tp} VALcon (tpcon (t1, t2)) of (VAL t1, VAL t2)
  | {t1,t2:tp} VALdis (tpdis (t1, t2)) of either (VAL t1, VAL t2)
  | {D:tps} {T1,T2:tp} {m:nat} VALclo (tpfun (T1, T2)) of
      (EXP (tpsmore (D, T1), T2, m), ENV D)
//  | {D:tps} {f:tp->tp} {m:nat} VALtclo (forall f) of
//      ({t:tp} EXP (D, f t, m), ENV D)

and ENV (tps) =
  | ENVnil (tpsnil)
  | {G:tps} {T:tp}
      ENVcons (tpsmore (G, T)) of (VAL T, ENV G)
  | {G:tps} {T:tp}
      ENVfix (tpsmore (G, T)) of (EXP0 (tpsmore (G, T), T), ENV G)

// typedef VAL0 (T:tp) = [n:nat] VAL (T, n)
// typedef ENV0 (G:tps) = [n:nat] ENV (G, n)

fun lookup {G:tps} {T:tp} {n:nat}
  (pf: TPI (n, T, G) | e: ENV G, n: int n)
  : VAL T =
  if n = 0 then let
    prval TPIone () = pf
  in
    case+ e of
    | ENVcons (x, _) => x
    | ENVfix (x, e) => eval (ENVfix (x, e), x)
  end else let
    prval TPIshi pf = pf
    val e = case+ e of
      | ENVcons (_, e) => e
      | ENVfix (_, e) => e
  in
    lookup (pf | e, n-1)
  end

and eval {G:tps} {T:tp}
  (e: ENV G, a: EXP0 (G, T))
  : VAL T = case+ a of
  // core
  | EXPvar (pf | n) => lookup (pf | e, n)
  | EXPlam b => VALclo (b, e)
  | EXPapp (a1, a2) => apply (e, a1, a2)
  // extensions
  | EXPfix b => eval (ENVfix (b, e), b)
  (* booleans *)
  | EXPtrue () => VALtrue ()
  | EXPfalse () => VALfalse ()
  | EXPif (a, b, c) => (case+ eval (e, a) of
      | VALtrue () => eval (e, b)
      | VALfalse () => eval (e, c))
  (* naturals *)
  | EXPzero () => VALzero ()
  | EXPsucc a => VALsucc (eval (e, a))
  | EXPcase (a, b, c) => (case+ eval (e, a) of
      | VALzero () => eval (e, b)
      | VALsucc v => eval (ENVcons (v, e), c))
  (* conjunction *)
  | EXPcon (a1, a2) => VALcon (eval (e, a1), eval (e, a2))
  | EXPfst a => let
      val VALcon (r, _) = eval (e, a)
    in r end
  | EXPsnd a => let
      val VALcon (_, r) = eval (e, a)
    in r end
  (* disjunction *)
  | EXPinl a => VALdis (inleft (eval (e, a)))
  | EXPinr a => VALdis (inright (eval (e, a)))
  | EXPdis (a, b, c) => let
      val VALdis r = eval (e, a)
    in case+ r of
      | inleft r => eval (ENVcons (r, e), b)
      | inright r => eval (ENVcons (r, e), c)
    end
(*
  | EXPtlam b => VALtclo (b, e)
  | EXPtapp a => let
      val VALtclo (a', e') = eval (e, a)
    in
      eval (e', a' {..})
    end
*)

and apply {G:tps} {T1,T2:tp}
  (e: ENV G, a1: EXP0 (G, tpfun (T1, T2)), a2: EXP0 (G, T1))
  : VAL T2 = let
  val VALclo (a1, e') = eval (e, a1)
  val a2 = eval (e, a2)
in
  eval (ENVcons (a2, e'), a1)
end

(* ****** ****** *)
// some simple programs

fun print_val {T:tp} (v: VAL T): void = case+ v of
  | VALtrue () => print "T"
  | VALfalse () => print "F"
  | VALzero () => print "Z"
  | VALsucc v => (print "S("; print_val v; print ")")
  | VALcon (a, b) =>
      (print "and("; print_val a; print ", "; print_val b; print ")")
  | VALdis (inleft x) => (print "inl("; print_val x; print ")")
  | VALdis (inright x) => (print "inr("; print_val x; print ")")
  | VALclo (a, e) => print "<closure>"

fun print_exp {G:tps} {T:tp} (e: EXP0 (G, T)): void =
  case+ e of
  | EXPvar (pf | i) => (print "var("; print i; print ")")
  | EXPlam e => (print "lam("; print_exp e; print ")")
  | EXPapp (e1, e2) =>
    (print "app("; print_exp e1; print ", "; print_exp e2; print ")")
  | EXPfix e => (print "fix("; print_exp e; print ")")
  | EXPfalse () => print "F"
  | EXPtrue () => print "T"
  | EXPif (a, b, c) =>
    (print "if("; print_exp a; print ","; print_exp b; print ",";
     print_exp c; print ")")
  | EXPzero () => print "Z"
  | EXPsucc e => (print "S("; print_exp e; print ")")
  | EXPcase (a, b, c) =>
    (print "case("; print_exp a; print ", "; print_exp b; print ", ";
     print_exp c; print ")")
  | EXPcon (a, b) =>
    (print "and("; print_exp a; print ", "; print_exp b; print ")")
  | EXPfst x => (print "fst("; print_exp x; print ")")
  | EXPsnd x => (print "snd("; print_exp x; print ")")
  | EXPinl x => (print "inl("; print_exp x; print ")")
  | EXPinr x => (print "inr("; print_exp x; print ")")
  | EXPdis (a, b, c) =>
    (print "or("; print_exp a; print ","; print_exp b; print ","; print_exp c;
     print ")")

// an abbreviation
fun exp2app (e: EXP0, x: EXP0, y: EXP0): EXP0 = EXP0app (EXP0app (e, x), y)

// truth-logical functions

// bool_and(x,y) = if x then false else y
val bool_and = EXP0lam ("x", TPbool (), EXP0lam ("y", TPbool (),
  EXP0if (EXP0var "x", EXP0false (), EXP0var "y")))
// bool_or(x,y) = if x then y else false
val bool_or = EXP0lam ("x", TPbool (), EXP0lam ("y", TPbool (),
  EXP0if (EXP0var "x", EXP0var "y", EXP0false ())))
// bool_not(x) = if x then false else true
val bool_not = EXP0lam ("x", TPbool (),
  EXP0if (EXP0var "x", EXP0false (), EXP0true ()))
// bool_imp(x,y) = or(not(x), y)
val bool_imp = EXP0lam ("x", TPbool (), EXP0lam ("y", TPbool (),
  exp2app (bool_or, EXP0app (bool_not, EXP0var "x"), EXP0var "y")))

// arithmetic
val fun_inc = EXP0lam ("x", TPnat (), EXP0succ (EXP0var "x"))
val inc = EXP0app (fun_inc, EXP0succ (EXP0succ (EXP0zero ())))
// pred(x) = case x of z => z | s(x) => x
val fun_pred = EXP0lam ("x", TPnat (),
  EXP0case (EXP0var "x", EXP0zero (), "x", EXP0var "x"))
// iszero(x) = case x of z => true | s(x) => false
val fun_iszero = EXP0lam ("x", TPnat (),
  EXP0case (EXP0var "x", EXP0true (), "x", EXP0false ()))

// 0+y=y
// x+y=((x-1)+y)+1
// add = \y:nat. fix(f:nat->nat. \x:nat. if(iszero(x),y,succ(f(pred(x)))))
val add = EXP0lam ("y", TPnat (),
  EXP0fix ("f", TPfun (TPnat (), TPnat ()), EXP0lam ("x", TPnat (),
    EXP0if (EXP0app (fun_iszero, EXP0var "x"), EXP0var "y",
      EXP0succ (EXP0app (EXP0var "f", EXP0app (fun_pred, EXP0var "x")))))))

// 0*y=0
// x*y=y+(x-1)*y
// mul = \y:nat. fix(f:nat->nat, \x:nat.
//         case x of Z => Z | S(x) => add(y,f(x,y)))
val mul = EXP0lam ("y", TPnat (),
  EXP0fix ("f", TPfun (TPnat (), TPnat ()), EXP0lam ("x", TPnat (),
    EXP0case (EXP0var "x", EXP0zero (),
      "x'", exp2app (add, EXP0var "y", EXP0app (EXP0var "f", EXP0var "x'"))))))

implement main (argc, argv) = let
  val one = EXP0succ (EXP0zero ())
  val two = EXP0succ one
  fun test (x: EXP0): void = case+ typecheck (x, CTXnil) of
    | Some @(t, x) => begin
        print "input term:\n"; print_exp x; print_newline ();
        print "evaluated term:\n"; print_val (eval (ENVnil, x));
        print_newline ()
      end
    | None () => print "type checking failed\n"
in
  print "----testing\n";
  test inc;
  test (EXP0app (bool_not, EXP0false ()));
  test (EXP0app (EXP0app (bool_imp, EXP0true ()), EXP0false ()));
  test (EXP0app (fun_iszero, EXP0zero ()));
  test (EXP0app (fun_iszero, EXP0succ (EXP0zero ())));
  test (EXP0app (fun_pred, EXP0zero ()));
  test (EXP0app (fun_pred, EXP0succ (EXP0succ (EXP0zero ()))));
  test (exp2app (add, EXP0zero (), EXP0zero ()));
  test (exp2app (add, one, two));
  test (exp2app (mul, EXP0zero (), EXP0zero ()));
  test (exp2app (mul, two, two))
end
