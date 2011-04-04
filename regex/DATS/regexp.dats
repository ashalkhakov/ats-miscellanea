staload "SATS/charset.sats"
staload "SATS/regexp.sats"

staload S = "SATS/linset.sats"
staload _ = "libats/DATS/linmap_avltree.dats"
staload _ = "DATS/linset.dats"
staload _ = "prelude/DATS/list_vt.dats"

#define ATS_STALOADFLAG 0
#define ATS_DYNLOADFLAG 0

(*
** sharing of nodes in AST represented by a linear inductive type?
** - not possible with let-bound variables of linear type
*)

(* ****** ****** *)

// word is a list of characters
// language is a set of words
// regular expression denotes a language, i.e. a set of words

datatype re (int) =
  // L(eps) = {eps}
  | REeps (0)
  // L(phi) = {} -- represented by empty charset
  // L(C) = C
  | RErng (0) of charset
  // L(r+s) = L(r) \union L(s)
  | {n1,n2:nat} REalt (n1+n2+1) of (re n1, re n2)
  // L(r&s) = L(r) \intersect L(s)
  | {n1,n2:nat} REint (n1+n2+1) of (re n1, re n2)
  // L(rs) = {uv | u \in L(r), v \in L(s)}
  | {n1,n2:nat} REcat (n1+n2+1) of (re n1, re n2)
  // L(r*) = {eps} \union L(rr*)
  | {n:nat} REclo (n+1) of re n
  // L(~r) = E* \difference L(r)
  | {n:nat} REneg (n+1) of re n
typedef re0 = [n:nat] re n

(* ****** ****** *)

assume RE = re0

(* ****** ****** *)
(* These are smart constructors for the RE type. *)

implement re_clo (r) = case+ r of
  | REclo _ => r
  | RErng cs when charset_is_empty cs => r
  | REeps () => REeps ()
  | _ =>> REclo r

implement re_neg (r) = case+ r of
  | REneg _ => r
  | RErng cs when charset_is_empty cs => RErng (charset_universe ())
  | _ =>> REneg r

implement re_phi () = RErng (charset_empty ())
implement re_emp () = REeps ()
implement re_lit (c) = RErng (charset_sing c)
implement re_rng (c1, c2) = RErng (charset_range (c1, c2))

implement re_alt (r1, r2) = let
  fun loop {n1,n2:nat} .<n1>. (r1: re n1, r2: re n2):<> re0 =
    case+ (r1, r2) of
    | (RErng cs, _) when charset_is_empty cs => r2
    | (RErng cs, _) when charset_is_universe cs => r1
    | (_, RErng cs) when charset_is_empty cs => r1
    | (_, RErng cs) when charset_is_universe cs => r2
    | (RErng cs1, RErng cs2) => RErng (charset_union (cs1, cs2))
    | (REalt (x1, x2), _) => loop (x1, REalt (x2, r2))
    | (_, _) =>> REalt (r1, r2)
in
  loop (r1, r2)
end

implement re_int (r1, r2) = let
  fun loop {n1,n2:nat} .<n1>. (r1: re n1, r2: re n2):<> re0 =
    case+ (r1, r2) of
    | (RErng cs, _) when charset_is_empty cs => r1
    | (RErng cs, _) when charset_is_universe cs => r2
    | (_, RErng cs) when charset_is_empty cs => r2
    | (_, RErng cs) when charset_is_universe cs => r1
    | (RErng cs1, RErng cs2) => RErng (charset_intersect (cs1, cs2))
    | (REint (x1, x2), _) => loop (x1, REint (x2, r2))
    | (_, _) =>> REint (r1, r2)  
in
  loop (r1, r2)
end

implement re_cat (r1, r2) = let
  fun loop {n1,n2:nat} .<n1>. (r1: re n1, r2: re n2):<> re0 =
    case+ (r1, r2) of
    | (_, RErng cs) when charset_is_empty cs => r2
    | (RErng cs, _) when charset_is_empty cs => r1
    | (_, REeps ()) => r1
    | (REeps (), _) => r2
    | (REcat (x1, x2), _) => loop (x1, REcat (x2, r2))
    | (_, _) =>> REcat (r1, r2)
in
  loop (r1, r2)
end

implement re_opt (r) = re_alt (re_emp (), r)

(* ****** ****** *)

// [re_is_emp r = true] iff the language denoted by [r]
// contains the empty word (eps)
implement re_is_emp (r) = let
  fun is_emp {n:nat} .<n>. (r: re n):<> bool = case+ r of
    | REeps () => true
    | RErng _ => false
    | REalt (r1, r2) => is_emp r1 || is_emp r2
    | REint (r1, r2) => is_emp r1 && is_emp r2
    | REcat (r1, r2) => is_emp r1 && is_emp r2
    | REclo r => true
    | REneg r => ~is_emp r
in
  is_emp r
end

// [re_is_phi r = true] iff the language denoted by [r]
// is empty (contains no words whatsoever)
implement re_is_phi (r) = let
  fun loop {n:nat} .<n>. (r: re n):<> bool =
    case+ r of
    | REeps () => false
    | RErng cs => charset_is_empty cs
    | REalt (r1, r2) => loop r1 && loop r2
    | REint (r1, r2) => loop r1 || loop r2
    | REcat (r1, r2) => loop r1 || loop r2
    | REclo _ => false
    | REneg r => ~loop r
  // end of [loop]
in
  loop r
end // end of [re_is_phi]

(* ****** ****** *)

#if 0

// partial derivative of [r] with respect to [c]
fun re_part_der {n:nat} .<n>. (r: re n, c: c1har):<> re0 =
  case+ r of
  | REeps () => re_phi ()
  | RErng cs => if charset_test (cs, c) then re_emp () else re_phi ()
  | REalt (r1, r2) => re_alt (re_part_der (r1, c), re_part_der (r2, c))
  | REcat (r1, r2) => if re_is_emp r1 then re_alt (re_cat (re_part_der (r1, c), r2), re_part_der (r2, c))
                      else re_cat (re_part_der (r1, c), r2)
  | REclo r' => re_cat (re_part_der (r', c), r)

#endif

// yields the derivative of r wrt to c
implement re_deriv (r, c) = let
  fun loop {n:nat} .<n>. (r: re n, c: c1har):<> re0 = case+ r of
    | REeps () => re_phi ()
    | RErng cs => if charset_test (cs, c) then re_emp () else re_phi ()
    | REcat (r1, r2) => re_cat (loop (r1, c), r2) \re_alt
                        re_cat (re_epsify r1, loop (r2, c)) where {
        fn re_epsify (r: re0):<> re0 = if re_is_emp r then re_emp () else re_phi ()
      }
    | REclo r' => re_cat (loop (r', c), r)
    | REalt (r1, r2) => re_alt (loop (r1, c), loop (r2, c))
    | REint (r1, r2) => re_int (loop (r1, c), loop (r2, c))
    | REneg r => re_neg (loop (r, c))
  // end of [loop]
in
  loop (r, c)
end

(* ****** ****** *)

// factor/compress function
implement re_factoring (r) = let
  viewtypedef lcset2 = $S.set charset

  fn cmp (x1: charset, x2: charset):<cloref> Sgn =
    compare_charset_charset (x1, x2)
  fn combine (xs: lcset2, ys: lcset2):<> lcset2 = let
    val xs = $S.linset_listize_free xs
    val ys = $S.linset_listize_free ys
    #define cons list_vt_cons
    #define nil list_vt_nil

    fun loop1 {n:nat} .<n>. (
        cs: &lcset2
      , x: charset
      , ys: !list_vt (charset, n)
      ) :<> void =
      case+ ys of
      | nil () => fold@ ys
      | cons (y, !yss) => let
          val _ = $S.linset_insert<charset> (cs, charset_intersect (x, y), cmp)
        in loop1 (cs, x, !yss); fold@ ys end // end of [let]
    // end of [loop1]

    fun loop2 {m,n:nat} .<m>. (
        cs: &lcset2
      , xs: !list_vt (charset, m)
      , ys: !list_vt (charset, n)
      ) :<> void =
      case+ xs of
      | nil () => fold@ xs
      | cons (x, !xss) => (loop1 (cs, x, ys); loop2 (cs, !xss, ys); fold@ xs)
    // end of [loop2]
    var cs = $S.linset_make_nil {charset} ()
  in
    loop2 (cs, xs, ys);
    list_vt_free xs; list_vt_free ys;
    cs
  end // end of [combine]

  fun loop {n:nat} .<n>. (r: re n):<> lcset2 =
    case+ r of
    | REeps () => s where {
        var s = $S.linset_make_nil ()
        val _ = $S.linset_insert<charset> (s, charset_universe (), cmp)
      } // end of [where]
    | RErng cs => s where {
        var s = $S.linset_make_nil ()
        val _ = $S.linset_insert<charset> (s, cs, cmp)
        val _ = $S.linset_insert<charset> (s, charset_complement cs, cmp)
      } // end of [where]
    | REcat (r, s) =>
        if ~re_is_emp r then loop r
        else combine (loop r, loop s)
    | REalt (r, s) => combine (loop r, loop s)
    | REint (r, s) => combine (loop r, loop s)
    | REclo r => loop r
    | REneg r => loop r
  // end of [loop]
  val s = loop (r)
in
  $S.linset_listize_free s
end

(* ****** ****** *)

// a simple regular expression matching algorithm
// yields [true] iff [s] is in the language of [r]
implement re_match (r, s) = let
  fun loop {i,n,k:nat | i <= k} .<k-i>. (
      r: re0, s: &strbuf (n, k)
    , i: size_t i
    ):<> bool =
    if strbuf_is_at_end (s, i) then re_is_emp r
    else loop (re_deriv (r, s[i]), s, i+1)
  // end of [loop]
in
  loop (r, s, 0)
end

(* ****** ****** *)

implement print_re (r) = let
  fun loop (r: re0): void = case+ r of
    | REeps () => print "<emp>"
    | RErng cs => print_charset cs
    | REalt (r1, r2) => (print "("; print_re r1; print "|"; print_re r2; print ")")
    | REint (r1, r2) => (print "("; print_re r1; print "&"; print_re r2; print ")")
    | REcat (r1, r2) => (print "("; print_re r1; print_re r2; print ")")
    | REclo r => (print "("; print_re r; print ")"; print "*")
    | REneg r => (print "~"; print "("; print_re r; print ")")
in
  loop (r)
end

(* ****** ****** *)

// wish Haskell's [derive Ord] clause was here...
implement compare_re_re (r, s) = let
  // lexicographical ordering
  fun loop {m,n:nat} .<m>. (r: re m, s: re n):<> Sgn =
    case+ r of
    | REeps () => begin
      case+ s of
      | REeps () => 0
      | _ => ~1
      end
    | RErng a => begin
      case+ s of
      | REeps () => 1
      | RErng b => compare (a, b)
      | _ => ~1
      end
    | REalt (r1, r2) => begin
      case+ s of
      | REeps () => 1
      | RErng _ => 1
      | REalt (s1, s2) => let
          val t = compare_re_re (r1, s1)
        in
          if t = 0 then compare_re_re (r2, s2) else t
        end
      | _ => ~1
      end
    | REint (r1, r2) => begin
      case+ s of
      | REeps () => 1
      | RErng _ => 1
      | REalt (_, _) => 1
      | REint (s1, s2) => let
          val t = compare_re_re (r1, s1)
        in
          if t = 0 then compare_re_re (r2, s2) else t
        end
      | _ => ~1
      end
    | REcat (r1, r2) => begin
      case+ s of
      | REcat (s1, s2) => let
          val t = compare_re_re (r1, s1)
        in
          if t = 0 then compare_re_re (r2, s2) else t
        end
      | REclo _ => ~1
      | REneg _ => ~1
      | _ => 1
      end
    | REclo r1 => begin
      case+ s of
      | REneg _ => ~1
      | REclo s1 => compare_re_re (r1, s1)
      | _ => 1
      end
    | REneg r1 => begin
      case+ s of
      | REneg s1 => compare_re_re (r1, s1)
      | _ => ~1
      end
  // end of [loop]
in
  loop (r, s)
end // end of [compare_re_re]
