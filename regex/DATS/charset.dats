(*
** Sparse character set represented by intervals.
** Translated from SML by Artyom Shalkhakov, original code is by John Reppy.
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynloading at run-time

(* ****** ****** *)

staload _ = "prelude/DATS/list.dats"

staload "SATS/charset.sats"

(* ****** ****** *)

(*
** It is strange to me that characters in ATS are actually signed on my system!
** (treating 'char' as unsigned gives unexpected results when comparing characters against 255).
** Also, NUL is defined to be 0!
*)

// exclude 0 (see also CHAR_MIN in prelude/SATS/char.sats)
#define CHAR_MIN 1
#define CHAR_MAX 127

(* ****** ****** *)

// in: a <= b
// these functions are not tail-recursive (and not used anywhere)
extern fun add_range (x: charset, a: char, b: char):<> charset
extern fun add (x: charset, a: char):<> charset

(* ****** ****** *)

// invariant: fst(x) <= snd(x)
typedef interval = (char, char)
// list of disjoint, ordered intervals
// x:char is in the set S iff it is within any of the intervals
assume charset = List interval

(* ****** ****** *)

typedef listi (n:int) = list (interval, n)

#define nil list_nil
#define cons list_cons
#define LT ~1
#define EQ 0
#define GT 1

(* ****** ****** *)

implement charset_empty () = nil ()

implement charset_universe () = cons ((char_of_int CHAR_MIN, char_of_int CHAR_MAX), nil ())

implement charset_is_empty (x) = list_is_empty x

implement charset_is_universe (x) = case+ x of
  | cons ((a, b), nil ()) when a = char_of_int CHAR_MIN && b = char_of_int CHAR_MAX => true
  | _ => false

implement charset_sing (x) = cons ((x, x), nil ())

implement charset_range (a, b) = cons ((a, b), nil ())

implement charset_extract (x, y) = case+ x of
  | nil () => (y := '\000'; false)
  | cons ((a, _), _) => let
      val () = y := char1_of_char a
      val () = $effmask_all (assert_errmsg (y <> '\000', "something bad happened"))
    in true end
// end of [charset_extract]

(* ****** ****** *)

fn min_char_char (x: char, y: char):<> char =
  if x < y then x else y
overload min with min_char_char

// pred CHAR_MIN = CHAR_MIN and succ CHAR_MAX = CHAR_MAX
fn pred (x: char):<> char = char_of_int (max (CHAR_MIN, int_of_char x - 1))
fn succ (x: char):<> char = char_of_int (min (CHAR_MAX, int_of_char x + 1))

// is_succ (a, b) -> (succ a) = b and a = (pred b)
fn is_succ (x: char, y: char):<> bool =
  succ x = y

(* ****** ****** *)

implement add_range (x, a, b) = let
  // a <= b
  fun ins {n:nat} .<n>. (a: char, b: char, xs: listi n):<> List interval =
    case+ xs of
    | nil () => cons ((a, b), nil ())
    | cons ((x, y), r) => begin
      case+ compare (b, x) of
      | LT => begin
          if is_succ (b, x) then cons ((a, y), r)
          else cons ((a, b), cons ((x, y), r))
        end // end of case [LT]
      | EQ => cons ((a, y), r)
      | GT => begin
        case+ compare (a, y) of
        | GT => begin
            if is_succ (y, a) then cons ((x, b), r)
            else cons ((x, y), ins (a, b, r))
          end // end of sub-case [GT]
        | EQ => ins (x, b, r)
        | LT => begin
          case compare (b, y) of
          | GT => ins (min (a, x), b, r)
          | _ => ins (min (a, x), y, r)
          end // end of case [LT]
        end // end of case [GT]
      end // end of [begin]
in
  ins (a, b, x)
end // end of [add_range]

(* ****** ****** *)

implement add (x, a) = let
  fun ins {n:nat} .<n>. (a: char, xs: listi n):<> charset = case+ xs of
    | nil () => charset_sing a
    | cons ((x, y), r) => begin
      case+ compare (a, x) of
      | LT => begin
          if is_succ (a, x) then cons ((a, y), r)
          else cons ((a, a), cons ((x, y), r))
        end // end of case [LT]
      | EQ => cons ((a, y), r)
      | GT => begin
          case compare (a, y) of
          | GT => if is_succ (y, a) then cons ((x, a), r) else cons ((x, y), ins (a, r))
          | _ => cons ((x, y), r)
          end // end of case [GT]
      end // end of [begin]
  // end of [ins]
in
  ins (a, x)
end // end of [add]

(* ****** ****** *)

implement charset_test (l, pt) = let
  fun look {n:nat} .<n>. (
      l: listi n
    , pt: char
    ):<> bool = case+ l of
    | nil () => false
    | cons ((a, b), r) => begin
      case+ compare (a, pt) of
      | LT => begin
        case+ compare (pt, b) of
        | GT => look (r, pt)
        | _ => true
        end // end of case [LT]
      | EQ => true
      | GT => false
      end // end of case [cons]
  // end of [look]
in
  look (l, pt)
end // end of [charset_test]

(* ****** ****** *)

implement charset_complement (x) = case+ x of
  | nil () => charset_universe ()
  | cons ((a, b), r) => let
      fun comp {m:nat} .<m>. (start: char, x: listi m, l: charset):<> charset = case+ x of
        | cons ((a, b), r) => comp (succ b, r, cons ((start, pred a), l))
        | nil () => begin
          case+ compare (start, char_of_int CHAR_MAX) of
          | LT => list_of_list_vt (list_reverse (cons ((start, char_of_int CHAR_MAX), l)))
          | _ => list_of_list_vt (list_reverse l)
          end // end of [begin]
      // end of [comp]

      // tail-recursive version of [comp]
      // in: start <= lowerbound(x)
      fun loop {m:nat} .<m>. (start: char, x: listi m, res: &(List interval)? >> charset):<> void = case+ x of
        | cons ((a, b), r) => let
            // start <= pred a
            val () = res := cons {interval} {0} ((start, pred a), ?)
            val+ cons (_, !p) = res
          in
            loop (succ b, r, !p); fold@ res
          end
        | nil () => begin
            case+ compare (start, char_of_int CHAR_MAX) of
            | LT => (res := cons ((start, char_of_int CHAR_MAX), nil ()))
            | _ => (res := nil ())
          end
      // end of [loop]
      var res: List interval // uninitialized
    in
      case+ compare (char_of_int CHAR_MIN, a) of
      | LT => let
          val () = res := cons {interval} {0} ((char_of_int CHAR_MIN, pred a), ?); val+ cons (_, !p) = res
          val () = loop (succ b, r, !p)
        in
          fold@ res; res
        end // comp (succ b, r, cons ((char_of_int CHAR_MIN, pred a), nil ()))
      | _ => let
          val () = loop (succ b, r, res)
        in
          res  
        end // comp (succ b, r, nil ())
    end // end of [let]
// end of [charset_complement]

(* ****** ****** *)

implement charset_union (l1, l2) = let
  fun join {n,m:nat} .<n,m>. (l1: listi n, l2: listi m):<> charset = case+ (l1, l2) of
    | (nil (), _) => l2
    | (_, nil ()) => l1
    | (cons ((a1, b1), r1), cons ((a2, b2), r2)) => begin
      case+ compare (a1, a2) of
      | LT => begin
        case+ compare (b1, b2) of
        | LT => begin
            if is_succ (b1, a2) then join (r1, cons ((a1, b2), r2))
            else cons ((a1, b1), join (r1, cons ((a2, b2), r2)))
          end
        | EQ => cons ((a1, b1), join (r1, r2))
        | GT => join (cons ((a1, b1), r1), r2)
        end // end of case [LT]
      | EQ => begin
        case+ compare (b1, b2) of
        | LT => join (r1, cons ((a2, b2), r2))
        | EQ => cons ((a1, b1), join (r1, r2))
        | GT => join (cons ((a1, b1), r1), r2)
        end // end of case [EQ]
      | GT => begin
        case+ compare (a1, b2) of
        | LT => begin
          case+ compare (b1, b2) of
          | LT => join (r1, cons ((a2, b2), r2))
          | EQ => cons ((a2, b2), join (r1, r2))
          | GT => join (cons ((a2, b1), r1), r2)
          end // end of sub-case [LT]
        | EQ => (* a2 < a1 = b2 <= b1 *) join (cons ((a2, b1), r1), r2)
	| GT => begin
            if is_succ (b2, a1) then join (cons ((a2, b1), r1), r2)
            else cons ((a2, b2), join (cons ((a1, b1), r1), r2))
          end // end of sub-case [GT]
        end // end of case [GT]
      end // end of [begin]
  // this is the same as the function above, but tail-recursive
  typedef I = interval
  fun loop {n,m:nat} .<n,m>. (l1: listi n, l2: listi m, res: &(List interval)? >> charset):<> void = case+ (l1, l2) of
    | (nil (), _) => res := l2
    | (_, nil ()) => res := l1
    | (cons ((a1, b1), r1), cons ((a2, b2), r2)) => begin
      case+ compare (a1, a2) of
      | LT => begin
        case+ compare (b1, b2) of
        | LT => begin
            if is_succ (b1, a2) then loop (r1, cons ((a1, b2), r2), res)
            else let
              val () = res := cons {I} {0} ((a1, b1), ?); val+ cons (_, !p) = res
            in
              loop (r1, cons ((a2, b2), r2), !p); fold@ res
            end
          end
        | EQ => let
            val () = res := cons {I} {0} ((a1, b1), ?); val+ cons (_, !p) = res
          in
            loop (r1, r2, !p); fold@ res
          end
        | GT => loop (cons ((a1, b1), r1), r2, res)
        end // end of case [LT]
      | EQ => begin
        case+ compare (b1, b2) of
        | LT => loop (r1, cons ((a2, b2), r2), res)
        | EQ => let
            val () = res := cons {I} {0} ((a1, b1), ?); val+ cons (_, !p) = res
          in
            loop (r1, r2, !p); fold@ res
          end
        | GT => loop (cons ((a1, b1), r1), r2, res)
        end // end of case [EQ]
      | GT => begin
        case+ compare (a1, b2) of
        | LT => begin
          case+ compare (b1, b2) of
          | LT => loop (r1, cons ((a2, b2), r2), res)
          | EQ => let
              val () = res := cons {I} {0} ((a2, b2), ?); val+ cons (_, !p) = res
            in
              loop (r1, r2, !p); fold@ res
            end
          | GT => loop (cons ((a2, b1), r1), r2, res)
          end // end of sub-case [LT]
        | EQ => (* a2 < a1 = b2 <= b1 *) loop (cons ((a2, b1), r1), r2, res)
	| GT => begin
            if is_succ (b2, a1) then loop (cons ((a2, b1), r1), r2, res)
            else let
              val () = res := cons {I} {0} ((a2, b2), ?); val+ cons (_, !p) = res
            in
              loop (cons ((a1, b1), r1), r2, !p); fold@ res
            end
          end // end of sub-case [GT]
        end // end of case [GT]
      end // end of [begin]
  // end of [loop]

  var res: List interval // uninitialized
in
  loop (l1, l2, res); res // join (l1, l2)
end

(* ****** ****** *)

// forall x:char, a:set, b:set, c:set.
//   member (a, x) -> member (b, x) -> c = intersect (a, b) -> member (c, x)
implement charset_intersect (l1, l2) = let
  // cons a possibly empty interval onto the front of l
  fn kons {n:nat} (
      a: char, b: char
    , l: list (interval, n)
    ):<> [n':nat | n' == n || n' == n+1] list (interval, n') =
    if a > b then l else cons ((a, b), l)
  // end of [kons]
  fun meet {n,m:nat} .<n,m>. (x: listi n, y: listi m):<> charset = case+ (x, y) of
    | (nil (), _) => nil ()
    | (_, nil ()) => nil ()
    | (cons ((a1, b1), r1), cons ((a2, b2), r2)) => begin
      case+ compare (a1, a2) of
      | LT => begin
        case+ compare (b1, a2) of
        | LT => (* a1 <= b1 < a2 <= b2 *) meet (r1, cons ((a2, b2), r2))
        | EQ => (* a1 <= b1 = a2 <= b2 *) cons ((b1, b1), meet (r1, kons (succ b1, b2, r2)))
	| GT => begin
          case+ compare (b1, b2) of
          | LT => (* a1 < a2 < b1 < b2 *) cons ((a2, b1), meet (r1, kons (succ b1, b2, r2)))
          | EQ => (* a1 < a2 < b1 = b2 *) cons ((a2, b1), meet (r1, r2))
          | GT => (* a1 < a2 < b1 & b2 < b1  *) cons ((a2, b2), meet (kons (succ b2, b1, r1), r2))
          end // end of sub-case [GT]
        end // end of case [LT]
      | EQ => begin
        case+ compare (b1, b2) of
        | LT => cons ((a1, b1), meet (r1, kons (succ b1, b2, r2)))
        | EQ => cons ((a1, b1), meet (r1, r2))
        | GT => cons ((a1, b2), meet (cons ((succ b2, b1), r1), r2))
        end // end of case [EQ]
      | GT => begin
        case+ compare (b2, a1) of
        | LT => (* a2 <= b2 < a1 <= b1 *) meet (cons ((a1, b1), r1), r2)
	| EQ => (* a2 < b2 = a1 <= b1 *) cons ((b2, b2), meet (kons (succ b2, b1, r1), r2))
        | GT => begin
          case+ compare (b1, b2) of
          | LT => (* a2 < a1 <= b1 < b2 *) cons ((a1, b1), meet (r1, kons (succ b1, b2, r2)))
          | EQ => (* a2 < a1 <= b1 = b2 *) cons ((a1, b1), meet (r1, r2))
          | GT => (* a2 < a1 < b2 < b1 *) cons ((a1, b2), meet (kons (succ b2, b1, r1), r2))
          end // end of sub-case [GT]
        end // end of case [GT]
      end // end of [meet]
  // this is the same as the version above but tail-recursive
  typedef I = interval
  fun loop {n,m:nat} .<n,m>. (x: listi n, y: listi m, res: &(List interval)? >> charset):<> void = case+ (x, y) of
    | (nil (), _) => res := nil ()
    | (_, nil ()) => res := nil ()
    | (cons ((a1, b1), r1), cons ((a2, b2), r2)) => begin
      case+ compare (a1, a2) of
      | LT => begin
        case+ compare (b1, a2) of
        | LT => (* a1 <= b1 < a2 <= b2 *) loop (r1, cons ((a2, b2), r2), res)
        | EQ => let (* a1 <= b1 = a2 <= b2 *)
            val () = res := cons {I} {0} ((b1, b1), ?); val+ cons (_, !p) = res
          in
            loop (r1, kons (succ b1, b2, r2), !p); fold@ res
          end
	| GT => begin
          case+ compare (b1, b2) of
          | LT => let (* a1 < a2 < b1 < b2 *)
              val () = res := cons {I} {0} ((a2, b1), ?); val+ cons (_, !p) = res
            in
              loop (r1, kons (succ b1, b2, r2), !p); fold@ res
            end
          | EQ => let (* a1 < a2 < b1 = b2 *)
              val () = res := cons {I} {0} ((a2, b1), ?); val+ cons (_, !p) = res
            in
              loop (r1, r2, !p); fold@ res
            end
          | GT => let (* a1 < a2 < b1 & b2 < b1 *)
              val () = res := cons {I} {0} ((a2, b2), ?); val+ cons (_, !p) = res
            in
              loop (kons (succ b2, b1, r1), r2, !p); fold@ res
            end
          end // end of sub-case [GT]
        end // end of case [LT]
      | EQ => begin
        case+ compare (b1, b2) of
        | LT => let
            val () = res := cons {I} {0} ((a1, b1), ?); val+ cons (_, !p) = res
          in
            loop (r1, kons (succ b1, b2, r2), !p); fold@ res
          end
        | EQ => let
            val () = res := cons {I} {0} ((a1, b1), ?); val+ cons (_, !p) = res
          in
            loop (r1, r2, !p); fold@ res
          end
        | GT => let
            val () = res := cons {I} {0} ((a1, b2), ?); val+ cons (_, !p) = res
          in
            loop (cons ((succ b2, b1), r1), r2, !p); fold@ res
          end
        end // end of case [EQ]
      | GT => begin
        case+ compare (b2, a1) of
        | LT => (* a2 <= b2 < a1 <= b1 *) loop (cons ((a1, b1), r1), r2, res)
	| EQ => let (* a2 < b2 = a1 <= b1 *)
            val () = res := cons {I} {0} ((b2, b2), ?); val+ cons (_, !p) = res
          in
            loop (kons (succ b2, b1, r1), r2, !p); fold@ res
          end
        | GT => begin
          case+ compare (b1, b2) of
          | LT => let (* a2 < a1 <= b1 < b2 *)
              val () = res := cons {I} {0} ((a1, b1), ?); val+ cons (_, !p) = res
            in
              loop (r1, kons (succ b1, b2, r2), !p); fold@ res
            end
          | EQ => let (* a2 < a1 <= b1 = b2 *)
              val () = res := cons {I} {0} ((a1, b1), ?); val+ cons (_, !p) = res
            in
              loop (r1, r2, !p); fold@ res
            end
          | GT => let (* a2 < a1 < b2 < b1 *)
              val () = res := cons {I} {0} ((a1, b2), ?); val+ cons (_, !p) = res
            in
              loop (kons (succ b2, b1, r1), r2, !p); fold@ res
            end
          end // end of sub-case [GT]
        end // end of case [GT]
      end // end of [loop]
  var res: List interval // uninitialized
in
  loop (l1, l2, res); res
end // end of [let]

(* ****** ****** *)

// experimental version of [charset_difference] consuming both its arguments
fn charset_vt_difference (x: List_vt interval, y: List_vt interval):<> List_vt interval =
  charset_vt_intersect (x, charset_vt_complement y)

// FIXME: replace the following with a direct implementation
implement charset_difference (x, y) = charset_intersect (x, charset_complement y)

(* ****** ****** *)

implement compare_charset_charset (l1, l2) = let
  fun comp {n,m:nat} .<n,m>. (l1: listi n, l2: listi m):<> Sgn = case+ (l1, l2) of
    | (nil (), nil ()) => EQ
    | (cons ((a1, b1), r1), cons ((a2, b2), r2)) => begin
      case+ compare (a1, a2) of
      | EQ => begin
        case+ compare (b1, b2) of
        | EQ => comp (r1, r2)
        | t => t
        end // end of case [EQ]
      | t => t
      end // end of [begin]
    | (nil (), _) => LT
    | (_, nil ()) => GT
in
  comp (l1, l2)
end // end of [compare_charset_charset]

(* ****** ****** *)

implement print_charset (x) = let
  fun loop (x: charset): void =
    case+ x of
    | cons ((a, b), x) => begin
        if a = b then print (uint_of_char a)
        else begin
          print (uint_of_char a); print ".."; print (uint_of_char b)
        end;
        if ~list_is_empty x then print ",";
        loop x
      end
    | nil () => ()
  // end of [loop]
in
  print "["; loop x; print "]"
end // end of [print_charset]
