(*
** Experimental code: linear character sets.
** Written by Artyom Shalkhakov on Apr 3, 2011.
*)

staload _ = "prelude/DATS/list_vt.dats"

staload "SATS/charset_vt.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynloading at run-time

(* ****** ****** *)

#define CHAR_MIN 1
#define CHAR_MAX 127

// invariant: fst(x) <= snd(x)
typedef interval = (char, char)

(* ****** ****** *)

// list of disjoint, ordered intervals
// x:char is in the set S iff it is within any of the intervals
assume charset_vt = List_vt interval

(* ****** ****** *)

#define nil list_vt_nil
#define cons list_vt_cons
#define LT ~1
#define EQ 0
#define GT 1

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

implement charset_vt_empty () = nil ()

implement charset_vt_universe () =
  cons ((char_of_int CHAR_MIN, char_of_int CHAR_MAX), nil ())

implement charset_vt_sing (x: char) =
  cons ((x, x), nil ())

implement charset_vt_range (a, b) =
  cons ((a, b), nil ())

implement charset_vt_free (xs) = list_vt_free<interval> (xs)

(* ****** ****** *)

implement charset_vt_complement (x) = let
  fun loop {n:nat} .<n>. (
      a: char, b: char
    , xs: list_vt (interval, n), res: &List_vt interval? >> List_vt interval
    ):<> void = case+ xs of
    | list_vt_nil () => (fold@ xs; res := list_vt_cons ((a, b), xs))
    | list_vt_cons (!p_x, !p_xs1) => let
        val x = !p_x.0 and y = !p_x.1
      in
        case+ compare (a, x) of
        | LT => begin
            !p_x.0 := a; !p_x.1 := pred x;
            res := xs;
            if is_succ (succ y, b) then let
              val xs1 = !p_xs1
            in
              list_vt_free xs1;
              !p_xs1 := list_vt_nil (); fold@ res
            end else let
              val xs1 = !p_xs1
            in
              loop (succ y, b, xs1, !p_xs1); fold@ res
            end
          end // end of [begin]
        | _ => let
            val xs1 = !p_xs1
          in
            free@ {interval} {0} (xs);
            if is_succ (succ y, b) then begin
              list_vt_free xs1;
              res := list_vt_nil ()
            end else loop (succ y, b, xs1, res)
          end // end of [let]
      end // end of [let]
  var res: List_vt interval
in
  loop (char_of_int CHAR_MIN, char_of_int CHAR_MAX, x, res); res
end

(* ****** ****** *)

implement charset_vt_union (l1, l2) = let
  // a version of [loop] which does no memory allocation by reusing the memory
  // of two input lists
  typedef I = interval
  fun loop1 {n,m:nat} .<n,m>. (
      l1: list_vt (I, n), l2: list_vt (I, m), res: &List_vt I? >> List_vt I
    ):<> void = case+ (l1, l2) of
    | (~list_vt_nil (), _) => res := l2
    | (_, ~list_vt_nil ()) => res := l1
    | (list_vt_cons (!p_x1, !p_r1), list_vt_cons (!p_x2, !p_r2)) => let
        val a1 = !p_x1.0 and b1 = !p_x1.1
        val a2 = !p_x2.0 and b2 = !p_x2.1
      in
        case+ compare (a1, a2) of
        | LT => begin
          case+ compare (b1, b2) of
          | LT => begin
              if is_succ (b1, a2) then let
                val r1 = !p_r1
                val () = !p_x2.0 := !p_x1.0; // coalesce the two intervals
              in
                free@ {I} {0} (l1); fold@ (l2); loop1 (r1, l2, res)
              end else let
                val r1 = !p_r1
              in
                fold@ l2; res := l1;
                loop1 (r1, l2, !p_r1); fold@ res
              end
            end
          | EQ => let
              val r1 = !p_r1 and r2 = !p_r2
            in
              free@ {I} {0} (l2); res := l1;
              loop1 (r1, r2, !p_r1); fold@ res
            end
          | GT => let
              val r2 = !p_r2
            in
              fold@ l1; free@ {I} {0} (l2); loop1 (l1, r2, res)
            end
          end // end of case [LT]
        | EQ => begin
          case+ compare (b1, b2) of
          | LT => let
              val r1 = !p_r1
            in
              free@ {I} {0} (l1); fold@ l2; loop1 (r1, l2, res)
            end
          | EQ => let
              val r1 = !p_r1 and r2 = !p_r2
            in
              free@ {I} {0} (l2); res := l1;
              loop1 (r1, r2, !p_r1); fold@ res
            end
          | GT => let
              val r1 = !p_r1 and r2 = !p_r2
            in
              free@ {I} {0} (l2); res := l1; loop1 (r1, r2, !p_r1); fold@ res
            end
          end // end of case [EQ]
        | GT => begin
          case+ compare (a1, b2) of
          | LT => begin
            case+ compare (b1, b2) of
            | LT => let
                val r1 = !p_r1
              in
                free@ {I} {0} (l1); fold@ l2; loop1 (r1, l2, res)
              end
            | EQ => let
                val r1 = !p_r1 and r2 = !p_r2
              in
                free@ {I} {0} (l2); res := l1;
                loop1 (r1, r2, !p_r1); fold@ res
              end
            | GT => let
                val r2 = !p_r2
              in
                !p_x1.0 := !p_x1.1;
                free@ {I} {0} (l2); fold@ l1; loop1 (l1, r2, res)
              end
            end // end of sub-case [LT]
          | EQ => (* a2 < a1 = b2 <= b1 *) let
              val r2 = !p_r2
            in
              !p_x1.0 := !p_x2.0;
              free@ {I} {0} (l2); fold@ l1; loop1 (l1, r2, res)
            end
  	| GT => begin
              if is_succ (b2, a1) then let
                val r2 = !p_r2
              in
                !p_x1.0 := !p_x2.0;
                free@ {I} {0} (l2); fold@ l1; loop1 (l1, r2, res)
              end else let
                val r2 = !p_r2
              in
                fold@ l1; res := l2; loop1 (l1, r2, !p_r2); fold@ res
              end
            end // end of sub-case [GT]
          end // end of case [GT]
      end // end of [let]
  // end of [loop1]
  var res: List_vt interval
in
  loop1 (l1, l2, res); res
end

(* ****** ****** *)

// experimental version of [charset_intersect] consuming both its arguments
implement charset_vt_intersect (l1, l2) = let
  // cons a possibly empty interval onto [!p_rst]
  fn kons {n:nat} {l0,l1:addr} (
      pf0: interval @ l0, pf1: list_vt (interval, n) @ l1
    | a: char, b: char
    , node: list_vt_cons_unfold (l0, l1)
    , p_x: ptr l0
    , p_rst: ptr l1
    ):<> [n':nat | n' == n || n' == n+1] list_vt (interval, n') =
    if a > b then let val rst = !p_rst in
      free@ {interval} {0} (node); rst
    end else begin
      !p_x.0 := a; !p_x.1 := b; fold@ node; node
    end
  // end of [kons]

  fun loop {n,m:nat} .<n,m>. (
      x: list_vt (interval, n), y: list_vt (interval, m)
    , res: &List_vt interval? >> List_vt interval
    ):<> void = case+ (x, y) of
    | (list_vt_nil (), _) => (fold@ x; res := x; list_vt_free y)
    | (_, list_vt_nil ()) => (fold@ y; res := y; list_vt_free x)
    | (list_vt_cons (!p_x1, !p_r1), list_vt_cons (!p_x2, !p_r2)) => let
        val a1 = !p_x1.0 and b1 = !p_x1.1
        val a2 = !p_x2.0 and b2 = !p_x2.1
      in
        case+ compare (a1, a2) of
        | LT => begin
          case+ compare (b1, a2) of
          | LT => (* a1 <= b1 < a2 <= b2 *) let
              val r1 = !p_r1
            in
              free@ {interval} {0} (x); fold@ y; loop (r1, y, res)
            end
          | EQ => let (* a1 <= b1 = a2 <= b2 *)
              val r1 = !p_r1
            in
              !p_x1.0 := b1; !p_x1.1 := b1; res := x;
              loop (r1, kons (view@ (!p_x2), view@ (!p_r2) | succ b1, b2, y, p_x2, p_r2), !p_r1); fold@ res
            end
          | GT => begin
            case+ compare (b1, b2) of
            | LT => let (* a1 < a2 < b1 < b2 *)
                val r1 = !p_r1
              in
                !p_x1.0 := a2; res := x;
                loop (r1, kons (view@ (!p_x2), view@ (!p_r2) | succ b1, b2, y, p_x2, p_r2), !p_r1); fold@ res
              end
            | EQ => let (* a1 < a2 < b1 = b2 *)
                val r1 = !p_r1 and r2 = !p_r2
              in
                !p_x1.0 := a2; free@ {interval} {0} (y); res := x;
                loop (r1, r2, !p_r1); fold@ res
              end
            | GT => let (* a1 < a2 < b1 & b2 < b1 *)
                val r2 = !p_r2
              in
                res := y;
                loop (kons (view@ (!p_x1), view@ (!p_r1) | succ b2, b1, x, p_x1, p_r1), r2, !p_r2); fold@ res
              end
            end // end of sub-case [GT]
          end // end of case [LT]
        | EQ => begin
          case+ compare (b1, b2) of
          | LT => let
              val r1 = !p_r1
            in
              free@ {interval} {0} (x);
              loop (r1, kons (view@ (!p_x2), view@ (!p_r2) | succ b1, b2, y, p_x2, p_r2), res)
            end
          | EQ => let
              val r1 = !p_r1 and r2 = !p_r2
            in
              res := x; free@ {interval} {0} (y);
              loop (r1, r2, !p_r1); fold@ res
            end
          | GT => let
              val r2 = !p_r2
            in
              !p_x1.0 := succ b2; fold@ x;
              res := y; !p_x2.0 := a1;
              loop (x, r2, !p_r2); fold@ res
            end
          end // end of case [EQ]
        | GT => begin
          case+ compare (b2, a1) of
          | LT => (* a2 <= b2 < a1 <= b1 *) let
              val r2 = !p_r2
            in
              fold@ x; free@ {interval} {0} (y); loop (x, r2, res)
            end
          | EQ => (* a2 < b2 = a1 <= b1 *) let
              val r2 = !p_r2
            in
              free@ {interval} {0} (y);
              loop (kons (view@ (!p_x1), view@ (!p_r1) | succ b2, b1, x, p_x1, p_r1), r2, res)
            end
          | GT => begin
            case+ compare (b1, b2) of
            | LT => let (* a2 < a1 <= b1 < b2 *)
                val r1 = !p_r1
              in
                res := x;
                loop (r1, kons (view@ (!p_x2), view@ (!p_r2) | succ b1, b2, y, p_x2, p_r2), !p_r1); fold@ res
              end
            | EQ => let (* a2 < a1 <= b1 = b2 *)
                val r1 = !p_r1 and r2 = !p_r2
              in
                res := x; free@ {interval} {0} (y);
                loop (r1, r2, !p_r1); fold@ res
              end
            | GT => let (* a2 < a1 < b2 < b1 *)
                val r2 = !p_r2
              in
                !p_x2.0 := a1; res := y;
                loop (kons (view@ (!p_x1), view@ (!p_r1) | succ b2, b1, x, p_x1, p_r1), r2, !p_r2); fold@ res
              end
            end // end of sub-case [GT]
          end // end of case [GT]
    end // end of [loop]
  var res: List_vt interval
in
  loop (l1, l2, res); res
end

(* ****** ****** *)

implement print_charset (x) = let
  fun loop (x: !charset_vt): void =
    case+ x of
    | list_vt_cons ((a, b), !p_x1) => begin
        if a = b then print (uint_of_char a)
        else begin
          print (uint_of_char a); print ".."; print (uint_of_char b)
        end;
        (case+ !p_x1 of
        | nil () => fold@ (!p_x1)
        | cons _ => (fold@ (!p_x1); print ","));
        loop (!p_x1);
        fold@ x
      end
    | list_vt_nil () => fold@ x
  // end of [loop]
in
  print "["; loop x; print "]"
end // end of [print_charset]

