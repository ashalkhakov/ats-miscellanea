staload "SATS/charset.sats"
staload "SATS/charset_vt.sats"
staload "SATS/regexp.sats"
staload "SATS/dfa.sats"

staload _ = "prelude/DATS/list_vt.dats"

dynload "DATS/charset.dats"
dynload "DATS/charset_vt.dats"
dynload "DATS/linset.dats"
dynload "DATS/regexp.dats"
dynload "DATS/dfa.dats"

(* ****** ****** *)

fun charset_vt_testing (): void = let
  val alp = charset_vt_union (charset_vt_range ('a', 'z'), charset_vt_range ('A', 'Z'))
  val nilcs = charset_vt_intersect (charset_vt_range ('a', 'z'), charset_vt_range ('A', 'Z'))
  val univ = charset_vt_complement (charset_vt_empty ());
  val alp2 = charset_vt_union (
              charset_vt_union (charset_vt_range ('a', 'z'), charset_vt_range ('A', 'Z')),
              charset_vt_range ('j', 'k'))
in
  print alp; charset_vt_free (alp); print_newline ();
  print nilcs; charset_vt_free (nilcs); print_newline ();
  print univ; charset_vt_free (univ); print_newline ();
  print alp2; charset_vt_free alp2; print_newline ()
end

fun charset_testing (): void = let
  fun pr (b: bool, r: bool): void = begin
    print "result: "; print b; print ", anticipated: "; print r;
    print_newline ()
  end
  val () = print "testing charset\n"
  val alp = charset_union (charset_range ('a', 'z'), charset_range ('A', 'Z'))
  val () = pr (charset_test (alp, 'm'), true)
  val () = pr (charset_test (alp, '0'), false)
  val () = pr (charset_test (alp, 'X'), true)
  val () = pr (charset_test (alp, '-'), false)
  val alp2 = charset_union (alp, charset_range ('j', 'k'))
  val () = pr (compare (alp, alp2) = 0, true)
  val ab = charset_intersect (alp, charset_sing ('X')) // charset_sing 'X'
  val () = pr (compare (ab, charset_sing 'X') = 0, true)

  val () = (print "small letters: "; print (charset_range ('a', 'z')); print_newline ())
  val () = (print "capital letters: "; print (charset_range ('A', 'Z')); print_newline ())

  val alp = charset_union (charset_range ('A', 'Z'), charset_range ('a', 'z'))
  val () = (print "small & capital letters: "; print alp; print_newline ())

  val () = (print "complement of [a]: "; print (charset_complement (charset_sing 'a')); print_newline ())
  val () = print (charset_difference (charset_range ('a', 'z'), charset_range ('a', 'c')))
  val () = print_newline ()

  val () = pr (compare (charset_difference (charset_range ('a', 'z'), charset_sing ('e')),
                        charset_union (charset_range ('a', 'd'), charset_range ('f', 'z'))) = 0, true)

  val () = print (compare (charset_range ('a', 'c'), charset_range ('a', 'z')))
  val () = print_newline ()
  val () = print "end of charset testing\n"
in
  (*empty*)
end

fun test_factor (): void = let
  // r = (a|ba)|c
  val r = re_alt (re_alt (re_lit 'a', re_cat (re_lit 'b', re_lit 'a')), re_lit 'c')
  val fr = re_factoring r
  val () = begin print "print factoring for: "; print r; print_newline () end
  val () = list_vt_foreach_fun<charset> (fr, lam (x) =<fun1> print x)
  val () = list_vt_free fr
in
  print "--end of factoring tests\n"
end // end of [test_factor]

fun test_dfa (): void = let
  val () = () where {
    var !p_str0 with pf_str0 = @[byte](byte_of_char '\000')
    val () = bytes_strbuf_trans (pf_str0 | p_str0, 0)
    val b = re_match (re_emp (), !p_str0)
    prval () = pf_str0 := bytes_v_of_strbuf_v pf_str0
    val () = printf ("%d\n", @(if b then 1 else 0))
  }

  val digit = '0' \re_rng '9'
  val () = () where {
    val d = dfa_make digit
    val () = print_dfa d
    val () = dfa_free d
  }
  val () = () where {
    var !p_str0 with pf_str0 = @[byte](byte_of_char '5', byte_of_char '\000')
    val () = bytes_strbuf_trans (pf_str0 | p_str0, 1)
    val b = re_match (digit, !p_str0)
    prval () = pf_str0 := bytes_v_of_strbuf_v pf_str0
    val () = printf ("%d\n", @(if b then 1 else 0))    
  }
  val two_digits = digit \re_cat digit
  val () = () where {
    val d = dfa_make two_digits
    val () = print_dfa d
    val () = dfa_free d
  }
  val () = () where {
    var !p_str0 with pf_str0 = @[byte](byte_of_char '5', byte_of_char '9', byte_of_char '\000')
    val () = bytes_strbuf_trans (pf_str0 | p_str0, 2)
    val b = re_match (two_digits, !p_str0)
    prval () = pf_str0 := bytes_v_of_strbuf_v pf_str0
    val () = printf ("%d\n", @(if b then 1 else 0))
  }

  val digits = re_clo digit
  val () = () where {
    val d = dfa_make digits
    val () = print_dfa d
    val () = dfa_free d
  }
  val () = () where {
    var !p_str0 with pf_str0 = @[byte](byte_of_char '5', byte_of_char '9', byte_of_char '0', byte_of_char '\000')
    val () = bytes_strbuf_trans (pf_str0 | p_str0, 3)
    val b = re_match (digits, !p_str0)
    prval () = pf_str0 := bytes_v_of_strbuf_v pf_str0
    val () = printf ("%d\n", @(if b then 1 else 0))
  }

  val letter = re_rng ('a', 'z') \re_alt re_rng ('A', 'Z')
  val () = () where {
    val d = dfa_make letter
    val () = print_dfa d
    val () = dfa_free d
  }
  val () = () where {
    var !p_str0 with pf_str0 = @[byte](byte_of_char 'X', byte_of_char '\000')
    val () = bytes_strbuf_trans (pf_str0 | p_str0, 1)
    val b = re_match (letter, !p_str0)
    prval () = pf_str0 := bytes_v_of_strbuf_v pf_str0
    val () = printf ("%d\n", @(if b then 1 else 0))
  }

  val letters = re_clo letter
  val ident = re_cat (letter, re_clo (re_alt (letter, digit)))
  val () = () where {
    val d = dfa_make ident
    val () = print_dfa d
    val () = dfa_free d
  }
  // the hard-core way :) (not recommended)
  var !p_str0 with pf_str0 = @[byte](byte_of_char 'a', byte_of_char 'b', byte_of_char 'c', byte_of_char '1', byte_of_char 'b', byte_of_char 'z', byte_of_char '\000')
  val () = bytes_strbuf_trans (pf_str0 | p_str0, 6)
  val b = re_match (ident, !p_str0)
  prval () = pf_str0 := bytes_v_of_strbuf_v pf_str0
  val () = printf ("%d\n", @(if b then 1 else 0))
in
  (*empty*)
end // end of [test_dfa]

implement main (argc, argv) = let
  val () = charset_vt_testing ()
//  val () = charset_testing ()
//  val () = test_factor ()
//  val () = test_dfa ()
in
  // empty
end
