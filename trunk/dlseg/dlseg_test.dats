staload "dlseg.sats"
staload _ = "dlseg.dats"

(*
fun{a:viewt@ype} dllst_foreach_main
  {v:view} {vt:viewtype} {n:nat} {lh,lt:addr} {f:eff} (
    pf1: !dllst_v (a, lh, lt, n), pf2: !v
  | ph: ptr lh, pt: ptr lt, f: (!v | &a, !vt) -<f> void, env: !vt
  ):<f> void *)

fun dllst_sum {lh,lt:addr} {n:nat} .<>.
  (pf: !dllst_v (int, lh, lt, n) | ph: ptr lh, pt: ptr lt):<> int = let
  var res with pf_res = 0
  stavar l:addr
  val pres: ptr l = &res
  fun f (pf: !unit_v | s: &int, x: !unit_vt ()): void = () // !x := !x + s
  prval pf_v = unit_v ()
  val () = dllst_foreach_main<int> {unit_v} (pf, pf_v | ph, pt, f, ())
  prval unit_v () = pf
in
end

implement main (argc, argv) = let
  var n1 with pf_n1 = @{prev= null, next= null, itm= 5}
  var n2 with pf_n2 = @{prev= null, next= null, itm= 10}
  var n3 with pf_n3 = @{prev= null, next= null, itm= 15}

  val pn1 = &n1 and pn2 = &n2 and pn3 = &n3
  var ph: ptr? and pt: ptr?

  val (pf | ()) = dllst_make_empty (ph, pt)
  val (pf | ()) = dllst_cons (pf, pf_n1 | ph, pt, pn1)
  val (pf | ()) = dllst_cons (pf, pf_n2 | ph, pt, pn2)
  val (pf | ()) = dllst_cons (pf, pf_n3 | ph, pt, pn3)

  var p1: ptr? and p2: ptr? and p3: ptr?

  val (pf, pf3_at | ()) = dllst_uncons (pf | ph, pt, p3)
  val (pf, pf2_at | ()) = dllst_uncons (pf | ph, pt, p2)
  val (pf, pf1_at | ()) = dllst_uncons (pf | ph, pt, p1)

  prval dlseg_v_none () = pf

  val () = assert_errmsg (p2 = pn2, "something bad happened")
  val () = assert_errmsg (p1 = pn1, "something bad happened")

  prval () = pf_n1 := pf1_at
  prval () = pf_n2 := pf2_at
  prval () = pf_n3 := pf3_at
in
end