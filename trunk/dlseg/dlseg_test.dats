staload _ = "prelude/DATS/pointer.dats"

staload "dlseg.sats"
staload _ = "dlseg.dats"

// sum dllst elements with a zipper
// (mainly a demonstration/test to see how it works)
fun dllst_sum {lh,lt:addr} {n:pos} .<>.
  (pf: !dllst_v (int, lh, lt, n) | ph: ptr lh, pt: ptr lt)
  :<> int = let
  fun loop {lh,lf,lt:addr} {l,r:nat} .<r>. (
      pf: dllst_v_zipper (int, lh, lf, lt, l, r)
    | h: ptr lh, f: &ptr lf >> ptr lf', t: ptr lt, acc: int
    ):<> #[lf':addr] (dllst_v_zipper (int, lh, lf', lt, l+r, 0) | int) =
    if dlzipper_right_is_empty (pf | h, f, t) then (pf | acc)
    else let
      val (pf_at, pf_p | pi) = dlzipper_takeout (pf | h, f, t)
      val acc = acc + !pi
      val (pfz | ()) = dlzipper_move_right (pf_p pf_at | h, f, t)
    in
      loop (pfz | h, f, t, acc)
    end // end of [loop]
  // make a zipper and use it for iteration
  var p: ptr?
  val (pfz | ()) = dlzipper_make_first (pf | ph, p, pt)
  val (pfz | res) = loop (pfz | ph, p, pt, 0)
  prval () = pf := dllst_v_of_zipper_v pfz
in
  res
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
  val () = printf ("the sum of elements is %d\n", @(sum)) where {
    val sum = dllst_sum (pf | ph, pt)
  }

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