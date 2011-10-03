(*
** A simple example of circular singly-linked list in ATS.
** Author: Artyom Shalkhakov, artyom DOT shalkhakov AT gmail DOT com
** Date: 3rd of October, 2011
** Make with:
**   atscc -o circlist circlist.dats prelude/SATS/memalign.sats
*)
staload "libats/ngc/SATS/slist.sats"
staload MA = "prelude/SATS/memalign.sats"

(* ****** ****** *)

sortdef t0p = t@ype
sortdef vt0p = viewt@ype

(* ****** ****** *)
// preliminaries: implementations
// for primitive operations on list nodes

local

viewtypedef node_vt (a:viewt@ype, ln:addr) = @{
  elem= a
, nxt= ptr ln
}
viewtypedef node_vt0 (a:viewt@ype) = @{
  elem= a
, nxt= ptr
}

assume slnode_v (a:viewt@ype, l:addr, ln:addr) = (
  freebyte_ngc_v (sizeof (node_vt0 a), l)
, node_vt (a, ln) @ l
)

in // in of [local]

implement{a} slnode_get_next {l,ln} (pf_v | p) = let
  prval (pf_fb, pf_at) = pf_v
  val res = !p.nxt
  prval () = pf_v := (pf_fb, pf_at)
in
  res
end // end of [slnode_get_next]

implement{a} slnode_set_next {l,ln} (pf_v | p, p2) = let
  prval (pf_fb, pf_at) = pf_v
  val () = !p.nxt := p2
  val () = pf_v := (pf_fb, pf_at)
in
  (*empty*)
end // end of [slnode_set_next]

implement{a} slnode_alloc () = let
  val sz = sizeof<node_vt0 (a)>
  val (pf | p) = malloc_ngc sz
in
  if p > null then let
    prval malloc_v_succ (pf_fb, pf_at) = pf
    prval pf_align = $MA.freebyte_ngc_isaligned {node_vt0 (a)} (pf_fb)
    prval pf_at = $MA.ptr_of_b0ytes_v {node_vt0 (a)} (pf_align, pf_at)
    // AS: is this necessary? typechecker says 'yes', I am in doubt
    // NOTE: [prval] instead of [val] will work just as fine, but
    // it seems more dependent on the current typechecker implementation
    val () = !p.nxt := null
  in
    #[.. | (Some_v @(pf_fb, pf_at) | p)]
  end else let
    prval malloc_v_fail () = pf
  in
    #[.. | (None_v () | null)]
  end // end of [if]
end // end of [slnode_alloc]

implement{a} slnode_free {l,ln} (pf_v | p) = let
  prval (pf_fb, pf_at) = pf_v
  val () = !p.nxt := null
  prval pf_at = ptr_to_b0ytes_v {node_vt0 (a?)} (pf_at)
in
  free_ngc (pf_fb, pf_at | p)
end // end of [slnode_free]

end // end of [local]

(* ****** ****** *)
// to work with circular linked lists, we specialize
// the definition of a singly-linked segment

viewdef cslist_v
  (a:viewt@ype, n:int, l:addr) = slseg_v (a, n, l, l)
// end of [cslist_v]

// AS: not sure if names are accurate
// also, no justification is provided

extern prfun slseg_v_isnot_null {a:vt0p} {n:nat} {l1:agz} {l2:addr} (
  pf: !slseg_v (a, n, l1, l2)
):<> [n > 0] void

extern fun slseg_is_cons {a:vt0p} {n:nat} {l1,l2:addr} (
  pf: !slseg_v (a, n, l1, l2) | p1: ptr l1, p2: ptr l2
):<> bool (n > 0) = "atspre_pneq"

extern fun slseg_is_nil {a:vt0p} {n:nat} {l1,l2:addr} (
  pf: !slseg_v (a, n, l1, l2) | p1: ptr l1, p2: ptr l2
):<> bool (n == 0) = "atspre_peq"

// prints a non-empty circular linked list, freeing it along the way
fun printcirc {n:nat} {l:agz} (
  pf_csl: cslist_v (int, n, l) | p: ptr l
) : void = let
  fun loop {n:nat} {l1,l2:addr} (
    pf_csl: slseg_v (int, n, l1, l) | p1: ptr l1, p2: ptr l
  ) : void =
    if slseg_is_cons (pf_csl | p1, p2) then let
      prval slseg_v_cons (pf_at, pf1_csl) = pf_csl
      val nxt = slnode_get_next<int> (pf_at | p1)
      prval (pf1_at, fpf) = slnode_v_takeout_val {int} (pf_at)
      val () = printf ("%d\n", @(!p1))
      prval () = pf_at := fpf (pf1_at)
      val () = slnode_free<int> (pf_at | p1)
      val () = loop (pf1_csl | nxt, p2)
    in
      (*empty*)
    end else let
      // empty!
      prval slseg_v_nil () = pf_csl
    in
      (*empty*)
    end // end of [if]
  // end of [loop]
  prval () = slseg_v_isnot_null (pf_csl)
  prval slseg_v_cons (pf_at, pf1_csl) = pf_csl
  prval (pf1_at, fpf) = slnode_v_takeout_val {int} (pf_at)
  val () = printf ("%d\n", @(!p))
  prval () = pf_at := fpf (pf1_at)
  val p' = slnode_get_next<int> (pf_at | p)
  val () = slnode_free<int> (pf_at | p)
  val () = loop (pf1_csl | p', p)
in
  (*empty*)
end // end of [printcirc]

implement main (argc, argv) = let
  val (pfopt | p1) = slnode_alloc<int> ()
in
  if p1 > null then let
    prval Some_v pf1 = pfopt
    val (pfopt | p2) = slnode_alloc<int> ()
  in
    if p2 > null then let
      prval Some_v pf2 = pfopt

      // finally, work with it
      val () = slnode_set_next<int?> (pf1 | p1, p2)
      prval (pf_at, fpf) = slnode_v_takeout_val {int?} (pf1)
      val () = !p1 := 10
      prval () = pf1 := fpf {int} (pf_at)

      val () = slnode_set_next<int?> (pf2 | p2, p1)
      prval (pf_at, fpf) = slnode_v_takeout_val {int?} (pf2)
      val () = !p2 := 15
      prval () = pf2 := fpf {int} (pf_at)

      // create a circular singly-linked list...
      prval pfsl = slseg_v_cons (pf1, slseg_v_cons (pf2, slseg_v_nil ()))
      val () = print "printing a circular list:\n"
      // ...and use it
      val () = printcirc (pfsl | p1)
    in
      print "success\n"
    end else let
      prval None_v () = pfopt
    in
      slnode_free<int> (pf1 | p1);
      print "failed to allocate memory\n"
    end
  end else let
    prval None_v () = pfopt
  in
    print "failed to allocate memory\n"
  end
end // end of [let]
