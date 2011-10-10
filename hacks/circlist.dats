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
// our circular singly-linked list definition

dataview cslist_v (a:vt0p, int, addr) =
  | cslist_v_none (a, 0, null)
  | {n:nat} {l1:agz;l2:addr}
    cslist_v_some (a, n+1, l1) of (
      slnode_v (a, l1, l2), slseg_v (a, n, l2, l1)
    ) // end of [cslst_v]

extern
fun{a:vt0p}
  cslist_is_nil
  {n:nat} {l:addr}
  (pf: !cslist_v (a, n, l) | p: ptr l)
  :<> bool (n == 0)
// end of [cslist_is_nil]

extern
fun{a:vt0p}
  cslist_is_cons
  {n:nat} {l:addr}
  (pf: !cslist_v (a, n, l) | p: ptr l)
  :<> bool (n > 0)
// end of [cslist_is_cons]

extern
fun{a:vt0p}
  cslist_make_sing
  {l1,l2:addr} (
    pfnod: slnode_v (a, l1, l2)
  | p: ptr l1
  ) :<> (cslist_v (a, 1, l1) | void)
// end of [cslist_make_sing]

extern
fun{a:vt0p}
  cslist_insert_after
  {n:pos} {l1,l2,l3:addr} (
    pfnod: slnode_v (a, l2, l3)
  , pfcsl: !cslist_v (a, n, l1) >> cslist_v (a, n+1, l1)
  | p1: ptr l1, p2: ptr l2
  ) :<> void
// end of [cslist_insert_after]

(* ****** ****** *)

implement{a} cslist_is_nil {n} {l} (pf | p) =
  if p > null then let
    prval cslist_v_some (pf_hd, pf_seg) = pf
    prval () = pf := cslist_v_some (pf_hd, pf_seg)
  in
    false
  end else let
    prval cslist_v_none () = pf
    prval () = pf := cslist_v_none ()
  in
    true
  end // end of [cslist_is_nil]

implement{a} cslist_is_cons {n} {l} (pf | p) = ~cslist_is_nil (pf | p)

implement{a} cslist_make_sing {l1,l2} (pf_nod | p) = let
  prval () = slnode_ptr_is_gtz (pf_nod)
  val () = slnode_set_next (pf_nod | p, p)
in
  (cslist_v_some (pf_nod, slseg_v_nil ()) | ())
end // end of [cslist_make_sing]

implement{a} cslist_insert_after {n} {l1,l2,l3} (
  pf_nod, pf_csl | p1, p2
) = let
  prval () = slnode_ptr_is_gtz (pf_nod)
  prval cslist_v_some (pf_hd, pf_seg) = pf_csl
  val () = slnode_set_next (pf_nod | p2, slnode_get_next (pf_hd | p1))
  val () = slnode_set_next (pf_hd | p1, p2)
  prval () = pf_csl := cslist_v_some (pf_hd, slseg_v_cons (pf_nod, pf_seg))
in
  (*empty*)
end // end of [cslist_insert_after]

(* ****** ****** *)

// prints a non-empty circular linked list, freeing it along the way
fun printcirc {n:pos} {l:addr} (
  pf_csl: cslist_v (int, n, l) | p: ptr l
) : void = let
  fun loop {n:nat} {l1,l2:addr} (
    pf_nod: slnode_v (int, l1, l2),
    pf_seg: slseg_v (int, n, l2, l)
  | p1: ptr l1, p2: ptr l
  ) : void = let
    prval (pf1_at, fpf) = slnode_v_takeout_val {int} (pf_nod)
    val () = printf ("%d\n", @(!p1))
    prval () = pf_nod := fpf (pf1_at)
    val p' = slnode_get_next<int> (pf_nod | p1)
    val () = slnode_free<int> (pf_nod | p1)
  in
    if p' <> p2 then let
      prval slseg_v_cons (pf_nod, pf1_seg) = pf_seg
    in
      loop (pf_nod, pf1_seg | p', p2)
    end else let
      prval () = __assert () where {
        extern prfun __assert (): [n <= 0] void
      } // end of [prval]
      prval slseg_v_nil () = pf_seg
    in
      (*empty*)
    end // end of [if]
  end // end of [loop]
  // end of [loop]
  prval cslist_v_some (pf_hd, pf_seg) = pf_csl
in
  loop (pf_hd, pf_seg | p, p)
end // end of [printcirc]

(* ****** ****** *)

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
      prval (pf_at, fpf) = slnode_v_takeout_val {int?} (pf1)
      val () = !p1 := 10
      prval () = pf1 := fpf {int} (pf_at)

      val (pfcl | ()) = cslist_make_sing<int> (pf1 | p1)

      prval (pf_at, fpf) = slnode_v_takeout_val {int?} (pf2)
      val () = !p2 := 15
      prval () = pf2 := fpf {int} (pf_at)

      val () = cslist_insert_after<int> (pf2, pfcl | p1, p2)
      val () = print "printing a circular list:\n"
      val () = printcirc (pfcl | p1)
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
