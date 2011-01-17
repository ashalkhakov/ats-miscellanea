(*
** rtrace -- a typeful ray tracer program
**
** Copyright (C) 2011 Artyom Shalkhakov
**
** All rights reserved
**
** rtrace is free software;  you can  redistribute it and/or modify it
** under the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published
** by the Free Software Foundation; either version 2.1, or (at your option)
** any later version.
** 
** rtrace is distributed in the hope that it will be useful, but WITHOUT
** ANY WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY
** or FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  rtrace;  see the  file COPYING.  If not, please write to
** the Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston,
** MA 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Artyom Shalkhakov (artyom DOT shalkhakov AT gmail DOT com) *)

(* ****** ****** *)

(*
** implementation of BVH (construction and tracing of rays)
** started by Artyom Shalkhakov in the evening of Jan 15,
** finished in the morning of Jan 16
*)

(* ****** ****** *)

staload _ = "prelude/DATS/array.dats" // array_ptr_exch template

(* ****** ****** *)

staload "SATS/vec.sats"
staload "SATS/geom.sats"
staload "SATS/accs.sats"

(* ****** ****** *)

staload _ = "DATS/vec.dats"
staload _ = "DATS/geom.dats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

// axis-aligned plane
// ax= 0 <-> dir= (1, 0, 0)
// ax= 1 <-> dir= (0, 1, 0)
// ax= 2 <-> dir= (0, 0, 1)
typedef pln = @{ax= axis3, dist= float}

// returns true iff point is in front of plane
fn pln_point_infront (pl: pln, p: vec3):<> bool =
  vec3_get_elt_at__intsz (p, pl.ax) - pl.dist > 1e-4f

(* ****** ****** *)
(* a concrete representation for BVH *)

// TODO: store more than one primitive in a leaf (2,4,8,...)
dataviewtype bvh_vt (n:int, int) =
  | bvh_vt_leaf (n, 0) of sizeLt n
  | {s1,s2:nat} bvh_vt_node (n, s1+s2+1) of (
      bbox           // bbox enclosing both subtrees
    , pln            // splitting plane for imposing ordering
                     // on subtrees wrt to axis
    , bvh_vt (n, s1) // at the back of [pln]
    , bvh_vt (n, s2) // in front of [pln]
    )
viewtypedef bvh0_vt (n:int) = [s:nat] bvh_vt (n, s)

assume accs_vt (n:int) = bvh0_vt n

(*
** given a list of size [n], the total number
** of binary tree nodes will be less than or equal
** to [2*n-1].
**
** TODO: recast this problem as a more general one.
** can you say this about a binary tree?
*)

(* ****** ****** *)
(* construction and destruction *)

implement accs_initialize {n} (p, n) = let
  // compute bbox that encloses all primitives
  fun bbox_for_prim {k:nat} (
    id: &(@[sizeLt n][k])
  , isz: size_t k
  , prim: &(@[sphere][n])
  ): bbox = let
    fn bbox_of_sphere (s: sphere):<> bbox = let
      val r = sphere_radius s
      val min = vec_make (~r, ~r, ~r)
      val max = vec_make (r, r, r)
    in
      bbox_make (min, max)
    end // end of [bbox_of_sphere]

    fun loop {k:nat} {i:nat | i <= k} (
        id: &(@[sizeLt n][k]), isz: size_t k
      , i: size_t i
      , prim: &(@[sphere][n])
      , mn: &vec3, mx: &vec3
      ): void = if i < isz then let
        val b = bbox_of_sphere (prim.[id.[i]])
        val () = mn := min (mn, bbox_min b)
        val () = mx := max (mx, bbox_max b)
      in
        loop (id, isz, i+1, prim, mn, mx)
      end // end of [loop]
    val HUGEVAL = 16384.0f
    var min = vec_make (HUGEVAL, HUGEVAL, HUGEVAL)
    var max = vec_make (~HUGEVAL, ~HUGEVAL, ~HUGEVAL)
    val () = loop (id, isz, 0, prim, min, max)
  in
    bbox_make (min, max)
  end // end of [bbox_for_prim]

  // given a plane, partition the input list.
  // when [part] finishes, [p_id] is partitioned
  // into two sublists such that:
  // - the former contains primitives that are in front
  //   of the splitting plane,
  // - the latter contains primitives to the back
  //   of the splitting plane
  fn part {k:pos} {l:addr} (
    pf_id: array_v (sizeLt n, k, l)
  | p_id: ptr l
  , isz: size_t k
  , prim: &(@[sphere][n])
  , pl: pln
  ):<> [i:nat | i < k] [ofs:nat] (
    MUL (i, sizeof size_t, ofs)
  , array_v (sizeLt n, i, l), array_v (sizeLt n, k-i, l+ofs)
  | size_t i, ptr (l+ofs)
  ) = let
    // returns true iff [s] is in front of [p]
    fn prim_plane_classify (s: sphere, p: pln):<> bool = let
      // find distance from center of [s] to [p]
      val c = vec3_get_elt_at__intsz (sphere_origin s, p.ax) - p.dist
      val r = sphere_radius s
    in
      // compare distance against radius
      c - r >= 1e-4f
    end // end of [prim_plane_classify]

    // when [loop] terminates, the resulting [r] tells us:
    // 0..r are elements to the back of [pl]
    // r..k are elements in front of [pl]
    fun loop {j:nat | j < k} {i:nat | i <= j} .<j-i>. (
        pf_id: !array_v (sizeLt n, k, l)
      | p_id: ptr l, isz: size_t k
      , prim: &(@[sphere][n])
      , i: size_t i, j: size_t j
      , pl: pln
      ):<> sizeLt k = let
        #define gte prim_plane_classify
        fun l2r {i':nat | i <= i'; i' <= j} .<j-i'>. (
            pf_id: !array_v (sizeLt n, k, l)
          | p_id: ptr l, prim: &(@[sphere][n]), pl: pln, i': size_t i', j: size_t j
          ):<> [r:int | i' <= r; r <= j] size_t r =
          if i' < j then
            if gte (prim.[!p_id.[i']], pl) then i'
            else l2r (pf_id | p_id, prim, pl, succ i', j)
          else i' // end of [l2r]
        val [i':int] i' = l2r (pf_id | p_id, prim, pl, i, j)
        fun r2l {j':nat | i' <= j'; j' <= j} .<j'-i'>. (
            pf_id: !array_v (sizeLt n, k, l)
          | p_id: ptr l, prim: &(@[sphere][n]), pl: pln, i': size_t i', j': size_t j'
          ):<> [r:int | i' <= r; r <= j] size_t r =
          if i' < j' then
            if ~gte (prim.[!p_id.[j']], pl) then j'
            else r2l (pf_id | p_id, prim, pl, i', pred j')
          else j' // end of [r2l]
        val [j':int] j' = r2l (pf_id | p_id, prim, pl, i', j)
      in
        if i' < j' then begin
          array_ptr_exch<sizeLt n> (!p_id, i', j');
          // FIXME: should we recur with i'+1, j'-1?
          loop (pf_id | p_id, isz, prim, i'+1, j', pl)
        end else i'
      end // end of [loop]
    val j = loop (pf_id | p_id, isz, prim, 0, pred isz, pl)
    val (pf_mul, pf1_id, pf2_id | p_id') =
      array_ptr_split (pf_id | p_id, j)
  in
    (pf_mul, pf1_id, pf2_id | j, p_id')
  end // end of [part]

  fun choose_plane {k:pos} {l:addr} (
      pf_id: !array_v (sizeLt n, k, l)
    | p_id: ptr l, isz: size_t k, prim: &(@[sphere][n]), bx: bbox
    ): pln = let
    // for now, split along longest axis
    fn mk_plane (bx: bbox):<> pln = let
      // pick longest axis
      fn amax (a: pln, b: pln):<> pln =
        if a.dist > b.dist then a else b
      val x = ((bbox_max bx).x - (bbox_min bx).x) / 2.0f
      val y = ((bbox_max bx).y - (bbox_min bx).y) / 2.0f
      val z = ((bbox_max bx).z - (bbox_min bx).z) / 2.0f
      fn pln (a: axis3, d: float):<> pln = @{ax= a, dist= d}
    in
      amax (pln (Ax, x), amax (pln (Ay, y), pln (Az, z)))
    end // end of [mk_plane]
  in
    mk_plane bx
  end // end of [choose_plane]

  // find a split that keeps the tree balanced
  // protip:
  // if a median split shows that we have empty space, continue
  // with the non-empty voxel
  // do this stuff ad infinitum (actually, don't know if this terminates
  // for all inputs, but it does for the scenes I've ran it on)
  fun split {k:pos} {l:addr} (
    pf_id: array_v (sizeLt n, k, l)
  | p_id: ptr l
  , isz: size_t k
  , prim: &(@[sphere][n])
  , bx: bbox
  ): [i:pos | i < k] [ofs:nat] (
    MUL (i, sizeof size_t, ofs)
  , array_v (sizeLt n, i, l), array_v (sizeLt n, k-i, l+ofs)
  | size_t i, ptr (l+ofs), pln
  ) = let
    // yields the part of bbox that is in front of plane
    // in: (bbox_min b)[p.ax] <= p.dist
    // out: (bbox_min res)[p.ax] = p.dist
    fn bbox_plane_front (b: bbox, p: pln):<> bbox = let
      val mn = vec3_set_elt_at__intsz (bbox_min b, p.ax, p.dist)
    in
      bbox_make (mn, bbox_max b)
    end // end of [bbox_plane_front]

    // yields the part of bbox that is at the back of plane
    // in: (bbox_max b)[p.ax] >= p.dist
    // out: (bbox_max res)[p.ax] = p.dist
    fn bbox_plane_back (b: bbox, p: pln):<> bbox = let
      val mx = vec3_set_elt_at__intsz (bbox_max b, p.ax, p.dist)
    in
      bbox_make (bbox_min b, mx)
    end // end of [bbox_plane_back]

    val pl = choose_plane (pf_id | p_id, isz, prim, bx)
    val (pf_mul, pf1_id, pf2_id | i, p_id') = part (pf_id | p_id, isz, prim, pl)
  in
    if i = 0 then let
      // nothing at the back of [pl],
      // continue with the half of the volume where
      // all the primitives reside
      prval () = array_v_unnil {sizeLt n} (pf1_id)
      prval MULbas () = pf_mul
    in
      split (pf2_id | p_id', isz, prim, bbox_plane_front (bx, pl))
    end else if isz - i = 0 then let
      // nothing in front of [pl],
      // continue with the half of the volume where
      // all the primitives reside
      prval () = array_v_unnil {sizeLt n} (pf2_id)
    in
      split (pf1_id | p_id, isz, prim, bbox_plane_back (bx, pl))
    end else begin
      // base case: the list is split into two non-empty sublists
      (pf_mul, pf1_id, pf2_id | i, p_id', pl)
    end
  end // end of [split]

  // TODO: move result into a call-by-reference argument,
  // so we can make use of one tail recursive call per node
  fun bvh_mk {k:pos} {l:addr} (
      pf_id: !array_v (sizeLt n, k, l)
    | p_id: ptr l
    , isz: size_t k
    , prim: &(@[sphere][n])
    , bx: bbox
    ): bvh0_vt n =
    if isz <= 1 then bvh_vt_leaf (!p_id.[0])
    else let
      // partition the input list in-place
      val [i:int] [ofs:int] (pf_mul, pf1_id, pf2_id | sz1, p_id', pl) =
        split (pf_id | p_id, isz, prim, bx)
      val l = bvh_mk (pf1_id | p_id, sz1, prim, bbox_for_prim (!p_id, sz1, prim))
      val r = bvh_mk (pf2_id | p_id', isz - sz1, prim, bbox_for_prim (!p_id', isz - sz1, prim))
      prval () = pf_id := array_v_unsplit {sizeLt n} (pf_mul, pf1_id, pf2_id)
    in
      bvh_vt_node (bx, pl, l, r)
    end // end of [bvh_mk]

  val (pf_gc, pf_id | p_id) = array_ptr_alloc<size_t?> (n)
  val () = () where {
    // when [loop] finishes, array will be in the form
    // forall i:int. i >= 0 && i < n -> !a.[i] = i
    // (where [a] is array of size [n])
    fun loop {n:nat} {i:nat | i <= n} {l:addr} .<n-i>. (
        pf_arr: array_v (size_t?, n-i, l)
      | p_arr: ptr l, i: size_t i, n: size_t n
      ):<> (array_v (sizeLt n, n-i, l) | void) =
      if i < n then let
        prval (pf_at, pf_rst) = array_v_uncons {size_t?} (pf_arr)
        val () = !p_arr := i
        val (pf_rst | ()) = loop (pf_rst | p_arr+sizeof<size_t>, i+1, n)
      in
        (array_v_cons {sizeLt n} (pf_at, pf_rst) | ())
      end else let
        prval () = array_v_unnil {size_t ?} (pf_arr)
      in
        (array_v_nil {sizeLt n} () | ())
      end // end of [loop]
    // initially, [p_id] represents an identity map
    val (pf_id' | ()) = loop (pf_id | p_id, 0, n)
    prval () = pf_id := pf_id'
  }
  // The upper bound on the size of BVH structure 2*n-1
  // (assuming n is the count of primitives, each leaf contains
  // only one of them, and that a bvh node divides the input
  // list of primitives in half).
  // TODO: prove this result, then formalize in ATS
  // TODO: remove GC stress altogether by preallocation
  val res = bvh_mk (pf_id | p_id, n, p, bbox_for_prim (!p_id, n, p))
  val () = array_ptr_free (pf_gc, pf_id | p_id)
in
  res
end

// will implement deallocation when [BVH]
// is made into a viewtype
implement accs_uninitialize {n} (bvh) = let
  fun bvh_free {n,s:nat} .<s>. (bvh: bvh_vt (n, s)):<> void =
    case+ bvh of
    | ~bvh_vt_leaf _ => ()
    | ~bvh_vt_node (_, _, l, r) => begin
        bvh_free l;
        bvh_free r
      end // end of [bvh_free]
in
  bvh_free (bvh)
end

(* ****** ****** *)
(* tracing rays through BVH *)

fun ray_test {n,s:nat} .<s>. (
    bvh: !bvh_vt (n, s)
  , p: &(@[sphere][n])
  , rs: ray
  , t: &float, s: &sizeLt n
  , tn: float, tf: float
  ):<> bool = case+ bvh of
  | bvh_vt_leaf s' => let
      var t': float
      val res = ray_sphere_test (rs, p.[s'], t')
    in
      if :(t': float?) => res then let
        prval () = opt_unsome {float} (t')
      in
        if t' < t then begin
          t := t';
          s := s'
        end;
        fold@ bvh;
        res
      end else let prval () = opt_unnone {float} (t') in fold@ bvh; res end
    end
  | bvh_vt_node (b, pl, !l, !r) => let
      var tnear': float and tfar': float
      val res = ray_bbox_test (rs, b, tnear', tfar')
    in
      if :(tnear': float?, tfar': float?) => ~res then let
        prval () = opt_unnone {float} (tnear')
        prval () = opt_unnone {float} (tfar')
      in
        fold@ bvh; false
      end else let
        prval () = opt_unsome {float} (tnear')
        prval () = opt_unsome {float} (tfar')
        val res = if pln_point_infront (pl, ray_origin rs) then begin
                    ray_test (!r, p, rs, t, s, tnear', tfar') ||
                    ray_test (!l, p, rs, t, s, tnear', tfar')
                  end else begin
                    ray_test (!l, p, rs, t, s, tnear', tfar') ||
                    ray_test (!r, p, rs, t, s, tnear', tfar')
                  end
      in
        fold@ bvh; res
      end
    end // end of [ray_test]

implement ray_accs_test {n} (bvh, p, r, t, s) = let
  val () = t := 16384.0f // something outside of scene (could be infinity)
  val () = s := size1_of_int1 0
  val res = ray_test (bvh, p, r, t, s, t, t)
in
  if :(t: float?, s: sizeLt n?) => res then let
    prval () = opt_some {float} (t)
    prval () = opt_some {sizeLt n} (s)
  in true end else let
    prval () = opt_none {float} (t)
    prval () = opt_none {sizeLt n} (s)
  in false end
end
