(*
** scene raytracing
** written by Artyom Shalkhakov on Dec 24, 2010
*)

(* ****** ****** *)

staload M = "libc/SATS/math.sats"

(* ****** ****** *)

staload _ = "prelude/DATS/list_vt.dats" // [list_vt_length]

(* ****** ****** *)

staload "SATS/vec.sats"
staload "SATS/geom.sats"
staload "SATS/scene.sats"
staload "SATS/bvh.sats"

(* ****** ****** *)

staload _ = "DATS/vec.dats"
staload _ = "DATS/geom.dats"
staload _ = "DATS/bvh.dats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynloading at runtime

(* ****** ****** *)

// implementation type
viewtypedef SCENE_vt (
  m:int, n:int, l:addr
) = @{
  pf_obj= array_v (sphere, m, l)
, pf_gc= free_gc_v (sphere, m, l)
, obj= ptr l
, n_obj= size_t m
, lgt= list_vt (light, n)
, bvh= BVH m
}

viewtypedef SCENE0_vt = SCENE_vt (0, 0, null)?

assume scene_vt (m:int, n:int) = [l:addr] SCENE_vt (m, n, l)

(* ****** ****** *)

implement mk_scene {m,n} (obj, lgt, sc) = () where {
  prval () = __assert (sc) where {
    extern prfun __assert (sc: &scene0_vt >> SCENE0_vt):<> void
  } // end of [prval]
  val n = size1_of_int1 (list_vt_length<sphere> (obj))
  val (pf_gc, pf_arr | p_arr) = array_ptr_alloc<sphere> (n)
  val () = array_ptr_initialize_lst_vt<sphere> (!p_arr, obj)
  val bvh = bvh_initialize (!p_arr, n)
  prval () = sc.pf_obj := pf_arr
  prval () = sc.pf_gc := pf_gc
  val () = sc.obj := p_arr
  val () = sc.n_obj := n
  val () = sc.lgt := lgt
  val () = sc.bvh := bvh
}

(* ****** ****** *)

implement ds_scene {m,n} (sc) = () where {
  val () = array_ptr_free (sc.pf_gc, sc.pf_obj | sc.obj)
  val () = bvh_uninitialize (sc.bvh)
  val () = list_vt_free (sc.lgt)
  prval () = __assert (sc) where {
    extern prfun __assert (s: &SCENE0_vt >> scene0_vt):<> void
  } // end of [prval]
}

(* ****** ****** *)

#if 1

implement intersect_ray {n,m} (s, r, res) = let
  var t: float
  var i: size_t
  val (pf_arr | p_arr) = (s.pf_obj | s.obj) // take the array out
in
  // the nearest intersection of ray with scene
  // is the same as the nearest intersection of ray
  // with the BVH of scene
  if :(t: float?, i: size_t?) => ray_bvh_test (s.bvh, !p_arr, r, t, i) then let
    prval () = opt_unsome {float} (t)
    prval () = opt_unsome {sizeLt n} (i)
    val () = res.t := t
    val () = res.p := ray_origin r + ray_direction r * t
    val () = res.id := i
    val () = res.n := sphere_normal_at (!p_arr.[i], res.p)
    prval () = opt_some {hit n} (res)
    prval () = s.pf_obj := pf_arr // put back
  in
    true
  end else let
    prval () = opt_unnone {float} (t)
    prval () = opt_unnone {sizeLt n} (i)
    prval () = opt_none {hit n} (res)
    prval () = s.pf_obj := pf_arr // put back
  in
    false
  end // end of [if .. then .. else ..]
end // end of [intersect_ray]

#else

// old code, doesn't work
fn ray_int {n,m:nat}
  (s: !scene_vt (n, m), r: ray, res: &float? >> opt (float, b))
  :<> #[b:bool] bool b = let
  fun loop {n:nat} .<n>. (
      xs: !list_vt (sphere, n), r: ray
    , b: &bool, res: &float
//  , b: &bool b >> bool b', res: &opt (float, b) >> opt (float, b')
//  b' is always greater than or equal to b, b' >= b:
//    true >= false
//    true >= true
    ):<> void = case+ xs of
    | list_vt_cons (x, !p_xs) => let
        var res': float
        var tag = ray_sphere_test (r, x, res')
        // ray_sphere_test (r, x, res') = true ^ b = true
        //  -> if res' < res then overwrite res with res'
        //     otherwise leave everything as-is
        // ray_sphere_test (r, x, res') = true ^ b = false
        //  -> if res' < res then write res' to res; true to b
        //     otherwise leave as-is
        // otherwise leave as-is
        val () = if :(res': float?) => tag then let
          prval () = opt_unsome {float} (res')
        in
          if res' < res then (b := true; res := res')
        end else let
          prval () = opt_unnone {float} (res')
        in (*empty*) end // end of [val]
      in
        loop (!p_xs, r, b, res);
        fold@ xs
      end
    | list_vt_nil () => (fold@ xs; ())
  var b = false
  var t = 0.0f
  val () = loop (s.obj, r, b, t)
in
  if b then let
    val () = res := t
    prval () = opt_some {float} (res)
  in
    true
  end else let
    prval () = opt_none {float} (res)
  in
    false
  end
end

// nothing fancy: intersect with the first element
// of the list
implement intersect_ray {n,m} (s, r, res) = let
  val list_vt_cons (sph, _) = s.obj
  val () = fold@ s.obj
  var t: float
in
  // FIXME: what if intersection point is nearer than near plane???
  if :(t: float?) => ray_sphere_test (r, sph, t) then let
    prval () = opt_unsome {float} (t)
    val () = res.t := t
    val () = res.p := ray_origin r + ray_direction r * t
    val () = res.id := size1_of_int1 0
    val () = res.n := sphere_normal_at (sph, res.p)
    prval () = opt_some {hit n} (res)
  in
    true
  end else let
    prval () = opt_unnone {float} (t)
    prval () = opt_none {hit n} (res)
  in
    false
  end // end of [if .. then .. else ..]
end
// ray_int (s, r, res)

#endif