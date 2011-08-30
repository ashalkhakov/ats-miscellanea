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

(* a very simple raytracer
 * the only supported primitive, for now, is sphere
 *
 * the approach is as follows.
 *
 * input: scene description, a camera, and image buffer
 * output: image buffer is filled up with some color data
 *
 * scene description S is just a list of spheres, sphere
 * being represented by a triple (O,R,C) where
 * O is point of origin, R is radius and C is color.
 *
 * a camera C is represented by a triple (O,A,F) where
 * O is point of origin, A is ortho-normal basis,
 * F = (fx, fy) are two values for horizontal and
 * vertical field of view (in radians), respectively.
 *
 * an image buffer I is a finite map from (s,t) to color
 * where s and t are natural numbers bounded
 * by W and H (width and height -- positive naturals),
 * respectively.
 *
 * the ray-tracing algorithm proceeds thus:
 * - spawn rays from the camera
 * - for all rays spawned:
 *   - intersect each ray against scene
 *     to intersect a ray against scene means to intersect
 *     the ray against each sphere individually
 *   - if intersection is found, compute point and normal,
 *     and calculate shading; output to the corresponding image pixel
 *   - if no intersection, output some "background" color
 *)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload M = "libc/SATS/math.sats"

(* ****** ****** *)

// various primitive types and operations

staload "SATS/vec.sats"
staload "SATS/geom.sats"
staload "SATS/imbuf.sats"
staload "SATS/scene.sats"

(* ****** ****** *)

staload _ = "DATS/vec.dats"
staload _ = "DATS/geom.dats"

(* ****** ****** *)

#define i2s size1_of_int1
#define s2f float_of_size

(* ****** ****** *)

// perform shading calculations
// very simple for now
fun shade_ray {n,m:pos} .< >.
  (s: !scene_vt (n, m), r: ray, h: hit n, e: vec3)
  :<> rgb = let
  // spot light at eye
  // L is the direction to light
  val L = vec_norm (e - h.p)
  // Lambert shading: color * dot(L, N)
  // where N is the normal at the point of impact
  // L is the direction to the light source
  // f < 0 if light cannot reach surface
  val f = max (0.0f, min (h.n * L, 1.0f))
in
  @{r= f, g= f, b= f}
end

(* ****** ****** *)

// trace the ray through the scene and perform shading
// e: eye point
fn trace_ray {n,m:pos} (s: !scene_vt (n, m), r: ray, e: vec3):<> rgb = let
  var h: hit0
in
  if :(h: hit0) => intersect_ray (s, r, h) then let
    prval () = opt_unsome {hit n} (h)
  in
    shade_ray (s, r, h, e)
  end else let
    prval () = opt_unnone {hit n} (h)
  in
    @{r= 0.0f, g= 0.0f, b= 0.0f}
  end
end // end of [trace_ray]

(* ****** ****** *)

// computing ray piercing through point (i,j) of image
// in world space

local
// we don't want any of this to be visible by callers;
// [local] will make it easier to move this code into a module
// in the future.

typedef camview (w:int, h:int) = @{
  o= vec3                                // origin
, ll= vec3, lr= vec3, ul= vec3, ur= vec3 // image plane corners
, w= size_t w, h= size_t h               // width and height
, iw= float, ih= float                   // inverse of width/height
}
typedef camview0 = @{
  o= vec3
, ll= vec3, lr= vec3, ul= vec3, ur= vec3
, w= size_t, h= size_t
, iw= float, ih= float
}?

// we want to share this computation
fun camera_to_camview .< >. {w,h:pos} (
    c: !camera, w: size_t w, h: size_t h, v: &camview0 >> camview (w, h)
  ):<> void = let
  val sinx = $M.sinf c.fov.x and siny = $M.sinf c.fov.y
  val () = let
    val x = c.f * sinx
    val y = c.f * siny
  in
    // compute corners of near plane
    // we rely on the fact that (c.f, c.fov.x, c.fov.y) can be seen
    // as spherical coordinates where left pole is (0,1,0)
    // and plane is at 0 with normal (0,0,1)
    v.ll := vec_rotate (vec_make (c.f, ~x, ~y), c.xf.a);
    v.lr := vec_rotate (vec_make (c.f, x, ~y), c.xf.a);
    v.ul := vec_rotate (vec_make (c.f, ~x, y), c.xf.a);
    v.ur := vec_rotate (vec_make (c.f, x, y), c.xf.a)
  end // end of [let]
in
  v.w := w;
  v.h := h;
  v.iw := 1.0f / float_of_size w;
  v.ih := 1.0f / float_of_size h;
  v.o := c.xf.o
end

// yields ray in world coordinates that goes through
// pixel (i,j) of image
fun cast_prim_ray_view .< >. {w,h:pos}
  (i: sizeLt w, j: sizeLt h, v: camview (w, h)):<> ray = let
  val wc = let
    #define s2f float_of_size
    val a = s2f (v.w-i) * v.iw and b = s2f (v.h-j) * v.ih
    val c = s2f i * v.iw and d = s2f j * v.ih
  in
    // a*b + a*d + b*c + c*d = 1
    // a*b, a*d, b*c, c*d are barycentric coordinates
    a*b*v.ll + a*d*v.ul + b*c*v.lr + c*d*v.ur
  end // end of [let]
in
  mk_ray (v.o, vec_norm wc)
end

in // of [local]

// spawn rays originating at [c] and piercing through image pixels;
// find intersection of each ray with scene; shade intersection points
// in: scene, camera, image buffer
// out: image buffer is filled up with some data
fn spawn_trace_rays {n,m:pos} {w,h:pos} (
    s: !scene_vt (n, m)
  , c: camera
  , ib: &image_vt (w, h)
  ):<> void = let
  fn* loop1 {i:nat | i <= w} .<w-i+1,0>. (
      i: size_t i, s: !scene_vt (n, m), c: camview (w, h), im: &image_vt (w, h)
    ):<> void =
    if i < c.w then loop2 (i, 0, s, c, im)
  // end of [loop1]

  and loop2 {i,j:nat | i < w; j <= h} .<w-i,h-j+1>. (
      i: size_t i, j: size_t j, s: !scene_vt (n, m), c: camview (w, h)
    , im: &image_vt (w, h)
    ) :<> void =
    if j < c.h then let
      val () = image_write (i, j, trace_ray (s, cast_prim_ray_view (i, j, c), c.o), im)
    in
      loop2 (i, j+1, s, c, im)
    end else loop1 (i+1, s, c, im)
  // end of [loop2]
  var cv: camview0
  val () = camera_to_camview (c, image_width ib, image_height ib, cv)
in
  loop1 (i2s 0, s, cv, ib)
end // end of [spawn_trace_rays]

end // of [local]

(* ****** ****** *)
// testing code

#ifdef TEST_RAYCAST

// the same as [cast_prim_ray_view], but more naive
// (doesn't share computations)
fun cast_prim_ray .< >. {w,h:pos} {i,j:nat | i < w; j < h}
  (i: size_t i, j: size_t j, w: size_t w, h: size_t h, c: camera):<> ray = let
  val sinx = $M.sinf c.fov.x and siny = $M.sinf c.fov.y
  local
    val x = c.f * sinx
    val y = c.f * siny
  in
    // compute corners of near plane
    // we rely on the fact that (c.f, c.fov.x, c.fov.y) are spherical coordinates
    // where left pole is (0,1,0) and plane is at 0, normal (0,0,1)
    val ll = vec_rotate (vec_make (c.f, ~x, ~y), c.xf.a)
    val lr = vec_rotate (vec_make (c.f, x, ~y), c.xf.a)
    val ul = vec_rotate (vec_make (c.f, ~x, y), c.xf.a)
    val ur = vec_rotate (vec_make (c.f, x, y), c.xf.a)
  end // end of [local]
  val wc = let
    #define s2f float_of_size
    val rw = 1.0f / s2f w and rh = 1.0f / s2f h
    val a = s2f (w-i) * rw and b = s2f (h-j) * rh
    val c = s2f i * rw and d = s2f j * rh
  in
    // a*b + a*d + b*c + c*d = 1
    // (a*b,a*d,b*c,c*d are barycentric coordinates)
    a*b*ll + a*d*ul + b*c*lr + c*d*ur
  end // end of [let]
in
  mk_ray (c.xf.o, vec_norm wc)
end // end of [cast_prim_ray]

fun print_vec3 (a: vec3): void = begin
  print "("; print a.x; print ", "; print a.y; print ", "; print a.z; print ")"
end
overload print with print_vec3
fun print_camera (cm: camera): void = begin
  print "--camera:\n";
  print "pos "; print cm.xf.o; print_newline ();
  print "axis "; print_newline ();
      print cm.xf.a.f; print_newline ();
      print cm.xf.a.r; print_newline ();
      print cm.xf.a.u; print_newline ();
  print "fovx "; print cm.fov.x; print ", fovy "; print cm.fov.y; print_newline ();
  print "nearpl "; print cm.f; print_newline ();
  print "--end camera\n"
end

fun test (): void = let
  val W = 320.0f
  val H = 240.0f
  val cm = @{xf= xform_identity (), fov= @{x= fov, y= fov * aspect}, f= 0.5f} where {
    val fov = float_of_double ($M.M_PI * 0.25)
    val aspect = H / W
    val () = begin print "aspect: "; print aspect; print_newline () end
  }
  val () = print_camera cm
  val s = mk_sphere (vec_make (10.0f, 0.0f, 0.0f), 7.0f)
  val r = cast_prim_ray (i2s 160, i2s 120, i2s 320, i2s 240, cm)
  val () = (print "cast_prim_ray direction: "; print r.d; print_newline ())
    // mk_ray (vec_make (0.0f, 0.0f, 0.0f), vec_make (1.0f, 0.0f, 0.0f))
  var t: float
in // of [let]
  if :(t: float?) => ray_sphere_test (r, s, t) then let
    prval () = opt_unsome {float} (t)
    val p = ray_origin r + ray_direction r * t
  in
    print ("TEST success: t = "); print t; print_newline ()
//    print ", intersection point at ("; print p.x; print p.y; print p.z;
  end else let
    prval () = opt_unnone {float} (t)
  in
    print ("TEST fail\n")
  end // end of [if .. then .. else ..]
end

#endif

implement main (argc, argv) =
  if argc >= 2 then let
    val name = argv.[1]
    val (pfopt | p_ifp) = fopen_err (name, file_mode_w)
  in
    if p_ifp > null then let
      prval Some_v (pf) = pfopt
#ifdef TEST_RAYCAST
      val () = test ()
#endif
      // initialize scene and camera
      var sc: scene0_vt
      #define :: list_vt_cons
      #define nil list_vt_nil
      val () = mk_scene (
          mk_sphere (vec_make (3.0f, 0.0f, 0.0f), 1.0f)
            :: mk_sphere (vec_make (4.5f, 1.0f, 1.5f), 0.5f)
            :: mk_sphere (vec_make (4.5f, ~1.0f, 1.5f), 0.5f)
            :: mk_sphere (vec_make (4.5f, ~1.0f, ~1.5f), 0.5f)
            :: mk_sphere (vec_make (4.5f, 1.0f, ~1.5f), 0.5f)
            :: nil
        , @{O= vec_make (3.0f, 3.0f, 0.0f), I= 1.0f, C= @{r= 1.0f, g= 0.5f, b= 0.5f}} :: nil
        , sc)
      val W = i2s 256 and H = i2s 256
      val cm: camera = @{xf= xform_identity (), fov= vec2_make (fovx, fovy), f= 0.5f} where {
        val fovx = float_of_double ($M.M_PI * 0.5)
        val aspect = (s2f W / s2f H)
        val fovy = fovx * aspect
      }
      var imb: image0_vt
      val () = image_initialize (W, H, imb)
#ifdef TEST_IMAGE
      val () = image_write (i2s 0, i2s 0, @{r= 1.0f, g= 0.0f, b= 0.0f}, imb)
      val () = image_write (i2s 0, i2s 1, @{r= 1.0f, g= 1.0f, b= 1.0f}, imb)
      val () = image_write (i2s 1, i2s 0, @{r= 0.0f, g= 0.0f, b= 1.0f}, imb)
      val () = print "wrote pixels\n"
#endif
      val () = spawn_trace_rays (sc, cm, imb)
      val () = image_output (file_mode_lte_w_w | !p_ifp, imb)
      val () = image_uninitialize imb
      val () = ds_scene sc
      val () = fclose_exn (pf | p_ifp)
    in
      (*empty*)
    end else let
      prval None_v () = pfopt
      val () = prerrf ("%s: can't open [%s]\n", @(argv.[0], name))
    in
      exit {void} (1)
    end
  end
