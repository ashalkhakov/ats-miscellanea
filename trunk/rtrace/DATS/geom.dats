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
** various things related to computational geometry
*)

(* ****** ****** *)

staload M = "libc/SATS/math.sats"

(* ****** ****** *)

staload "SATS/vec.sats"
staload "SATS/geom.sats"

(* ****** ****** *)

staload _ = "DATS/vec.dats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynloading at run-time

(* ****** ****** *)

assume ray = @{o= vec3, d= vec3}

// pre: magnitude of [d] = 1
implement{} mk_ray (o, d) = let
  // TODO
//  val () = assert_errmsg (vec_len d ~ 1.0f, "direction must be normalized")
in @{o= o, d= d} end

implement{} ray_origin (x) = x.o
implement{} ray_direction (x) = x.d
implement{} ray_point (x, t) = x.o + t * x.d

(* ****** ****** *)

assume sphere = @{o= vec3, r= float}

implement{} mk_sphere (o: vec3, r: float): sphere = let
  val () = assert_errmsg (r > 0.0f, "radius must be nonnegative")
in @{o= o, r= r} end

implement{} sphere_origin (x) = x.o
implement{} sphere_radius (x) = x.r

(* ****** ****** *)

assume bbox = @{min= vec3, max= vec3}

implement{} bbox_make (a, b) = @{min= a, max= b}
implement{} bbox_min (x) = x.min
implement{} bbox_max (x) = x.max
implement{} bbox_of_ray (r, t0, t1) = let
  val t0p = ray_point (r, t0)
  val t1p = ray_point (r, t1)
in
  bbox_make (vec_min (t0p, t1p), vec_max (t0p, t1p))
end

implement ray_bbox_test (r, b, tnear, tfar) = let
  // not robust! based on the slab test which I know nothing of
  // (picked up from tbp of ompf.org)
  // FIXME: what is the geometrical interpretation of [rpint]?
  fn rpint (r: ray, p: vec3):<> vec3 = (p - ray_origin r) / ray_direction r

  val l1 = rpint (r, bbox_min b) and l2 = rpint (r, bbox_max b)
  val np = min (l1, l2) and fp = max (l1, l2)
  val () = tnear := max (np.x, max (np.y, np.z)) and () = tfar := min (fp.x, min (fp.y, fp.z))
in
  if :(tnear: float?, tfar: float) => tfar >= tnear && tfar >= 0.0f then let
    prval () = opt_some {float} (tnear) and () = opt_some {float} (tfar)
  in true end else let
    prval () = opt_none {float} (tnear) and () = opt_none {float} (tfar)
  in false end
end

(* ****** ****** *)

(*
** assume a sphere [(c, r)] (where c:R^3, r:R).
** point p:R^3 lies on the surface of the sphere if
**   (p - c) * (p - c) = r^2 (1)
** given a ray [(o, d)] such that [ray(t) = o + t*d] where [t>=0],
** we can find the [t] at which the ray intersects the sphere
** by substituting [ray(t)] for [p] in the equation (1):
**   (ray(t) - c) * (ray(t) - c) = r^2
** ->(o + t*d - c) * (o + t*d - c) = r^2
** to solve for [t] we first expand the above into a more recognizable
** form:
**   (d*d)t^2 + 2(o-c)dt + (o-c)*(o-c) - r^2 = 0
** or
**   At^2 + Bt + C = 0
**   A = d*d
**   B = 2(o - c)d
**   C = (o - c)*(o - c) - r^2
** which can be solved using standard algebraic means
*)
implement ray_sphere_test (r, s, res) = let
  val oc = r.o - s.o
  val a = r.d * r.d
  val b = 2.0f * (oc * r.d)
  val c = oc * oc - s.r*s.r
  val dsc = b*b - 4.0f*a*c
in
  case+ 0 of
  | _ when dsc < 0.0f => let // no intersection
      prval () = opt_none {float} (res)
    in false end
  | _ when dsc < 0.1f => let // one point
      val () = res := ~b / 2.0f * a
      prval () = opt_some {float} (res)
    in true end
  | _ => let // two points, we need the nearest one
      val sqdsc = $M.sqrtf dsc
      val t0 = (~b - sqdsc) / 2.0f * a
      val t1 = (~b + sqdsc) / 2.0f * a
    in
      if t1 < 0.0f then let // no intersection
        prval () = opt_none {float} (res)
      in false end else let
        val () = if :(res: float) => t0 < 0.0f then res := t1 else res := t0
        prval () = opt_some {float} (res)
      in true end
    end
end

implement sphere_normal_at (s, p) = vec_norm (p - s.o)

(* ****** ****** *)

implement bbox_of_face (f) = let
  val a = min (f.v0, min (f.v1, f.v2))
  val b = max (f.v0, max (f.v1, f.v2))
in
  bbox_make (a, b)
end

// the method is due to "Fast, Minimum Storage
// Ray/Triangle Intersection" (Moller & Trumbore)
implement ray_face_test (r, f, t, u, v) = let
  val V0 = f.v0 and V1 = f.v1 and V2 = f.v2
  val edge1 = V1 - V0 and edge2 = V2 - V0
  val pvec = vec_cross (ray_direction r, edge2)
  val det = edge1 * pvec
in
  if det < 1e-6f then let // ray is on the back of the face
    prval () = opt_none {float} (t)
      and () = opt_none {float} (u)
      and () = opt_none {float} (v)
  in
    false
  end else let
    // calculate distance from V0 to ray origin
    val tvec = ray_origin r - V0
    // calculate u parameter and test bounds
    val () = u := tvec * pvec
  in
    if u < 0.0f || u > det then let
      prval () = opt_none {float} (t)
        and () = opt_none {float} (u)
        and () = opt_none {float} (v)
    in
      false
    end else let
      val qvec = vec_cross (tvec, edge1)
      val () = v := ray_direction r * qvec
    in
      if v < 0.0f || u + v > det then let
        prval () = opt_none {float} (t)
          and () = opt_none {float} (u)
          and () = opt_none {float} (v)
      in
        false
      end else let
        // calculate t, scale parameters
        val () = t := edge2 * qvec
        val () = let
          val inv_det = 1.0f / det
        in
          t := t * inv_det;
          u := u * inv_det;
          v := v * inv_det
        end
        prval () = opt_some {float} (t)
          and () = opt_some {float} (u)
          and () = opt_some {float} (v)
      in
        true
      end
    end
  end
end

implement ray_face_test_hit (r, f) = let
  // I'm feeling lazy today
  var t: float and u: float and v: float
  val res = ray_face_test (r, f, t, u, v)
  prval () = __assert (t, u, v) where {
    extern prfun __assert {b:bool} (
        t: &opt (float, b) >> float?
      , u: &opt (float, b) >> float?
      , v: &opt (float, b) >> float?
      ): void
  }
in
  res
end
