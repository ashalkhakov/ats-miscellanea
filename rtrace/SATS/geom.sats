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

(* computational geometry algorithms *)

(* ****** ****** *)

staload "SATS/vec.sats"

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at runtime

(* ****** ****** *)

// axis-aligned plane
// ax= 0 <-> dir= (1, 0, 0)
// ax= 1 <-> dir= (0, 1, 0)
// ax= 2 <-> dir= (0, 0, 1)
typedef pln = @{ax= axis3, dist= float}

// returns true iff point is in front of plane
fun pln_point_infront (pl: pln, p: vec3):<> bool

(* ****** ****** *)

// ray: origin and direction
abst@ype ray = @{o= vec3, d= vec3}

// pre: magnitude of [d] = 1
fun{} mk_ray (o: vec3, d: vec3):<> ray
fun{} ray_origin (x: ray):<> vec3
fun{} ray_direction (x: ray):<> vec3
fun{} ray_point (x: ray, t: float):<> vec3

(* ****** ****** *)

// sphere: origin and radius
abst@ype sphere = @{o= vec3, r= float}

// pre: [r > 0]
fun{} mk_sphere (o: vec3, r: float): sphere
fun{} sphere_origin (x: sphere):<> vec3
fun{} sphere_radius (x: sphere):<> float

(* ****** ****** *)
// axis-aligned bounding box

// property that should be enforced: min <= max
abst@ype bbox = @{min= vec3, max= vec3}

fun{} bbox_make (min: vec3, max: vec3):<> bbox
fun{} bbox_min (x: bbox):<> vec3
fun{} bbox_max (x: bbox):<> vec3

// given a ray and two ray parameters t0 and t1 (t0 <= t1),
// construct an axis-aligned bounding box
fun{} bbox_of_ray (r: ray, t0: float, t1: float):<> bbox

// true if ray hits the box,
// and tnear/tfar are ray parameters for the entry/exit points
fun ray_bbox_test (
  r: ray, b: bbox, tnear: &float? >> opt (float, b), tfar: &float? >> opt (float, b)
):<> #[b:bool] bool b

(* ****** ****** *)

// returns true if ray intersects sphere, in that case
// [res] will contain the parameter to [r] for the (nearest)
// intersection point.
// it is expected that ray and sphere are in one coordinate
// frame!
// out: res >= 0 if b == true
fun ray_sphere_test
  (r: ray, s: sphere, res: &float? >> opt (float, b))
  :<> #[b:bool] bool b

// computes sphere normal at point [p]
// in: [p] must be on sphere! (as determined by
//     [ray_sphere_test])
fun sphere_normal_at (s: sphere, p: vec3):<> vec3

// in: sphere
// out: bbox encompassing sphere
fun bbox_of_sphere (s: sphere):<> bbox

// returns true iff [s] is in front of [p]
fun pln_sphere_infront (p: pln, s: sphere):<> bool

(* ****** ****** *)

typedef face = @{
  v0= vec3, v1= vec3, v2= vec3
}

// computes bounding box for a face
fun bbox_of_face (f: face):<> bbox

// reports whether ray hits a face at all
fun ray_face_test_hit (r: ray, f: face):<> bool

// in:
// - V0, V1 and V2 are vertices of the triangular face
// - V0, V1 and V2 are in the counter-clockwise order
// out (b = true):
// - t is the distance alogn ray, t >= 0
// - u and v are barycentric coordinates within triangle;
//   u >= 0, v >= 0, u + v <= 1
// out (b = false):
// - ray doesn't intersect the triangle
fun ray_face_test (
    r: ray, f: face
  , t: &float? >> opt (float, b)
  , u: &float? >> opt (float, b)
  , v: &float? >> opt (float, b)
  ):<> #[b:bool] bool b
