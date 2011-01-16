(* computational geometry algorithms
** written by Artyom Shalkhakov
*)

(* ****** ****** *)

staload "SATS/vec.sats"

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at runtime

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
