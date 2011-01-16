(*
** the problem that this module solves is as follows.
** given a scene description as input,
** provide efficient means of solving the following
** queries:
** - ray/scene intersection
**
** the way we achieve this is by building an acceleration
** structure, which sorts scene elements in some way.
**
** FIXME: "scene" is a misnomer; the module
** should be split in two: scene description
** and acceleration structure
**
** written by Artyom Shalkhakov on Dec 22, 2010
** acceleration structure implementation: Jan 3, 2011
*)

staload "SATS/vec.sats"
staload "SATS/geom.sats"

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at runtime

(* ****** ****** *)
// scene description

typedef material = @{
  spec= float  // specular reflection constant (k_s)
, diff= float  // diffuse reflection constant (k_d)
, amb= float   // ambient reflection constant (k_a)
, alpha= float // shininess factor
}

// two types of lights: directed and point.
// directed light is so far away from the scene that its rays are almost parallel,
// so we approximate it with a single direction vector. sun can be modelled
// by a directed light.
//
// point light is located somewhere within the scene; its rays are not parallel,
// so we approximate it with an origin point.
typedef light = @{
  O= vec3
, I= float
, C= rgb
// , spec= rgb
// , diff= rgb
}

// pin-hole camera: transformation, horizontal/vertical field of view,
// distance from origin to near view plane
typedef camera = @{xf= xform, fov= vec2, f= float}

(* ****** ****** *)

// FIXME: not very abstract, really
// how do we work around this?
absviewt@ype scene_vt ((*primitives*)int, (*lights*)int) = @{
  obj= ptr
, n_obj= size_t
, lgt= ptr
, bvh= ptr
}
// end of [scene_vt]

viewtypedef scene0_vt = [n,m:int] scene_vt (m, n)?

(* ****** ****** *)

fun mk_scene {n,m:pos} (
    obj: list_vt (sphere, n)
  , lgt: list_vt (light, m)
  , sc: &scene0_vt >> scene_vt (n, m)
  ): void
// end of [mk_scene]

fun ds_scene {n,m:pos} (
    sc: &scene_vt (n, m) >> scene0_vt
  ):<> void
// end of [ds_scene]

(* ****** ****** *)

typedef hit (n:int) = @{
  id= sizeLt n
, t= float // ray parameter
, p= vec3  // point of impact
, n= vec3  // surface normal at point of impact
}
typedef hit0 = @{id= size_t, t= float, p= vec3, n= vec3}?

(* ****** ****** *)

// find the nearest intersection of ray
// with the scene
fun intersect_ray {n,m:pos}
  (s: !scene_vt (n, m), r: ray, res: &hit0? >> opt (hit n, b))
  :<> #[b:bool] bool b
