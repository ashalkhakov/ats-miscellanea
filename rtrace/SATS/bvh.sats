(* a simple BVH implementation
** written by Artyom Shalkhakov on Jan 15, 2011
*)
staload "SATS/geom.sats"

absviewtype BVH (n:int)

// construct a BVH given a list of primitives
fun bvh_initialize {n:pos} (p: &(@[sphere][n]), n: size_t n): BVH n

fun bvh_uninitialize {n:nat} (bvh: BVH n):<> void

// perform a ray-BVH intersection test.
// if the result is [true], then [t>=0] is the ray
// parameter for the nearest intersection point
// and [s] is the id of the primitive
fun ray_bvh_test {n:pos} (
    bvh: !BVH n, p: &(@[sphere][n])
  , r: ray, t: &float? >> opt (float, b), s: &size_t? >> opt (sizeLt n, b)
  ):<> #[b:bool] bool b
