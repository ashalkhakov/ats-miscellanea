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

// BIH implementation written by Shalkhakov Artyom
// in the time span of 3th to 8th of Jan, 2011.
// Untested, left for future reference.
// Lessons learnt:
// - start with small, don't try to do everything at once
// - the BIH paper is way too imprecise from the perspective
//   of an implementor
// - typechecker can be very picky, impacting your productivity
//   in an adverse manner. theorem proving is not quite the same
//   as programming; when programming, our goal is producing
//   a program, and theorem proving can become merely a digression
// - the more invariants you enforce through static type
//   checking, the more programs are ruled out by the typechecker
//   that you would consider correct on an intuitive level.
//   striking a balance here seems more like an art.

staload _ = "prelude/DATS/list_vt.dats" // for [list_vt_free]
staload _ = "prelude/DATS/array.dats"   // for BIH

(* ****** ****** *)

staload "vec.sats"
staload "geom.sats"
staload "scene.sats"

(* ****** ****** *)

staload _ = "vec.dats"
staload _ = "geom.dats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynloading at runtime

(* ****** ****** *)

(* the BIH paper sweeps technicalities under the rug. I will list here
** the thoughts I have after reading it.
**
** the construction algorithm has the following pre and post
** conditions:
** in: list of objects, where an object is (id, bbox)
**     and a bbox that tightly confines all of them
** out: bih structure
**
** the bih structure can be defined inductively thus:
** - base case (leaf node): an [id] for an object from the input list
** - inductive case (inner node):
**   - axis (X, Y, Z)
**   - min and max
**   - left and right BIH nodes
**   side conditions:
**   - left node is entirely to the left of [min]
**   - right node is entirely to the right of [max]
** an axis in the inductive case determines a vector:
** (1, 0, 0) for X, (0, 1, 0) for Y, (0, 0, 1) for Z
** [min] and [max] are two real numbers which, together with the axis
** vector give rise to two half-planes:
** ((-1, 0, 0), min) and ((1, 0, 0), max)
**
** to construct the bih, we proceed in a top-down fashion,
** dividing the input list in two at each iteration.
** the key invariant is that bbox tightly confines the input
** list.
** - base case, input list contains a single node (or a number of nodes
**   that we deem inefficient to divide): we move input list nodes to leaves
** - inductive case, input list is not empty:
**   - pick an axis and a "pivot" value along it
**     (very much like quicksort!)
**   - divide the input list into two:
**     - let L be the list where all nodes are to the left of pivot
**       and Lv be the "rightmost" corner of all these objects
**     - let R be the list where all nodes are to the right of pivot
**       and Rv be the "leftmost" corner of all these objects
**   - recur with both lists to construct children:
**     - L and R need their bboxes adjusted in accordance with Lv, Rv
**   - done, actually :)
**
** an AABB is defined as (min:vec3, max:vec3), where min <= max, ordering
** is defined thus: a <= b iff a.x <= b.x ^ a.y <= b.y and a.z <= b.z
**
** how do you know that an AABB is "to the left" or "to the right"
** of a plane? or is it straddling the plane?
** if we restrict ourselves to consider only axis-aligned planes (a plane
** being normal vector as discussed previously, and distance along it), then:
** - for axis X we have: to the left if b.x < dist, to the right if b.x > dist
** - and similarly for other axes
**
** let a be axis, p be pivot, min and max be bbox dimensions along a, min < max,
** and min < L, max > L.
** we move the bbox to the list L if (min+max)/2 < L, to the list R otherwise.
** also, we do not sort *objects*, only references to them!
**
** "rightmost" (resp. "leftmost") object within a list of objects
** is the one which has the greatest "max" component of bounding box projected
** onto axis in question. for example, given a list of 1D AABBs:
** [(0,1), (0.5,1.3), (1.2,1.4)] the rightmost object is #3, since
** it's max component (second component of min-max tuple) is the greatest one
**
** okay, how do you trace rays against this structure?
** we are trying to answer a *range query* here. a range for our
** purposes is a ray in conjunction with (min, max), min < max.
** (when tracing primary rays, min is our near plane distance)
**
** in: ray segment (range as discussed above) and bih
** out: boolean indicating "hit", hit point
** we proceed by induction on the bih structure.
** base case (leaf node): find the nearest intersection among objects
** inductive case (inner node): let L and R denote left and right subtrees, resp.
**   we proceed by cases on axis:
**   - X:
**     - left child only, right child only, left then right, right then left
**   - others are similar
*)

(*
Tue Jan 4, 8PM-9.30PM:

haskell quicksort for reference:

qsort [] = []
qsort (x:xs) = qsort (filter (<= x) xs) ++ x ++ qsort (filter (> x) xs)

inductive step of BIH construction is analogous to this.

we have a predicate "X to the left of pivot plane".

we mutate the input array in-place such that all elements
that are to the left of pivot plane occupy first half
of an array (the other half being occupied by elements that
are to the right of pivot plane).

we also keep track of leftmost/rightmost objects
as we move them to the left/right lists.
given a list of objects and a pivot, we perform the following
for each object:
- initialize L and R (candidate planes) to BIG_VALUE and -BIG_VALUE, resp.
- classify object against pivot
- if to the left of pivot:
    move to the left list
    if object.max > L then L := object.max
  if to the right of pivot:
    move to the right list
    if object.min < R then R := object.min
L is the rightmost dimension of objects in left list
R is the leftmost dimension of objects in right list

how do you swap elements hmmm? keep two subarrays:
- one grows from left to right
- another grows from right to left
initially, both are empty, but as you go comparing
and swapping things, they grow until meeting somewhere
in the middle.
*)

(* Jan 5 12:18
how much nodes do we need?
*)

(* ****** ****** *)

// axis-aligned plane
typedef plane = @{ax= axis3, dist= float}
(*
fun vec_of_axis .< >. (a: axis0):<> vec3 = case+ a of
  | Ax () => vec_make (1.0f, 0.0f, 0.0f)
  | Ay () => vec_make (0.0f, 1.0f, 0.0f)
  | Az () => vec_make (0.0f, 0.0f, 1.0f)
  | Anx () => vec_make (~1.0f, 0.0f, 0.0f)
  | Any () => vec_make (0.0f, ~1.0f, 0.0f)
  | Anz () => vec_make (0.0f, 0.0f, ~1.0f)
datatype inter =
  // no intersection between plane and ray segment
  | left | right
  // ray segment goes from left to right or vice versa
  | left2right | right2left

fn vec_axis_repl (v: vec3, a: axis3, f: float):<> vec3 =
  case+ a of
  | Ax () => vec_make (f, v.y, v.z)
  | Ay () => vec_make (v.x, f, v.z)
  | Az () => vec_make (v.x, v.y, f)

// project arbitrary point [t] along [r] onto [a]
fn proj_ray_axis (a: sizeLt 3, r: ray, t: float):<> float =
 (ray_origin r)[a] + (ray_direction r)[a] * t
*)

// classify ray segment against plane
// (this type of test is the core of kd-tree ray intersection
// algorithm: inner node splitting plane is used to classify
// ray segment, depending on the result of the test we visit
// the left or the right children first; if ray goes from left
// to right and there is intersection at the left child we stop,
// as there can be no more intersections -- this is guaranteed
// by the fact that all kd-tree volumes are pairwise disjoint
// in a given tree)
(*
fun ray_segment_plane_test .< >. (
    p: plane, r: ray, t0: float, t1: float
  ):<> inter = let
  // is point in front of plane? (specialized to axis-aligned planes)
  fn frnt (d: float, t: float):<> bool = t - d >= 1e-6f
  val d = p.dist
in
  // classify points (r,t0) and (r,t1) projected onto plane axis
  case+ (frnt (d, proj_ray_axis (p.ax, r, t0)), frnt (d, proj_ray_axis (p.ax, r, t1))) of
  | (false, false) => left
  | (false, true) => left2right
  | (true, false) => right2left
  | (true, true) => right
end *)

(*
** when using BVHs (and generally other structures that allow
** overlapping volume elements), we can't stop search at first
** intersection.
** let L and R denote two distances along axis.
** if we have an intersection at L' < L (along axis), then:
** - if L < R, we can ignore right subtree
** - otherwise, we'll have to check the right subtree as well
**   (the two volume elements overlap)
*)
(*
castfn axis_of_int .< >. {n:nat| n < 6}
  (x: int n):<> AXIS n = case+ x of
  | 0 => Ax | 1 => Ay | 2 => Az
  | 3 => Anx | 4 => Any | 5 => Anz
*)
// two axis-aligned parallel planes
typedef appln = @{ax= axis3, d0= float, d1= float}
// two planes: (~ax_to_vec ax, d0) and (ax_to_vec ax, d1)
// [d0,d1] is empty space if d0 <= d1

fn split_box_appln (bx: bbox, p: appln):<> (bbox, bbox) = let
  val mx = bbox_max bx
  val mx = mx[p.ax] := p.d0
  val mn = bbox_min bx
  val mn = mn[p.ax] := p.d1
in
  (bbox_make (bbox_min bx, mx), bbox_make (mn, bbox_max bx))
end

// this is the root of all evil
// rewrite everything to use indices instead
// viewtypedef ref (a:viewt@ype) = a // [l:addr] (a @ l | ptr l)

// bih_vt (a, l, n, h) represents a BIH such that
// the following holds:
// - the start of leaves array is at l
// - the size of leaves array is n
// - h is the overall "size" of the tree
// leaves array is contigous, we enforce this
// invariant by construction.
dataview bih_v (
    a:viewt@ype+
  , int  // total count of elements in leaves
  , addr // start of leaves array
  , addr // self
  , int  // size of tree
  ) =
  | {n:nat} {l1,l2:addr}
    bih_v_leaf (a, n, l1, l2, 1) of
      (array_v (a, n, l1) | ptr l1, size_t n) @ l2
  | {n1,n2:nat} {l1,l2,l3,ls:addr} {ofs:nat} {h1,h2:nat}
    bih_v_node (a, n1+n2, l1, ls, h1+h2+1) of
      ( MUL (n1, sizeof (a), ofs)
      , @{apl= appln, lft= ptr l1, rgt= ptr l2} @ ls
      , bih_v (a, n1, l1, l2, h1)
      , bih_v (a, n2, l1+ofs, l3, h2)
      )

dataviewtype bih_vt (
    k:int // size of array holding primitives
  , int   // total count of elements in leaves
  , addr  // start of leaves array
  , int   // size of tree (a termination argument)
  ) =
  | {n:nat} {l:addr}
    bih_vt_leaf (k, n, l, 1) of
      (array_v (sizeLt k, n, l) | ptr l, size_t n)
  | {n1,n2:nat} {l:addr} {ofs:nat} {h1,h2:nat}
    bih_vt_node (k, n1+n2, l, h1+h2+1) of
      ( MUL (n1, sizeof size_t, ofs)
      | appln
      , (*lft*)bih_vt (k, n1, l, h1), (*rgt*)bih_vt (k, n2, l+ofs, h2)
      )

viewtypedef bih0_vt (k:int, n:int, l:addr) =
  [h:int] bih_vt (k, n, l, h)

// relationship between box and plane
// datatype box_plane = BPlft | BPrgt

// classification function: takes an object
// and a plane, returns true if object is in front
// of plane, false otherwise
// typedef cls_fun (a:viewt@ype) =
//  (ref a, plane) -<fun> bool

// TODO: compute bounds of face projected onto axis
extern fun bbox_of_face_along_axis (f: face, ax: axis3):<> (float, float)

(* Jan 11. finding nearest intersection between AABB binary tree
** and a ray.
**
** AABB tree is simply:
** - leaf: primitive
** - node: bbox, two children AABB trees, split_axis (0,1,2)
** key invariant is that bbox of an AABB tree node encloses
** both children.
**
** nearest intersection test involves:
** - an AABB tree in question
** - a ray
** and yields:
** - hit (boolean, true if something has been intersected by a ray)
** - distance (distance to nearest intersection)
**
** now, we proceed by induction on the tree.
** state involved: hit, distance
** initially: hit = false, distance = infinity.
** by cases on AABB tree:
** - base case -- just intersect:
**   thit = primitive_ray_test (prim, ray, tdist)
**   if thit then:
**     dist = min (dist, tdist)
**     hit = true
** - inductive case -- find nearest intersection among children:
**   if ray_box_test (bbox, ray) then: // does it intersect our node?
**     if ray.origin[split_axis] - ray.direction[split_axis] * dist > 0.0f then:
**       thit1 = test (left_child, ray, tdist1)
**       thit2 = test (right_child, ray, tdist2)
**     else:
**       thit1 = test (right_child, ray, tdist1)
**       thit2 = test (left_child, ray, tdist2)
**     if thit1 then: // pick nearest of two
**       dist = min (dist, tdist1)
**       hit = true
**     if thit2 then:
**       dist = min (dist, tdist2)
**       hit = true
** and that's all, folks!
** now, how do we store all primitives?
** - as viewtypes (boxed)
**   single reference all around...
**   munging with takeout ...
** - as indices?
*)

// FIXME: how much memory do we need for N objects?
// compute: N -> M (for N objects need M nodes)
// base case: N is sufficiently small that we stuff objects in one leaf
// inductive case: N is greater than some cutoff value, so
//   N' = N/2 (input is roughly divided by two since our tree is binary)
//   and we recur with N' and N'
(*
cutoff = 2

compute :: Int -> Int
compute n | n <= cutoff = 1
          | otherwise   = compute a + compute b where
                            a = div n 2
                            b = n - a

proposition: compute n < 2*n
base case: n <= cutoff, we have 1, which is less than n*2
inductive case:
  a = n `div` 2, b = n - a,
  compute a <= a*2, compute b <= b*2 (ind. hypot.)
  is a*2+b*2 <= n*2?
     (a+b)*2 <= n*2 (LHS: distributivity of mult.)
     (a+b) <= n (divide both sides by 2
*)

// TODO: returns true if face is in front of plane
extern fun face_plane_classify (f: face, pl: plane):<> bool

// this function can be specialized
// returns true if object is in front of plane
(*
fun{a:viewt@ype} classify .< >. {l:addr} (
    pf_at: !a @ l
  | r: ptr l, pl: plane, bnd: bnd_fun a
  ):<> bool = let
    val (min, max) = bnd (pf_at | r, pl.ax)
  in
    (min + max)*0.5f - pl.dist >= 1e-6f
  end*)

// Jan 6: finally works
fun bih_initialize {k,n:pos} {l1,l2:addr} (
    pf_arr: array_v (sizeLt k, n, l1)
  , pf_prm: !array_v (face, k, l2)
  | p_arr: ptr l1, sz: size_t n
  , p_prm: ptr l2, psz: size_t k
  , bx: bbox
  ):<!ntm> [h:nat] bih_vt (k, n, l1, h) = let
  #define CUTOFF 1

  // choose a candidate plane
  fn mk_plane (bx: bbox):<> plane = let
    // pick longest axis
    fn amax (a: plane, b: plane):<> plane =
      if a.dist > b.dist then a else b
    val x = ((bbox_max bx).x - (bbox_min bx).x) / 2.0f
    val y = ((bbox_max bx).y - (bbox_min bx).y) / 2.0f
    val z = ((bbox_max bx).z - (bbox_min bx).z) / 2.0f
    fn pln (a: axis3, d: float):<> plane = @{ax= a, dist= d}
  in
    amax (pln (Ax, x), amax (pln (Ay, y), pln (Az, z)))
  end // end of [mk_plane]

  // sort array (classify with respect to the splitting plane)
  fn arrsort {l1,l2:addr} {k,n:pos} (
      pf_arr: array_v (sizeLt k, n, l1)
    , pf_prm: !array_v (face, k, l2)
    | p_arr: ptr l1, n: size_t n
    , p_prm: ptr l2, k: size_t k
    , pl: plane
    , lft: &float? >> float, rgt: &float? >> float
    ):<> [i:nat | i < n] [ofs:nat] (
      MUL (i, sizeof size_t, ofs)
    , array_v (sizeLt k, i, l1), array_v (sizeLt k, n-i, l1+ofs)
    | size_t i, ptr (l1+ofs)
    ) = let
    // three arrays: A, B, C
    // A is for elements that <= pivot
    // C is for elements that > pivot
    // B is for yet unexplored elements
    // initially, we have that A and C are empty
    // exploring an element e of B yields:
    // e <= pivot then we leave e as-is ("append" to A)
    // e > pivot then we exchange e with tail of B ("prepend" to C)
    // thus at each iteration the size of B is decremented by one,
    // and we stop when it reaches zero
    fun loop {j:nat | j < n} {i:nat | i <= j} .<j-i>. (
        pf_a: !array_v (sizeLt k, n, l1)
      , pf_p: !array_v (face, k, l2)
      | b: ptr l1, sz: size_t n
      , p: ptr l2, k: size_t k
      , i: size_t i, j: size_t j
      , pl: plane, lft: &float, rgt: &float
      ):<> sizeLt n = if i = j then j else let
          val (min, max) = bbox_of_face_along_axis (!p.[!b.[i]], pl.ax)
        in
          if ~face_plane_classify (!p.[!b.[i]], pl) then let
            val () = if min < rgt then rgt := min // FIXME: epsilon!
            val () = array_ptr_exch<sizeLt k> (!b, i, j)
          in
            loop (pf_a, pf_p | b, sz, p, k, i, j-1, pl, lft, rgt)
          end else let
            val () = if max > lft then lft := max // FIXME: epsilon!
          in
            loop (pf_a, pf_p | b, sz, p, k, i+1, j, pl, lft, rgt)
          end // end of [if]
        end // end of [let]
    val () = lft := 16384.0f and () = rgt := ~16384.0f // FIXME: hack!
    val j = loop (pf_arr, pf_prm | p_arr, n, p_prm, k, 0, n-1, pl, lft, rgt)
    val (pf_mul, pf1_arr, pf2_arr | p_arr') =
      array_ptr_split (pf_arr | p_arr, j)
  in
    (pf_mul, pf1_arr, pf2_arr | j, p_arr')
  end // end of [sort_arr]

  // FIXME: does this function terminate?
  fun mk_bih {k:pos} {n:nat} {l,l',l'':addr} (
      pf_a: array_v (sizeLt k, n, l)
    , pf_b: !bih0_vt (k, n, l)? @ l' >> bih_vt (k, n, l, h) @ l'
    , pf_p: !array_v (face, k, l'')
    | p_a: ptr l, sz: size_t n
    , p_f: ptr l'', k: size_t k
    , bx: bbox, res: ptr l'
    ):<!ntm> #[h:nat] void =
    if sz <= CUTOFF then begin
      !res := bih_vt_leaf (pf_a | p_a, sz)
    end else let
      // choose an axis and a splitting plane
      val pln = mk_plane bx
      // categorize input list into two non-empty lists
      var min: float and max: float
      // FIXME: what if one of the lists is empty?
      val [i:int] [ofs:int] (pf_mul, pf1_arr, pf2_arr | sz1, p_b) =
        arrsort (pf_a, pf_p | p_a, sz, p_f, k, pln, min, max)
      val ap = @{ax= pln.ax, d0= min, d1= max}
      val (bx1, bx2) = split_box_appln (bx, ap)
      val () = !res := bih_vt_node {k} {i,n-i} {l} {ofs} {0,0} (pf_mul | ap, ?, ?)
      val+ bih_vt_node (_ | _, !lft, !rgt) = !res
      // FIXME: what to do if sz1 = 0? (and generally, when one list is empty)
      // can we make a special terminator node? should we continue in some other way?
      // (I don't see any way to prove termination of this function if
      // input array isn't halved at each step)
      val () = mk_bih (pf1_arr, view@ (!lft), pf_p | p_a, sz1, p_f, k, bx1, lft)
      val () = mk_bih (pf2_arr, view@ (!rgt), pf_p | p_b, sz - sz1, p_f, k, bx2, rgt)
    in fold@ (!res) end // end of [mk_bih]
  var res: bih0_vt (k, n, l1)?
  val () = mk_bih (pf_arr, view@ res, pf_prm | p_arr, sz, p_prm, psz, bx, &res)
in
  res
end

// free the BIH
fn bih_uninitialize {l:addr} {k,n:pos} {h:nat} (
    bih: bih_vt (k, n, l, h)
  , p_arr: &ptr? >> ptr l
  , sz: &size_t? >> size_t n
  ):<> (array_v (sizeLt k, n, l) | void) = let
  fun loop {h:nat} {n:nat} {l:addr} .<h>. (bih: bih_vt (k, n, l, h))
    :<> (array_v (sizeLt k, n, l) | ptr l, size_t n) = case+ bih of
    | ~bih_vt_leaf (pfa | b, n) => (pfa | b, n)
    | ~bih_vt_node (pf_mul | _, lc, rc) => let
        val (pf1_arr | b1, n1) = loop lc
        val (pf2_arr | b2, n2) = loop rc
      in
        (array_v_unsplit {sizeLt k} (pf_mul, pf1_arr, pf2_arr) | b1, n1+n2)
      end // end of [loop]
  val (pf_arr | p, n) = loop bih
  val () = p_arr := p;
  val () = sz := n
in
  (pf_arr | ())
end

// ray segment (parameter is unknown, but must be within min/max)
typedef rayseg = @{
    r= ray
  , n= float // near
  , f= float // far
  , np= vec3 // ray_point (r, n)
  , fp= vec3 // ray_point (r, f)
  , bx= bbox // 
}

fn mk_rayseg (r: ray, n: float, f: float):<> rayseg = let
  val np = ray_point (r, n)
  val fp = ray_point (r, f)
in @{
    r= r, n= n, f= f, np= np, fp= fp
  , bx= bbox_make (vec_min (np, fp), vec_max (np, fp))
  }
end

fn face_ray_test (f: face, rs: &rayseg):<> bool =
  ray_face_test_hit (rs.r, f)

// given rs with (t0, t1) being two endpoints projected onto axis,
// a= min(t0,t1) and b= max(t0,t1) gives us a proper ordering,
// whereas sign(t0-t1) (0 iff t0 <= t1, 1 iff t0 > t1) gives us direction
// to test if (a,b) is to the left of L: b <= L
// to test if (a,b) is to the right of R: a >= R
// if b > L and a < R ray misses both planes
//
// a <= L && b >= R: BOTH
//   (t0 <= t1: LEFT_TO_RIGHT, otherwise RIGHT_TO_LEFT)
// a <= L && b < R: LEFT
// a > L && b >= R: RIGHT
// a > L && b < R: MISS
//
// Jan 6: 22.08-22.15 (function below, with remark on bits)
//
// fun classify (ax: axis3, L: float, R: float, r: ray, mindist: float, maxdist: float) = let
//   val t0 = proj (ax, r, mindist)
//   val t1 = proj (ax, r, maxdist)
//   val a = min (t0, t1)
//   val b = max (t0, t1)
// in
//   // hmmm: a <= L, b >= R give what we need also
//   // we can view these as bits: t0 <= t1, a <= L, b >= R
//   // 111 is for LEFT_TO_RIGHT, BOTH
//   // 011 is for RIGHT_TO_LEFT, BOTH etc.
//   if a <= L then
//     if b >= R then if (t0 <= t1) then LEFT_TO_RIGHT else RIGHT_TO_LEFT
//     else LEFT
//   else
//     if b >= R then RIGHT
//     else MISS
// end

(* Jan 6
18.00-19.15: ray intersection algorithm in more detail.

in: ray, mindist, maxdist (mindist <= maxdist -- always!)
  initially, mindist=maxdist=infinity
state: hp -- primitive hit (mindist -- distance to this prim)
out: mindist, primitive ID

base case: p -- primitive
  d = intersect (ray, p)
  if d > maxdist then (mindist, hp) // TODO: quick culling here
  else if d < mindist then (d, p) else (mindist, hp)

inductive case (lft is left child, rgt is right child, L is left clip plane, R is right clip plane):
    to determine that ray (o,d) segment (min,max) can intersect an axis-aligned plane (ax,dist):
    - project min and max onto axis:
      o+min*d (ray equation)
      (o+min*d) dot ax (dot product gives projection)
      o dot ax + min*d dot ax (distrib. of dot over addition)
    - compare min and max against dist
    now, how to find (ax,dist) point on ray (o,d) as a parameter?
    --bullshit below this point
    we have p = ax*dist (point on axis), q(t) = o+d*t (point on ray)
    ax*dist = o+d*t
    o+d*t = ax*dist (symm.)
    o/d + t = ax*dist/d (principle of multiplication)
    t = ax*dist/d - o/d (principle of addition)
    t = (ax*dist - o)*d (distributivity of division)
  Jan 6, 22:00 -- incorporated projection/clipping, need to test this stuff on real data!
  case classify (axis, L, R, ray, mindist, maxdist) of
  | MISS () => (mindist, hp)
  | LEFT () => recur (ray, lft, hp, mindist, clipmin (axis, L, ray, maxdist))
  | RIGHT () => recur (ray, rgt, hp, mindist, clipmax (axis, R, ray, maxdist))
  | BOTH (dir) => begin
      case dir of
      | LEFT_TO_RIGHT () => let
          // test left child first, bound search by left split plane
          val (mindist,hp) = recur (ray, lft, hp, mindist, clipmin (axis, L, ray, maxdist))
        in
          // children overlap and intersection is further than R (thus might intersect right child)
          // bound new search by (mindist, R)
          if L > R && proj(axis,ray,mindist) > R then recur (ray, rgt, hp, mindist, clipmin (axis, R, ray, mindist))
          else (mindist,hp)
        end
      | RIGHT_TO_LEFT () => let
          // test right child first, bound search by right split plane
          val (mindist,hp) = recur (ray, rgt, hp, mindist, clipmax (axis, R, ray, maxdist))
        in
          // children overlap and intersection is further than L (thus might intersect left child)
          // bound new search by (mindist, L)
          if L > R && proj(axis,ray,mindist) < L then recur (ray, lft, hp, mindist, clipmax (axis, L, ray, mindist))
          else (mindist,hp)
        end
    end

fun horz_min (v: vec3): float = min (v.x, min (v.y, v.z))
fun horz_max (v: vec3): float = max (v.x, max (v.y, v.z))
fun vec_max (a: vec3, b: vec3): vec3 = vec_make (max (a.x, b.x), max (a.y, b.y), max (a.z, b.z))
fun vec_min (a: vec3, b: vec3): vec3 = vec_make (min (a.x, b.x), min (a.y, b.y), min (a.z, b.z))

fun intersect_ray_box (b: bbox, r: ray, near: &float, far: &float): bool = let
  val l1 = (bbox_min b - ray_origin r) / ray_direction r
  val l2 = (bbox_max b - ray_origin r) / ray_direction r
in
  far := min (horz_min (vec_max (l1, l2)), far);
  near := max (horz_max (vec_min (l1, l2)), near);
  far >= near && far >= 0.0f
end

FIXME: how to clip a point on line by a plane?
in 2D: line is given by o+t*dir, plane by another line, ax*dist.
the task is to find t, (o+t*dir)dot ax = dist
(in words, length of projection of line onto ax is dist)
given dist, compute t.
p(t) = o+t*dir
p(t) dot ax = dist
(o+t*dir)dot ax = dist
o dot ax + t*dir dot ax = dist
t*dir dot ax = dist - o dot ax
t = (dist - o dot ax)/(dir dot ax)
check: dist=4, ax=(0,1), o=(0,0), dir=(0.5,0.5)
(4 - 0)/(0.5) -> 8

((0,0) + 8*(0.5,0.5)) dot (1,0) = 4
(4,4) dot (1,0) = 4

seems to work both ways, what is (0.5,0.5) when graphed?

clip(ax,o,dir,dist) = (dist - o dot ax)/(dir dot ax)
*)

fn clip (ax: axis3, f: float, r: ray, t: float):<> float = let
  val x = vec3_get_elt_at__intsz (ray_direction r, ax)
in
  // see if ray and axis are colinear
  if x > 1e-6f then (min (f, t) - vec3_get_elt_at__intsz (ray_origin r, ax)) / x
  else t
end

(* trace a ray against bih *)
(*
fn bih_ray_test {n:nat} {l:addr} (
    bih: !bih0_vt (n, l), r: ray, res: &hit0? >> opt (hit n, b)
  ):<> #[b:bool] bool b = let
  val rs = @{r= r, min= 0.0f, max= 16384.0f}
  extern fun test_leaf {n:nat} {l:addr} (
      pf_arr: array_v (sphere, n, l)
    | p_arr: ptr l, sz: size_t n, rs: rayseg, res: &hit0? >> opt (hit n, b)
    ):<> #[b:bool] bool b
  fun loop {n:nat} {l:addr} (
      bih: !bih0_vt (n, l), rs: rayseg, t: &hit0? >> opt (hit n, b)
    ):<> #[b:bool] bool b = case+ bih of
    | bih_vt_leaf (pf_arr | p_arr, sz) => test_leaf (pf_arr | p_arr, sz, rs, t)
    | bih_vt_node (_ | p, l, r) => let
        val w = way of rs wrt to left plane of p
      in
        case+ w of
        | front () => let // intersect with left
            val r = loop (l, rs, t) 
          in (**) end
        | back () => let  // intersect with right
            val r = loop (r, rs, t)
          in (**) end
        | cross () => let
      end
in
  loop (bih, rs, res)
end *)

// Jan 9: another attempt at tracing rays through BIH
// Jan 12: will return [k] if there is no intersection,
// otherwise index of primitive

// FIXME: want to make sure that result falls within [0,k]
// (result == k iff there is no intersection)
fn trace_bih {k,n,h:nat} {l1,l2:addr} (
    pf_p: !array_v (face, k, l2)
  | bih: !bih_vt (k, n, l1, h), r: ray
  , p_f: ptr l2, k: size_t k
  ):<> size_t = let
  fun loop {n,h:nat} {l1,l2:addr} .<h>. (
      pf_p: !array_v (face, k, l2)
    | bih: !bih_vt (k, n, l1, h)
    , p_f: ptr l2, k: size_t k
    , rs: &rayseg
    , ht: &size_t
    ):<> void = case+ bih of
    | bih_vt_leaf (!pf_arr | !p_arr, sz) => let
         // test against all objects in a leaf
         // there is only brute force here
         fun loop {l:addr} {n:nat} .<n>. (
             pf_arr: !array_v (sizeLt k, n, l)
           , pf_p: !array_v (face, k, l2)
           | p_arr: ptr l, n: size_t n
           , p_f: ptr l2
           , ht: &size_t, rs: rayseg
           ):<> void = if n > 0 then let
             prval (pf_at, pf_rst) = array_v_uncons {sizeLt k} (pf_arr)
             val res = ray_face_test_hit (rs.r, !p_f.[!p_arr])
             val () = if res then begin
                 // TODO: check intersection distance
                 ht := !p_arr
               end
             val () = loop (pf_rst, pf_p | p_arr+sizeof<size_t>, pred n, p_f, ht, rs)
             prval () = pf_arr := array_v_cons (pf_at, pf_rst)
           in
             (*empty*)
           end else let
             prval () = array_v_unnil (pf_arr)
             prval () = pf_arr := array_v_nil ()
           in (*empty*) end // end of [loop]
         val () = loop (!pf_arr, pf_p | !p_arr, sz, p_f, ht, rs)
         val () = fold@ (bih)
      in () end // end of [let .. in .. end]
    | bih_vt_node (_ | p, !l, !r) => let
        symintr .#
        infixl (+) .#
        overload .# with vec3_get_elt_at__intsz
      in
        if rs.np .# p.ax <= rs.fp .# p.ax then let
          // ray goes from left to right
          val () = if bbox_min rs.bx .# p.ax <= p.d0 then loop (pf_p | !l, p_f, k, rs, ht)
          val () = if bbox_max rs.bx .# p.ax >= p.d1 then loop (pf_p | !r, p_f, k, rs, ht)
        in (*empty*) end else begin
          // ray goes from right to left
          if bbox_max rs.bx .# p.ax >= p.d1 then loop (pf_p | !r, p_f, k, rs, ht);
          if bbox_min rs.bx .# p.ax <= p.d0 then loop (pf_p | !l, p_f, k, rs, ht)
        end;
        fold@ (bih)
      end // end of [loop]
  var rs = mk_rayseg (r, 0.0f, 16384.0f) // FIXME: 16384.0f is a hack
  var ht = k
  val () = loop (pf_p | bih, p_f, k, rs, ht)
in
  ht
end
