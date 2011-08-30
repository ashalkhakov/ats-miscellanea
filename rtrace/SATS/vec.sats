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

(* vector operations *)

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

typedef vec (a:t@ype, n:int) = @[a][n]
typedef vec3_t (a:t@ype) = vec (a, 3)
fun{a:t@ype} add_flt_flt (x: a, y: a):<> a
fun{a:t@ype} add_vec_vec {n:nat} (x: vec (a, n), y: vec (a, n)):<> vec (a, n)

typedef vec2 = @{x= float, y= float}

fun{} vec2_make (x: float, y: float):<> vec2

fun{} vec2_get_elt_at (x: vec2, i: sizeLt 2):<> float
overload [] with vec2_get_elt_at

fun{} vec2_set_elt_at (x: vec2, i: sizeLt 2, a: float):<> vec2
overload [] with vec2_set_elt_at

// these are present only for convenience

fun{} vec2_set_elt_at__intsz {i:nat | i < 2} (x: vec2, i: int i, a: float):<> vec2
overload [] with vec2_set_elt_at__intsz

fun{} vec2_get_elt_at__intsz {i:nat | i < 2} (x: vec2, i: int i):<> float
overload [] with vec2_get_elt_at__intsz

typedef vec3 = @{x= float, y= float, z= float}

fun{} vec3_get_elt_at (x: vec3, i: sizeLt 3):<> float
overload [] with vec3_get_elt_at

fun{} vec3_set_elt_at (x: vec3, i: sizeLt 3, a: float):<> vec3
overload [] with vec3_set_elt_at

// these are present only for convenience
fun{} vec3_get_elt_at__intsz {i:nat | i < 3} (x: vec3, i: int i):<> float
overload [] with vec3_get_elt_at__intsz

fun{} vec3_set_elt_at__intsz {i:nat | i < 3} (x: vec3, i: int i, a: float):<> vec3
overload [] with vec3_set_elt_at__intsz

// ortho-normal basis: f(ront), r(ight), u(p)
typedef basis = @{f= vec3, r= vec3, u= vec3}
typedef rgb = @{r= float, g= float, b= float}

(* ****** ****** *)

typedef AXIS (n:int) = int n
#define Ax 0
#define Ay 1
#define Az 2

typedef axis0 = [n:int] AXIS n
typedef axis2 = [n:int | n >= 0; n < 2] AXIS n
typedef axis3 = [n:int | n >= 0; n < 3] AXIS n

(* ****** ****** *)

// rigid body transformation
typedef xform= @{o= vec3, a= basis}

(* ****** ****** *)
(* basic vector operations *)

fun{} vec_make (x: float, y: float, z: float):<> vec3

fun{} vec_add (a: vec3, b: vec3):<> vec3
overload + with vec_add
// end of [vec_sub]

fun{} vec_sub (a: vec3, b: vec3):<> vec3
overload - with vec_sub
// end of [vec_sub]

fun{} vec_dot (a: vec3, b: vec3):<> float
overload * with vec_dot
// end of [vec_dot]

fun{} vec_scale_r (a: vec3, x: float):<> vec3
overload * with vec_scale_r
// end of [vec_scale_r]

fun{} vec_scale_l (x: float, a: vec3):<> vec3
overload * with vec_scale_l
// end of [vec_scale_l]

fun{} vec_div (a: vec3, b: vec3):<> vec3
overload / with vec_div
// end of [vec_div]

fun{} vec_div_r (a: vec3, x: float):<> vec3
overload / with vec_div_r
// end of [vec_div_r]

// length (magnitude) of vector
fun{} vec_len (a: vec3):<> float

// normalize vector
fun{} vec_norm (a: vec3):<> vec3

// rotate vector
fun{} vec_rotate (a: vec3, cf: basis):<> vec3

// cross product
fun{} vec_cross (a: vec3, b: vec3):<> vec3

// component-wise min/max
fun{} vec_min (a: vec3, b: vec3):<> vec3
overload min with vec_min
fun{} vec_max (a: vec3, b: vec3):<> vec3
overload max with vec_max

// projection of vertex on axis-aligned direction vector
fun{} vec_axis (v: vec3, a: axis2):<> float

(* ****** ****** *)

fun{} xform_identity ():<> xform
