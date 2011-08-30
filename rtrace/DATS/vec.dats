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

staload M = "libc/SATS/math.sats"

(* ****** ****** *)

staload "SATS/vec.sats"

(* ****** ***** *)

#define ATS_DYNLOADFLAG 0 // no dynloading at runtime

(* ****** ****** *)

(*
implement add_flt_flt<float> (x, y) = x + y
implement{a} add_vec_vec {n} (x, y) = $array (x.0 + y.0)

fun add_vec_vec (x: @[int][2], y: @[int][2]): @[int][2] =
  @[int](0, 1)
*)

(* ****** ***** *)

implement{} vec2_make (x, y) = @{x= x, y= y}

implement{} vec2_get_elt_at (a, i) =
  if i = 0 then a.x else a.y
// end of [vec2_get_elt_at]

implement{} vec2_set_elt_at (v, i, x) =
  if i = 0 then vec2_make (x, v.y) else vec2_make (v.x, x)
// end of [vec2_set_elt_at]

implement{} vec2_set_elt_at__intsz (v, i, x) =
  if i = 0 then vec2_make (x, v.y) else vec2_make (v.x, x)
// end of [vec2_set_elt_at__intsz]

implement{} vec2_get_elt_at__intsz (x, i) =
  if i = 0 then x.x else x.y
// end of [vec2_get_elt_at__intsz]

implement{} vec3_get_elt_at (v, i) =
  if i = 0 then v.x else if i = 1 then v.y else v.z
// end of [vec3_get_elt_at]

implement{} vec3_set_elt_at (v, i, x) =
  if i = 0 then vec_make (x, v.y, v.z)
  else if i = 1 then vec_make (v.x, x, v.z)
  else vec_make (v.x, v.y, x)
// end of [vec3_set_elt_at]

implement{} vec3_get_elt_at__intsz (v, i) =
  if i = 0 then v.x else if i = 1 then v.y else v.z
// end of [vec3_get_elt_at__intsz]

implement{} vec3_set_elt_at__intsz (v, i, x) =
  if i = 0 then vec_make (x, v.y, v.z)
  else if i = 1 then vec_make (v.x, x, v.z)
  else vec_make (v.x, v.y, x)
// end of [vec3_set_elt_at__intsz]

implement{} vec_make (x, y, z) = @{x= x, y= y, z= z}

implement{} vec_add (a, b) = @{x= a.x+b.x, y= a.y+b.y, z= a.z+b.z}

implement{} vec_sub (a, b) = @{x= a.x-b.x, y= a.y-b.y, z= a.z-b.z}

implement{} vec_dot (a, b) = a.x*b.x + a.y*b.y + a.z*b.z

implement{} vec_scale_r (a, f) = @{x= a.x*f, y= a.y*f, z= a.z*f}

implement{} vec_scale_l (f, a) = vec_scale_r (a, f)

implement{} vec_div (a, b) = @{x= a.x/b.x, y= a.y/b.y, z= a.z/b.z}

implement{} vec_div_r (a, f) = @{x= a.x/f, y= a.y/f, z= a.z/f}

implement{} vec_len (a) = $M.sqrtf (a * a)

implement{} vec_norm (a) = let
  val l = vec_len a
in
  if l < 1.0e-5f then @{x= 0.0f, y= 0.0f, z= 0.0f}
  else a * (1.0f / l)
end

implement{} vec_rotate (a, cf) = vec_make (a * cf.f, a * cf.r, a * cf.u)

implement{} vec_cross (a, b) = let
  val x = a.y*b.z - a.z*b.y
  val y = a.z*b.x - a.x*b.z
  val z = a.x*b.y - a.y*b.x
in
  vec_make (x, y, z)
end

implement{} vec_min (a, b) =
  vec_make (min (a.x, b.x), min (a.y, b.y), min (a.z, b.z))
implement{} vec_max (a, b) =
  vec_make (max (a.x, b.x), max (a.y, b.y), max (a.z, b.z))

(* ****** ******* *)

implement{} xform_identity () = @{
    o= vec_make (0.0f, 0.0f, 0.0f)
  , a= @{
      f= vec_make (1.0f, 0.0f, 0.0f)
    , r= vec_make (0.0f, 1.0f, 0.0f)
    , u= vec_make (0.0f, 0.0f, 1.0f)
    }
  }
