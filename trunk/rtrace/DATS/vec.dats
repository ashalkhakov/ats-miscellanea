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

(* ****** ***** *)

implement{} vec2_make (x, y) = @{x= x, y= y}

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

fun test (): void = let
  val a = vec_make (0.0f, 1.0f, 2.0f)
  val a = a[size1_of_int1 0] := 1.0f
//  val a = a
in (*empty*) end

(*
implement{} vec_axis (v, a) = case+ a of
  | Ax () => v.x
  | Ay () => v.y
  | Az () => v.z
*)

(* ****** ******* *)

implement{} xform_identity () = @{
    o= vec_make (0.0f, 0.0f, 0.0f)
  , a= @{
      f= vec_make (1.0f, 0.0f, 0.0f)
    , r= vec_make (0.0f, 1.0f, 0.0f)
    , u= vec_make (0.0f, 0.0f, 1.0f)
    }
  }