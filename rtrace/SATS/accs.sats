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

(* an abstract datatype for an acceleration structure *)

staload "SATS/geom.sats"

absviewtype accs_vt (n:int)

// construct an acceleration
// structure given a list of primitives
fun accs_initialize {n:pos} (p: &(@[sphere][n]), n: size_t n): accs_vt n

fun accs_uninitialize {n:nat} (acs: accs_vt n):<> void

// perform a ray-accs intersection test.
// if the result is [true], then [t>=0] is the ray
// parameter for the nearest intersection point
// and [s] is the id of the primitive
fun ray_accs_test {n:pos} (
    acs: !accs_vt n, p: &(@[sphere][n])
  , r: ray, t: &float? >> opt (float, b), s: &size_t? >> opt (sizeLt n, b)
  ):<> #[b:bool] bool b
