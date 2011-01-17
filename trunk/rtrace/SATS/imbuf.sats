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

(* image buffer *)

(* ****** ****** *)

staload "libc/SATS/stdio.sats"

(* ****** ****** *)

staload "SATS/vec.sats"

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at runtime

(* ****** ****** *)

// our convention is that pixel at [(0,0)]
// is at the lower left corner of the image,
// and [x] goes right whereas [y] goes up

typedef imbuf_vt (w:int, h:int, l:addr) = @{
  w= size_t w
, h= size_t h
, b= ptr l
}
// end of [imbuf_vt]

absviewt@ype image_vt (w(*width*):int, h(*height*):int) = imbuf_vt (w, h, null)

viewtypedef image0_vt = [n,m:int] image_vt (m, n)?

fun image_initialize {m,n:pos} (
    w: size_t m, h: size_t n
  , im: &image0_vt >> image_vt (m, n)
  ):<> void
// end of [image_initialize]

fun image_uninitialize {n,m:pos} (
    im: &image_vt (n, m) >> image0_vt
  ):<> void
// end of [image_uninitialize]

(* ****** ****** *)

fun image_width {n,m:pos} (im: !image_vt (m, n)):<> size_t m
fun image_height {n,m:pos} (im: !image_vt (m, n)):<> size_t n

(* ****** ****** *)

fun image_write {n,m:pos} (
    i: sizeLt n, j: sizeLt m
  , p: rgb, im: &image_vt (n, m)
  ):<> void
// end of [image_write]

(* ****** ****** *)

// output the image buffer to a file
fun image_output {n,m:pos} {fm:file_mode} (
    pf: file_mode_lte (fm, w)
  | fl: &FILE fm
  , im: !image_vt (n, m)
  ): void
// end of [image_output]
