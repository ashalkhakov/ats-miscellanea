(* simplistic implementation of image buffer
**
** here we define an image buffer to be a matrix
** of pixels. pixel at (0,0) is at the bottom left
** corner.
**
** written by Artyom Shalkhakov on Dec 22, 2010
*)
(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload _ = "prelude/DATS/array.dats"

(* ****** ****** *)

staload "SATS/vec.sats"
staload "SATS/imbuf.sats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynloading at runtime

(* ****** ****** *)

// pixel of image buffer: little-endian RGB (alpha is not used)
typedef pxl = uint
fun{} quantize .< >. (r: float, g: float, b: float):<> pxl = let
  fn{} f2ui (x: float):<> uint = uint_of_int (int_of_float x)
in
  (f2ui (r * 255.0f) << 16)
    lor (f2ui (g * 255.0f) << 8)
    lor (f2ui (b * 255.0f))
end
val pxl_zero: pxl = 0u

(* ****** ****** *)

// implementation type
viewtypedef IMAGE_vt (
  m:int, n:int, l:addr, nm:int
) = @{
  buf= imbuf_vt (m, n, l)
, pf_mul= MUL (n, m, nm)
, pfb= matrix_v (pxl, n, m, l)
, pfb_gc= free_gc_v (pxl, nm, l)
} // end of [IMAGE_vt]

viewtypedef IMAGE0_vt = IMAGE_vt (0, 0, null, 0)?

assume image_vt (m:int, n:int) =
  [l:addr] [mn:int] IMAGE_vt (m, n, l, mn)

(* ****** ****** *)

implement image_initialize {m,n} (w, h, im) = () where {
  prval () = __assert (im) where {
    extern prfun __assert (im: &image0_vt >> IMAGE0_vt):<> void
  } // end of [prval]
  val [mn:int] (pf_mul | wh) = h szmul2 w
  val [l:addr] (pf_ngc, pf_arr | b) = array_ptr_alloc<pxl> (wh)
  val () = array_ptr_initialize_elt<pxl> (!b, wh, pxl_zero)
  prval pf_mat = matrix_v_of_array_v {pxl} (pf_mul, pf_arr)
  val () = im.buf.w := w
  val () = im.buf.h := h
  val () = im.buf.b := b
  prval () = im.pf_mul := pf_mul
  prval () = im.pfb := pf_mat
  prval () = im.pfb_gc := pf_ngc
}

(* ****** ****** *)

implement image_uninitialize {n,m} (im) = () where {
  prval (pf_mul, pf_arr) = array_v_of_matrix_v {pxl} (im.pfb)
  prval () = mul_isfun (pf_mul, im.pf_mul)
  val () = array_ptr_free (im.pfb_gc, pf_arr | im.buf.b)
  prval () = __assert (im) where {
    extern prfun __assert (s: &IMAGE0_vt >> image0_vt):<> void
  } // end of [prval]
}

(* ****** ****** *)

implement image_width {n,m} (im) = im.buf.w
implement image_height {n,m} (im) = im.buf.h

(* ****** ****** *)

implement image_write {n,m} (i, j, p, im) = () where {
  // image pixel at (i,j) is actually stored at b + (j*w + i)
  val (pf_at, fpf | pij) = matrix_ptr_takeout_tsz {pxl} (
    im.pfb | im.buf.b, j, im.buf.w, i, sizeof<pxl>
  )
  val () = !pij := quantize (p.r, p.g, p.b)
  prval () = im.pfb := fpf pf_at
}

(* ****** ****** *)

(*
from TGA spec (http://www.dca.fee.unicamp.br/~martino/disciplinas/ea978/tgaffs.pdf)

everything is little-endian

tga header:
  ID_Length: byte @ 0
  color_map_type: byte @ 1 (always 0)
  image type: byte @ 2
    0 no image data included
    1 uncompressed, color-mapped
    2 uncompressed, true color
    3 uncompressed, black and white
    5 RLE, color-mapped
    10 RLE, true color
    11 RLE, b&w
  color_map_specification: bytes 5 @ 3
    all zero (since color_map_type is zero)
  image specification: bytes 10 @ 8
    x origin: bytes 2
    y origin: bytes 2
    image width: bytes 2
    image height: bytes 2
    pixel depth: byte (8, 16, 24, 32)
    descriptor: byte
       bits: 7 6 5 4 3 2 1 0
       bits 3 - 0: zero
       bits 4, 5: left to right ordering,  top to bottom ordering
         screen destination of first pixel | image origin bit 5 | bit 4
         bottom left 0 0
         bottom right 0 1
         top left 1 0
         top right 1 1
       bits  6, 7: zero

image/color map data:
   image ID: bytes (ID_Length)
  color map data: bytes 0 (since no colormap exists)
  image data: variable
    width * height pixels

Each pixel specifies image data in one of the following formats: a single color-map index for Pseudo-Color; Attribute, Red, Green and Blue ordered data for True-Color; and independent color-map indices for Direct-Color. The number of attribute and color-definition bits for each pixel are defined in image descriptor and pixel depth, respectively. Each pixel is stored as an integral number of bytes.

then goes developer area, extension area and footer.

footer:
  Bytes 0-3: The Extension Area Offset (zero)
  Bytes 4-7: The Developer Directory Offset (zero)
  Bytes 8-23: The Signature: TRUEVISION-XFILE
  Byte 24: ASCII Character “.”
  Byte 25: Binary zero string terminator (0x00)

----image types
true color iff color map type = 0, image type = 2
RLE true color iff color map type = 0, image type = 10

----run-length encoding of images
the basic idea is to replace a row of consecutive pixels identical to each other with a notice saying that "N pixels have the value A". for example, AAA is replaced by 3A.
two types of elements: run-length packets and raw packets.
packet = repetitionCount: byte, pixelValue: pixel
the 2D matrix of pixels is then represented by:

list (packets, rows)

(because packets can never cross the scan line boundary)

The first field (1 byte) of each packet is called the Repetition Count field. The second field is called the Pixel Value field. For Run-length Packets, the Pixel Value field contains a single pixel value. For Raw Packets, the field is a variable number of pixel values.

rle_pixel = bool * packet, if bool is true, then we have an RLE packet, otherwise it is a raw packet.

The highest order bit of the Repetition Count indicates whether the packet is a Raw Packet or a Run-length Packet. If bit 7 of the Repetition Count is set to 1, then the packet is a Run-length Packet. If bit 7 is set to zero, then the packet is a Raw Packet.

The lower 7 bits of the Repetition Count specify how many pixel values are represented by the packet. In the case of a Run-length packet, this count indicates how many successive pixels have the pixel value specified by the Pixel Value field. For Raw Packets, the Repetition Count specifies how many pixel values are actually contained in the next field. This 7 bit value is actually encoded as 1 less than the number of pixels in the packet (a value of 0 implies 1 pixel while a value of 0x7F implies 128 pixels).

Run-length Packets should never encode pixels from more than one scan line. Even if the end of one scan
line and the beginning of the next contain pixels of the same value, the two should be encoded as separate
packets. In other words, Run-length Packets should not wrap from one line to another. This scheme allows
software to create and use a scan line table for rapid, random access of individual lines. Scan line tables are
discussed in further detail in the Extension Area section of this document.

As an example of the difference between the two packet types, consider a section of a single scan line with
128, 24-bit (3 byte) pixels all with the same value (color). The Raw Packet would require 1 byte for the
Repetition Count and 128 pixels values each being 3 bytes long (384 bytes). The total number of bytes
required to specify the chosen data using the Raw Packet is, therefore, 385 bytes. The Run-length Packet
would require 1 byte for the Repetition Count and a single, 3-byte pixel value. The total number of bytes
required to specify the chosen data using the Run-length Packet is, therefore, just 4 bytes!

Some theoretical considerations:
- TGA file format may be formalized using type theory! what gives?
  essentially, it's just a derivation of some sort
- the structure of a TGA file can be captured using inductively defined dependent types
- since we're dealing with memory locations, this is all about heap: linear types to the rescue
  (no aliasing, thus no problems)

*)

// should really go to the prelude
// applies [f] to every element of [p_mat]
fun{a:t@ype}{vt:viewt@ype} matrix_ptr_app {e:eff} {m,n:nat} {l:addr} .< >. (
    pf_mat: !matrix_v (a, m, n, l)
  | f: (&vt, a) -<fun,e> void
  , p_mat: ptr l
  , m: size_t m, n: size_t n
  , env: &vt
  ):<e> void = let
  // we rely on the fact that matrix is a 2D array
  // and is stored in memory thus:
  //   row 1
  //   row 2
  //   row 3
  // where each row consists of columns
  // but but this means that we have column-major matrix! (this is not the case!)
  fun loop {s:nat} {l:addr} .<s>. (
      pf_arr: !array_v (a, s, l)
    | f: (&vt, a) -<fun,e> void
    , env: &vt
    , b: ptr l, s: size_t s
    ):<e> void = if s > 0 then let
    prval (pf_at, pf1_arr) = array_v_uncons {a} (pf_arr)
    val () = f (env, !b)
    val () = loop (pf1_arr | f, env, b + sizeof<a>, s-1)
    prval () = pf_arr := array_v_cons {a} (pf_at, pf1_arr)
  in (*empty*) end else let
    prval () = array_v_unnil {a} (pf_arr)
    prval () = pf_arr := array_v_nil {a} ()
  in (*empty*) end // end of [loop]
  val (pf_mul | mn) = m szmul2 n
  prval (pf_mul2, pf_arr) = array_v_of_matrix_v{a} (pf_mat)
  prval () = mul_isfun (pf_mul, pf_mul2)
  prval () = mul_nat_nat_nat {m,n} (pf_mul)
  val () = loop (pf_arr | f, env, p_mat, mn)
  prval () = pf_mat := matrix_v_of_array_v{a} (pf_mul, pf_arr)
in
  (*empty*)
end // end of [matrix_ptr_app]

// will write true color TGA
implement image_output {n,m} {fm} (pf_mod | fl, im) = let
  (*
  ** helper functions
  *)
  local
    #define ui2b char_of_uint
  in
    fun fwr_byte .< >. (fl: &FILE fm, x: uint):<!exn> void =
      fputc_exn (pf_mod | char_of_uint x, fl)
    // write a two-byte word in little-endian order
    fun fwr_short .< >. (fl: &FILE fm, x: uint):<!exn> void = begin
      fputc_exn (pf_mod | ui2b (x land 255u), fl);
      fputc_exn (pf_mod | ui2b ((x >> 8) land 255u), fl)
    end // end of [fwr_short]
    // write a string and a null to the file
    fun fwr_string (fl: &FILE fm, x: !READ(string)): void = begin
      fputs_exn (pf_mod | x, fl);
      fputc_exn (pf_mod | '\0', fl)
    end // end of [fwr_string]
    // write a true color pixel
    fun fwr_pxl (fl: &FILE fm, v: pxl): void = begin
      fwr_byte (fl, v land 255u); // blue
      fwr_byte (fl, (v >> 8) land 255u); // green
      fwr_byte (fl, (v >> 16) land 255u) // red
    end // end of [fwr_pxl]
  end // end of [local]
  (*
  ** write TGA header
  *)
  val () = fwr_byte (fl, 0u) // id length
  val () = fwr_byte (fl, 0u) // color map type
  val () = fwr_byte (fl, 2u) // image type (uncompressed RGB)
  val () = (fwr_short (fl, 0u); fwr_short (fl, 0u); fwr_byte (fl, 0u)) // color map
  val () = (fwr_short (fl, 0u); fwr_short (fl, 0u)) // x,y origin
  val () = let
    val () = assert_errmsg (im.buf.w < 65535, "width too big")
    val () = assert_errmsg (im.buf.h < 65535, "height too big")
    val () = fwr_short (fl, uint_of_size im.buf.w)
    val () = fwr_short (fl, uint_of_size im.buf.h)
  in (*empty*) end
  val () = fwr_byte (fl, 24u) // color bits
  val () = fwr_byte (fl, 0u) // image descriptor
  (*
  ** write image data
  *)
  // no image id
  // no color map
  val () = matrix_ptr_app (im.pfb | fwr_pxl, im.buf.b, im.buf.h, im.buf.w, fl) // image data
  (*
  ** write footer
  *)
  val () = (fwr_short (fl, 0u); fwr_short (fl, 0u)) // extension area offset
  val () = (fwr_short (fl, 0u); fwr_short (fl, 0u)) // developer directory offset
  val () = fwr_string (fl, "TRUEVISION-XFILE.")
in (*empty*) end
