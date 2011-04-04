staload M = "libats/SATS/linmap_avltree.sats"

staload "SATS/linset.sats"

(* ****** ****** *)

assume set_t0ype (a:t@ype) = $M.map (a, bool)

(* ****** ****** *)

implement{} linset_make_nil {key} () =
  $M.linmap_make_nil {key,bool} ()
// end of [linset_make_nil]

(* ****** ****** *)

// implement{key} linset_search (m, k0, cmp) =

(* ****** ****** *)

implement{key} linset_insert (m, k0, cmp) = let
  var res: bool
  val b = $M.linmap_insert (m, k0, false, cmp, res)
in
  if :(res: bool?) => b then let
    prval () = opt_unsome {bool} (res)
  in b end else let
    prval () = opt_unnone {bool} (res)
  in b end
end

(* ****** ****** *)

// implement{key} linset_remove (m, k0, cmp) =

(* ****** ****** *)

implement{key} linset_listize_free (m) = let
  fun loop {n:nat} .<n>. (
      xs: list_vt (@(key, bool), n)
    ):<> list_vt (key, n) = case+ xs of
    | list_vt_nil () => (fold@ xs; xs)
    | ~list_vt_cons ((x, y), xs) => list_vt_cons (x, loop xs)
  // end of [loop]
in
  loop ($M.linmap_listize_free m)
end // end of [linset_listize_free]
