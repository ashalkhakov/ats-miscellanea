(*
** a data structure to represent sets
*)

absviewtype set_t0ype (key:t@ype)
stadef set = set_t0ype

typedef cmp (key:t@ype) = (key, key) -<cloref> Sgn
fun{key:t@ype} compare_key_key (x1: key, x2: key, cmp: cmp key):<> Sgn

fun{} linset_make_nil {key:t@ype} ():<> set key
// end of [linset_make_nil]

fun{key:t@ype}
linset_search (
  m: !set key
, k0: key, cmp: cmp key
) :<> #[b:bool] bool b // end of [linset_search]

fun{key:t@ype}
linset_insert (
  m: &set key
, k0: key, cmp: cmp key
) :<> #[b:bool] bool b // end of [linset_insert]

fun{key:t@ype}
linset_remove (m: &set key, k0: key, cmp: cmp key):<> bool
// end of [linset_remove]

fun{key:t@ype}
linset_listize_free (m: set key):<> List_vt key
// end of [linset_listize_free]
