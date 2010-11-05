(*
** A doubly-linked list implementation which
** uses no memory allocation (the memory must
** be provided explicitly by the programmer).
** The implementation ensures that no memory
** leaks can occur.
**
** Contributed by Artyom Shalkhakov (artyom DOT shalkhakov AT gmail DOT com)
** Time: November, 2010
** Based on the code written by Hongwei Xi (hwxi AT cs DOT bu DOT edu) sometime in 2004
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

// doubly-linked list segments representation
// we write dlist_v (a, i, i', j, j') and
// i is the address of the node
// i' is the address of the previous node
// j is the address of the node after the last
// j' is the address of the last node

(* ****** ****** *)

viewtypedef dlnode (
  itm:viewt@ype
, prev:addr
, next:addr
) = @{
  prev= ptr prev
, next= ptr next
, itm= itm
} // end of [dlnode]

viewtypedef dlnode (itm:viewt@ype) = @{
  prev= ptr?
, next= ptr?
, itm= itm
}

typedef dlnode0 (itm:viewt@ype) = dlnode (itm)?

(* ****** ****** *)

(* we define two views on doubly-linked list segments:
 * one is forwards -- starts at some node, extends to the right,
 * another is backwards/reverse (extends to the left)
 *)

dataview dlseg_v (
  a:viewt@ype+
, addr // self
, addr // previous (before self)
, addr // next after last
, addr // last
, int  // length
) = (* front view for doubly-linked list segments *)
  | {i,j:addr} dlseg_v_none (a, i, j, i, j, 0)
  | {i,i',j,k,k':addr | i > null; k' > null} {n:nat}
      dlseg_v_some (a, i, i', k, k', n+1) of
        (dlnode (a, i', j) @ i, dlseg_v (a, j, i, k, k', n))
// end of [dlseg_v]

(* ****** ****** *)

dataview rdlseg_v (
  a:viewt@ype+
, addr // self
, addr // prev (before self)
, addr // next (after last)
, addr // last
, int  // length
) = (* backwards view for doubly-linked list segments *)
  | {l, l': addr} rdlseg_v_none (a, l, l', l, l', 0)
  | {n:nat} {f, p', k', l, p:addr | f > null; l > null}
      rdlseg_v_some (a, f, p', k', l, n+1) of
        (rdlseg_v (a, f, p', l, p, n), dlnode (a, p, k') @ l)
// end of [rdlseg_v]

(* ****** ****** *)

// open doubly-linked lists
viewdef dllst_v (a:viewt@ype, l1:addr, l2:addr, n:int) =
  dlseg_v (a, l1, null, null, l2, n)

viewdef rdllst_v (a:viewt@ype, l1:addr, l2:addr, n:int) =
  rdlseg_v (a, l1, null, null, l2, n)

(* ****** ****** *)

// circular doubly-linked lists
// viewdef cdllst_v (a:viewt@ype, l1:addr, l2:addr, n:int) =
//   dlseg_v (a, l1, l2, l1, l2, n)
// viewdef rcdllst_v (a:viewt@ype, l1:addr, l2:addr, n:int) =
//   rdlseg_v (a, l1, l2, l1, l2, n)

(* ****** ****** *)

viewtypedef dllst_vt (a:viewt@ype, l1:addr, l2:addr, n:int) =
  @{pf= dllst_v (a, l1, l2, n), hd= ptr l1, tl= ptr l2}

viewtypedef rdllst_vt (a:viewt@ype, l1:addr, l2:addr, n:int) =
  @{pf= rdllst_v (a, l1, l2, n), hd= ptr l1, tl= ptr l2}

(* ****** ****** *)

(*
 * given pf1 and pf2, two dl segments pointing
 * to one another appropriately, appends pf2
 * onto the end of pf1
 *)
prfun dlseg_v_append {a:viewt@ype} {n1,n2:nat}
  {f1,f2,l1,l2,p,n:addr | l2 > null} (
    pf1: dlseg_v (a, f1, p, f2, l1, n1)
  , pf2: dlseg_v (a, f2, l1, n, l2, n2)
  ):<> dlseg_v (a, f1, p, n, l2, n1+n2)
// end of [dlseg_v_append]

(*
 * given sa1 and sa2, 2 dl segments pointing
 * to one another appropriately,
 * appends sa1 onto the beginning of sa2
 *)
prfun rdlseg_v_append {a: viewt@ype} {n1,n2:nat}
  {f1, f2, l1, l2, pL, nL:addr | f1 > null} (
    sa1: rdlseg_v (a, f1, pL, f2, l1, n1)
  , sa2: rdlseg_v (a, f2, l1, nL, l2, n2)
  ):<> rdlseg_v (a, f1, pL, nL, l2, n1+n2)
// end of [rdlseg_v_append]

(* ****** ****** *)

(*
 * given a front view of a doubly linked list,
 * returns a proof of an end view of that same list
 *)
prfun rdlseg_v_of_dlseg_v {a:viewt@ype} {n:nat} {l1,l2,pL,nL:addr}
  (pf: dlseg_v (a, l1, pL, nL, l2, n)):<> rdlseg_v (a, l1, pL, nL, l2, n)
// end of [rdlseg_v_of_dlseg_v]

(*
 * given an end view of a doubly linked list,
 * returns a proof of a front view of same list
 *)
prfun dlseg_v_of_rdlseg_v {a:viewt@ype} {i,i',j,j':addr} {n:nat}
  (pf: rdlseg_v (a, i, j, i', j', n)):<> dlseg_v (a, i, j, i', j', n)
// end of [dlseg_v_of_rdlseg_v]

(* ****** ****** *)

fun{a:viewt@ype} dlnode_takeout {l,prev,next:addr} (
  pf: dlnode (a, prev, next) @ l | p: ptr l
):<> [l1:addr] (
  a @ l1
, a @ l1 -<lin,prf> dlnode (a, prev, next) @ l
| ptr l1
) // end of [dlnode_takeout]

(* ****** ****** *)

fun{a:viewt@ype} dlseg_is_empty {lh,pr,lt:addr} {n:nat}
  (pf: !dlseg_v (a, lh, pr, null, lt, n) | ph: ptr lh, pt: ptr lt)
  :<> bool (n == 0) // end of [dlseg_is_empty]

fun{a:viewt@ype} rdlseg_is_empty {lh,nx,lt:addr} {n:nat}
  (pf: !rdlseg_v (a, lh, null, nx, lt, n) | ph: ptr lh, pt: ptr lt)
  :<> bool (n == 0) // end of [rdlseg_is_empty]

(* ****** ****** *)

fun{a:viewt@ype} dlseg_takeout {lh,pr,lt:addr} {n:pos} (
    pf: dlseg_v (a, lh, pr, null, lt, n)
  | ph: ptr lh, pt: ptr lt
  ):<> [l1:addr] (
    a @ l1, a @ l1 -<lin,prf> dlseg_v (a, lh, pr, null, lt, n)
  | ptr l1
  ) // end of [dlseg_first_takeout]

fun{a:viewt@ype} rdlseg_takeout {lh,nx,lt:addr} {n:pos} (
    pf: rdlseg_v (a, lh, null, nx, lt, n)
  | ph: ptr lh, pt: ptr lt
  ):<> [l1:addr] (
    a @ l1, a @ l1 -<lin,prf> rdlseg_v (a, lh, null, nx, lt, n)
  | ptr l1
  ) // end of [dlseg_first_takeout]

(* ****** ****** *)

// cons an element onto a dlseg
fun{a:viewt@ype} dlseg_cons {n:nat} {pr',lh,pr,lt,e:addr | pr > null; e > null} (
    pf: dlseg_v (a, lh, pr, null, lt, n)
  , pf_pr: dlnode (a, pr', lh) @ pr
  , pf_at: dlnode a @ e
  | pr: ptr pr, ph: &ptr lh >> ptr e, pt: &ptr lt >> ptr lt', e: ptr e
  ):<> #[lt':addr] (
    dlseg_v (a, e, pr, null, lt', n+1)
  , dlnode (a, pr', e) @ pr
  | void
  ) // end of [dlseg_cons]

// cons an element onto a rdlseg
fun{a:viewt@ype} rdlseg_cons {n:nat} {lh,nx,lt,nx',e:addr | nx > null; e > null} (
    pf: rdlseg_v (a, lh, null, nx, lt, n)
  , pf_nx: dlnode (a, lt, nx') @ nx
  , pf_at: dlnode a @ e
  | nx: ptr nx, ph: &ptr lh >> ptr lh', pt: &ptr lt >> ptr e, e: ptr e
  ):<> #[lh':addr] (
    rdlseg_v (a, lh', null, nx, e, n+1)
  , dlnode (a, e, nx') @ nx
  | void
  ) // end of [rdlseg_cons]

(* ****** ****** *)

fun{a:viewt@ype} dllst_make_empty
  (ph: &ptr? >> ptr null, pt: &ptr? >> ptr null)
  :<> (dllst_v (a, null, null, 0) | void)
// end of [dllst_make_empty]

fun{a:viewt@ype} dllst_make_singleton {l:agz} (
    pf_at: dlnode a @ l
  | ph: &ptr? >> ptr l, pt: &ptr? >> ptr t, pl: ptr l
  ):<> #[t:addr] (dllst_v (a, l, t, 1) | void)
// end of [dllst_make_singleton]

(* ****** ****** *)

fun{a:viewt@ype} dllst_is_empty {n:nat} {lh,lt:addr}
  (pf: !dllst_v (a, lh, lt, n) | ph: ptr lh, pt: ptr lt)
  :<> bool (n == 0)
// end of [dllst_is_empty]

fun{a:viewt@ype} dllst_isnot_empty {n:nat} {lh,lt:addr}
  (pf: !dllst_v (a, lh, lt, n) | ph: ptr lh, pt: ptr lt)
  :<> bool (n <> 0)
// end of [dllst_isnot_empty]

(* ****** ****** *)

fun{a:viewt@ype} dllst_length {n:nat} {lh,lt:addr}
  (pf: !dllst_v (a, lh, lt, n) | ph: ptr lh, pt: ptr lt)
  :<> size_t n
// end of [dllst_length]

(* ****** ****** *)

(*
 * given a front view on a doubly-linked list and a free-standing node,
 * inserts it at the beginning (before first node)
 *)
fun{a:viewt@ype} dllst_cons {n:nat} {lh,lt,e:addr | e > null} (
    pf: dllst_v (a, lh, lt, n), pf_at: dlnode a @ e
  | ph: &ptr lh >> ptr e, pt: &ptr lt >> ptr lt', e: ptr e
  ):<> #[lt':addr] (dllst_v (a, e, lt', n+1) | void)
// end of [dllst_cons]

(* given a front view on a doubly-linked list
 * returns the first element, detaching it from the list
 *)
fun{a:viewt@ype} dllst_uncons {n:pos} {lh,lt:addr} (
    pf: dllst_v (a, lh, lt, n)
  | ph: &ptr lh >> ptr lh', pt: &ptr lt >> ptr lt', e: &ptr? >> ptr lh
  ):<> #[lh',lt':addr] (
    dllst_v (a, lh', lt', n-1)
  , dlnode (a, null, lh') @ lh
  | void
  ) // end of [dllst_uncons]

(* ****** ****** *)

(*
 * given an end view on a doubly-linked list and a free-standing node,
 * insert it at the end (after last node)
 *)
fun{a:viewt@ype} dllst_snoc {n:nat} {lh,lt,e:addr | e > null} (
    pf: rdllst_v (a, lh, lt, n), pf_at: dlnode a @ e
  | ph: &ptr lh >> ptr lh', pt: &ptr lt >> ptr e, e: ptr e
  ):<> #[lh':addr] (rdllst_v (a, lh', e, n+1) | void)
// end of [dllst_snoc]

(*
 * given the end view on a doubly-linked list
 * returns the last element, detaching it from the list
 *)
fun{a:viewt@ype} dllst_unsnoc {n:pos} {lh,lt:addr} (
    pf: rdllst_v (a, lh, lt, n)
  | ph: &ptr lh >> ptr lh', pt: &ptr lt >> ptr lt', pl: &ptr? >> ptr lh
  ):<> #[lh',lt':addr] (
    rdllst_v (a, lh', lt', n-1)
  , dlnode (a, lt', null) @ lt
  | void
  ) // end of [dllst_unsnoc]

(* ****** ****** *)

// concatenate two doubly-linked lists
fun{a:viewt@ype} dllst_concat {n1,n2:nat} {l1h, l1t, l2h, l2t:addr} (
    pf1: dllst_v (a, l1h, l1t, n1), pf2: dllst_v (a, l2h, l2t, n2)
  | p1h: ptr l1h, p1t: ptr l1t, p2h: ptr l2h, p2t: ptr l2t
  , ph: &ptr? >> ptr lh, pt: &ptr? >> ptr lt
  ):<> #[lh,lt:addr] (dllst_v (a, lh, lt, n1+n2) | void)
// end of [dllst_concat]

(* ****** ****** *)

// map [f] over the list in the forward direction
fun{a:viewt@ype} dllst_foreach_main
  {v:view} {vt:viewtype} {n:nat} {lh,lt:addr} {f:eff} (
    pf1: !dllst_v (a, lh, lt, n), pf2: !v
  | ph: ptr lh, pt: ptr lt, f: (!v | &a, !vt) -<f> void, env: !vt
  ):<f> void
// end of [dllst_foreach_main]

// map [f] over the list in reverse direction (backwards)
fun{a:viewt@ype} rdllst_foreach_main
  {v:view} {vt:viewtype} {n:nat} {lh,lt:addr} {f:eff} (
    pf1: !rdllst_v (a, lh, lt, n), pf2: !v
  | ph: ptr lh, pt: ptr lt, f: (!v | &a, !vt) -<f> void, env: !vt
  ):<f> void
// end of [rdllst_foreach_main]

(* ****** ****** *)

(* zipper distinguishes a special "focussed" element (cursor) somewhere
 * within a list and allows navigation
 *)

dataview dllst_v_zipper
  (a:viewt@ype, lh:addr, lf:addr, lt:addr, n1:int, n2:int) =
  | {lfp,lfn:addr} dllst_v_zip (a, lh, lf, lt, n1, n2) of
      (rdlseg_v (a, lh, null, lf, lfp, n1), dlnode (a, lfp, lfn) @ lf,
       dlseg_v (a, lfn, lf, null, lt, n2)) // end of [dllst_v_zip]
// end of [dllst_v_zipper]

prfun dllst_v_of_zipper_v {a:viewt@ype}
  {lh,lf,lt:addr} {l,r:nat}
  (pf: dllst_v_zipper (a, lh, lf, lt, l, r))
  :<> dllst_v (a, lh, lt, l+r+1)
// end of [dllst_v_of_zipper_v]

prfun rdllst_v_of_zipper_v {a:viewt@ype}
  {lh,lf,lt:addr | lf > null; lt > null} {l,r:nat}
  (pf: dllst_v_zipper (a, lh, lf, lt, l, r))
  :<> rdllst_v (a, lh, lt, l+r+1)
// end of [rdllst_v_of_zipper_v]

(* ****** ****** *)

// take the first node as the cursor
fun{a:viewt@ype} dlzipper_make_first {lh,lt:addr} {n:pos}
  ( pf1: dllst_v (a, lh, lt, n)
  | ph: ptr lh, pc: &ptr? >> ptr lh, pc: ptr lt
  ):<> (dllst_v_zipper (a, lh, lh, lt, 0, n-1) | void)
// end of [dlzipper_make_first]

// take the last node as the cursor
fun{a:viewt@ype} dlzipper_make_last {lh,lt:addr} {n:pos}
  ( pf1: rdllst_v (a, lh, lt, n)
  | ph: ptr lh, pc: &ptr? >> ptr lt, pt: ptr lt
  ):<> (dllst_v_zipper (a, lh, lt, lt, n-1, 0) | void)
// end of [dlzipper_make_last]

// returns the element under the cursor
fun{a:viewt@ype} dlzipper_takeout {lh,lc,lt:addr} {l,r:nat} (
    pf1: dllst_v_zipper (a, lh, lc, lt, l, r)
  | ph: ptr lh, pc: ptr lc, pt: ptr lt
  ):<> [l1:addr] (
    a @ l1, a @ l1 -<lin,prf> dllst_v_zipper (a, lh, lc, lt, l, r)
  | ptr l1
  )
// end of [dlzipper_takeout]

// returns true if there is at least one element
// to the left of the cursor
fun{a:viewt@ype} dlzipper_left_is_empty {lh,lc,lt:addr} {l,r:nat}
  ( pf1: !dllst_v_zipper (a, lh, lc, lt, l, r)
  | ph: ptr lh, pc: ptr lc, pt: ptr lt
  ):<> bool (l == 0)
// end of [dlzipper_left_is_empty]

// returns true if there is at least one element
// to the right of the cursor
fun{a:viewt@ype} dlzipper_right_is_empty {lh,lc,lt:addr} {l,r:nat}
  ( pf1: !dllst_v_zipper (a, lh, lc, lt, l, r)
  | ph: ptr lh, pc: ptr lc, pt: ptr lt
  ):<> bool (r == 0)
// end of [dlzipper_right_is_empty]

// move the cursor one node right
fun{a:viewt@ype} dlzipper_move_right
  {lh,lc,lt:addr} {l:nat} {r:pos}
  ( pf1: dllst_v_zipper (a, lh, lc, lt, l, r)
  | ph: ptr lh, pc: &ptr lc >> ptr lc', pt: ptr lt)
  :<> #[lc':addr] (dllst_v_zipper (a, lh, lc', lt, l+1, r-1) | void)
// end of [dlzipper_move_right]

// move the cursor one node left
fun{a:viewt@ype} dlzipper_move_left
  {lh,lc,lt:addr} {l:pos} {r:nat} (
    pf1: dllst_v_zipper (a, lh, lc, lt, l, r)
  | ph: ptr lh, pc: &ptr lc >> ptr lc', pt: ptr lt
  ):<> #[lc':addr] (dllst_v_zipper (a, lh, lc', lt, l-1, r+1) | void)
// end of [dlzipper_move_left]

// insert before cursor
fun{a:viewt@ype} dlzipper_cons
  {lh,lc,lt,le:addr | le > null} {l,r:nat} (
    pf1: dllst_v_zipper (a, lh, lc, lt, l, r),
    pf_at: dlnode a @ le
  | ph: &ptr lh >> ptr lh', pc: ptr lc, pt: ptr lt, e: ptr le
  ):<> #[lh':addr] (dllst_v_zipper (a, lh', lc, lt, l+1, r) | void)
// end of [dlzipper_cons]

// insert after cursor
fun{a:viewt@ype} dlzipper_snoc
  {lh,lc,lt,le:addr | le > null} {l,r:nat} (
    pf1: dllst_v_zipper (a, lh, lc, lt, l, r),
    pf_at: dlnode a @ le
  | ph: ptr lh, pc: ptr lc, pt: &ptr lt >> ptr lt', e: ptr le
  ):<> #[lt':addr] (dllst_v_zipper (a, lh, lc, lt', l, r+1) | void)
// end of [dlzipper_snoc]

(* ****** ****** *)
