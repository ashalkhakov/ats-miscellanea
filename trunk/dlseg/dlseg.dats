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

#define ATS_DYNLOADFLAG 0 // no dynloading at run-time
#define ATS_STALOADFLAG 0 // no staloading at run-time

(* ****** ****** *)

staload "dlseg.sats"

(* ****** ****** *)

sortdef t0p = t@ype and vt0p = viewt@ype

(* ****** ****** *)

implement dlseg_v_append {a} {n1,n2} {f1,f2,l1,l2,p,n} (pf1, pf2) =
  case+ pf1 of
  | dlseg_v_none () => pf2
  | dlseg_v_some (pf_at, pf1) => 
      dlseg_v_some (pf_at, dlseg_v_append (pf1, pf2))

implement rdlseg_v_append (sa1, sa2) = let
  prfun loop {a:vt0p} {n1,n2:nat}
    {f1, f2, l1, l2, pL, nL:addr | f1 <> null} .<n2>. (
    sa1: rdlseg_v (a, f1, pL, f2, l1, n1)
  , sa2: rdlseg_v (a, f2, l1, nL, l2, n2)
  ):<> rdlseg_v (a, f1, pL, nL, l2, n1+n2) = case+ sa2 of
  | rdlseg_v_none () => sa1
  | rdlseg_v_some (sa22, sa21) => 
      rdlseg_v_some (loop (sa1, sa22), sa21)
in
  loop (sa1, sa2)
end

implement rdlseg_v_of_dlseg_v (pf) = let
  prfun loop {a:vt0p} {n:nat} {l1,l2,pL,nL:addr} .<n>.
    (pf: dlseg_v (a, l1, pL, nL, l2, n)):<> rdlseg_v (a, l1, pL, nL, l2, n)
    = case+ pf of 
    | dlseg_v_none () => rdlseg_v_none ()
    | dlseg_v_some (pf_at, pf) =>
        rdlseg_v_append (rdlseg_v_some (rdlseg_v_none (), pf_at), loop pf)
in
  loop pf
end

implement dlseg_v_of_rdlseg_v {a} {i,i',j,j'} {n} (pf) = let
  prfun loop {a:vt0p} {n:nat} {l1,l2,pL,nL:addr} .<n>.
    (pf: rdlseg_v (a, l1, pL, nL, l2, n)):<> dlseg_v (a, l1, pL, nL, l2, n)
    = case+ pf of
    | rdlseg_v_none () => dlseg_v_none ()
    | rdlseg_v_some (pf, pf_at) =>
        dlseg_v_append (loop pf, dlseg_v_some (pf_at, dlseg_v_none ()))
in
  loop pf
end

(* ****** ****** *)

implement{a} dllst_make_empty (ph, pt) = begin
  ph := null;
  pt := null;
  (dlseg_v_none () | ())
end

implement{a} dllst_make_singleton {l} (pf_at | ph, pt, pl) = let
  val () = pl->next := null
  val () = pl->prev := null
  val () = ph := pl
  val () = pt := pl
in
  (dlseg_v_some (pf_at, dlseg_v_none ()) | ())
end

(* ****** ****** *)

implement{a} dllst_is_empty (pf | ph, pt) =
  if ph = null then let
    prval dlseg_v_none () = pf
    prval () = pf := dlseg_v_none ()
  in true end else let
    prval dlseg_v_some (pf_at, pf1) = pf
    prval () = pf := dlseg_v_some (pf_at, pf1)
  in false end

implement{a} dllst_isnot_empty (pf | ph, pt) =
  ~dllst_is_empty (pf | ph, pt)

(* ****** ****** *)

implement{a} dllst_length {n}{lh,lt} (pf | ph, pt) = let
  fun{a:vt0p} loop {i,j,pr,nx:addr | nx == null} {k,n:nat} .<n>.
    ( pf: !dlseg_v (a, i, pr, nx, j, n)
    | i: ptr i, pr: ptr pr, nx: ptr nx, j: ptr j, k: size_t k)
    :<> size_t (n+k) =
    if i = null then let
      prval dlseg_v_none () = pf
      prval () = pf := dlseg_v_none ()
    in k end else let
      prval dlseg_v_some (pf_at, pf2) = pf
      val k = loop (pf2 | i->next, i, nx, j, k+1)
      prval () = pf := dlseg_v_some (pf_at, pf2)
    in k end
in
  loop (pf | ph, null, null, pt, 0)
end

(* ****** ****** *)

implement{a} dllst_cons {n}{lh,lt,e} (pf, pf_at | ph, pt, e) =
  if ph = null then let
    prval dlseg_v_none () = pf
  in
    e->next := null;
    e->prev := null;
    ph := e;
    pt := e;
    (dlseg_v_some (pf_at, dlseg_v_none ()) | ())
  end else let
    prval dlseg_v_some (pf1_at, pf2) = pf
  in
    e->next := ph;
    e->prev := null;
    ph->prev := e;
    ph := e;
    (dlseg_v_some (pf_at, dlseg_v_some (pf1_at, pf2)) | ())
  end

implement{a} dllst_uncons {n}{lh,lt} (pf | ph, pt, pl) = let
    prval dlseg_v_some (pf1_at, pf1) = pf
    val p = ph
    val nxt = ph->next
  in
    if nxt = null then let
       prval dlseg_v_none () = pf1
    in
       ph := null; pt := null;
       pl := p;
       (dlseg_v_none (), pf1_at | ())
    end else let
      prval dlseg_v_some (pf2_at, pf2) = pf1
    in
      nxt->prev := null;
      pl := ph;
      ph := nxt;
      (dlseg_v_some (pf2_at, pf2), pf1_at | ())
    end
  end

(* ****** ****** *)

implement{a} dllst_snoc {n}{lh,lt,e} (pf, pf_at | ph, pt, e) =
  if pt = null then let
    prval rdlseg_v_none () = pf
  in 
    e->next := null;
    e->prev := null;
    ph := e;
    pt := e;
    (rdlseg_v_some (rdlseg_v_none (), pf_at) | ())
  end else let
    prval rdlseg_v_some (pf2, pf1_at) = pf
  in
    e->prev := pt;
    e->next := null;
    pt->next := e;
    pt := e;
    (rdlseg_v_some (rdlseg_v_some (pf2, pf1_at), pf_at) | ())
  end

implement{a} dllst_unsnoc {n}{lh,lt} (pf | ph, pt, pl) = let
    prval rdlseg_v_some (pf1, pf1_at) = pf
    val p = ph
    val pre = pt->prev
  in
    if pre = null then let
       prval rdlseg_v_none () = pf1
    in
       ph := null; pt := null;
       pl := p;
       (rdlseg_v_none (), pf1_at | ())
    end else let
      prval rdlseg_v_some (pf2, pf2_at) = pf1
      val () = pre->next := null
    in
      pt := pre;
      pl := p;
      (rdlseg_v_some (pf2, pf2_at), pf1_at | ())
    end
  end

(* ****** ****** *)

implement{a} dllst_concat {n1,n2}{l1h,l1t,l2h,l2t}
  (pf1, pf2 | p1h, p1t, p2h, p2t, ph, pt) =
  if p1h = null then let
    prval dlseg_v_none () = pf1
  in
    ph := p2h;
    pt := p2t;
    (pf2 | ())
  end else if p2h = null then let
    prval dlseg_v_none () = pf2
  in
    ph := p1h;
    pt := p1t;
    (pf1 | ())
  end else let
    prval dlseg_v_some (pfh2, pfrest2) = pf2
    prval rdlseg_v_some (pftrest1, pft1) = rdlseg_v_of_dlseg_v pf1
    val () = p1t->next := p2h
    val () = p2h->prev := p1t
    prval pf1' = dlseg_v_of_rdlseg_v (rdlseg_v_some (pftrest1, pft1))
    prval ret_pf = dlseg_v_append (pf1', dlseg_v_some (pfh2, pfrest2))
  in
    ph := p1h;
    pt := p2t;
    (ret_pf | ())
  end

(* ****** ****** *)

implement{a} dllst_foreach_main {v}{vt}{n}{lh,lt}{f} (pf1, pf2 | ph, pt, f, env) = let
  fun{a:vt0p} loop {v:view} {vt:viewtype} {n:nat} {lh,lt,pr:addr} {f:eff} .<n>. (
      pf1: !dlseg_v (a, lh, pr, null, lt, n), pf2: !v
    | ph: ptr lh, pr: ptr pr, pt: ptr lt, f: (!v | &a, !vt) -<f> void, env: !vt
    ):<f> void =
    if ph = null then let
      prval dlseg_v_none () = pf1
      prval () = pf1 := dlseg_v_none ()
    in (*nothing*) end else let
      prval dlseg_v_some (pf_at, pf_rst) = pf1
      val () = f (pf2 | ph->itm, env)
      val () = loop (pf_rst, pf2 | ph->next, ph, pt, f, env)
      prval () = pf1 := dlseg_v_some (pf_at, pf_rst)
    in (*nothing*) end
in
  loop (pf1, pf2 | ph, null, pt, f, env)
end

implement{a} rdllst_foreach_main {v}{vt}{n}{lh,lt}{f} (pf1, pf2 | ph, pt, f, env) = let
  fun{a:vt0p} loop {v:view} {vt:viewtype} {n:nat} {lh,lt,nx:addr} {f:eff} .<n>. (
      pf1: !rdlseg_v (a, lh, null, nx, lt, n), pf2: !v, nx: ptr nx
    | ph: ptr lh, pt: ptr lt, f: (!v | &a, !vt) -<f> void, env: !vt
    ):<f> void =
    if pt = null then let
      prval rdlseg_v_none () = pf1
      prval () = pf1 := rdlseg_v_none ()
    in (*nothing*) end else let
      prval rdlseg_v_some (pf_rst, pf_at) = pf1
      val () = f (pf2 | pt->itm, env)
      val () = loop (pf_rst, pf2, pt | ph, pt->prev, f, env)
      prval () = pf1 := rdlseg_v_some (pf_rst, pf_at)
    in (*nothing*) end
in
  loop (pf1, pf2, null | ph, pt, f, env)
end

(* ****** ****** *)

implement dllst_v_of_zipper_v {a} {lh,lf,lt} {l,r} (pf) = let
  prval dllst_v_zip (pf1, pf_at, pf2) = pf
  prval () = __assert () where {
    // it's really tiring to thread such constraints everywhere
    extern prfun __assert (): [lf <> null && lt <> null] void
  }
in
  dlseg_v_append (dlseg_v_of_rdlseg_v pf1, dlseg_v_some (pf_at, pf2))
end

implement rdllst_v_of_zipper_v {a} {lh,lf,lt} {l,r} (pf) =
  rdlseg_v_of_dlseg_v (dllst_v_of_zipper_v pf)

(* ****** ****** *)

// take the first node as the cursor
implement{a} dlzipper_make_first {lh,lt} {n} (pf1 | ph, f, pt) = let
  prval dlseg_v_some (pf_at, pf1) = pf1
in
  f := ph;
  (dllst_v_zip (rdlseg_v_none (), pf_at, pf1) | ())
end

// take the last node as the cursor
implement{a} dlzipper_make_last {lh,lt} {n} (pf1 | ph, f, pt) = let
  prval rdlseg_v_some (pf1, pf_at) = pf1
in
  f := pt;
  (dllst_v_zip (pf1, pf_at, dlseg_v_none ()) | ())
end

// shows how to take out an item from a node
fun dlnode_takeout {a:vt0p} {l,prev,next:addr} .< >. (
  pf: dlnode (a, prev, next) @ l | p: ptr l
):<> [l1:addr] (
  a @ l1, a @ l1 -<lin,prf> dlnode (a, prev, next) @ l | ptr l1
) = let
  val pitm = &(p->itm)
  prval pfitm = view@ (p->itm)
in #[.. | (
  pfitm
, llam pfitm => let prval () = view@ (p->itm) := pfitm in view@ (!p) end
| pitm
)] end // end of [dlnode_takeout]

// returns the element under the cursor
implement{a} dlzipper_takeout {lf,lh,lt} {l,r}
  (pf | ph, p, pt) = let
  prval dllst_v_zip (pf_l, pf, pf_r) = pf
  val pitm = &(p->itm)
  prval pfitm = view@ (p->itm)
in #[.. | (
    pfitm
  , llam pfitm => let
      prval () = view@ (p->itm) := pfitm
    in
      dllst_v_zip (pf_l, view@ (!p), pf_r)
    end
  | pitm
  )]
end // end of [dlzipper_takeout]

fn{a:vt0p} dlseg_is_empty {lh,pr,lt:addr} {n:nat}
  (pf: !dlseg_v (a, lh, pr, null, lt, n) | ph: ptr lh, pt: ptr lt)
  :<> bool (n == 0) =
    if ph = null then let
      prval dlseg_v_none () = pf
      prval () = pf := dlseg_v_none ()
    in true end else let
      prval dlseg_v_some (pf_at, pf1) = pf
      prval () = pf := dlseg_v_some (pf_at, pf1)
    in false end

fn{a:vt0p} rdlseg_is_empty {lh,nx,lt:addr} {n:nat}
  (pf: !rdlseg_v (a, lh, null, nx, lt, n) | ph: ptr lh, pt: ptr lt)
  :<> bool (n == 0) =
    if pt = null then let
      prval rdlseg_v_none () = pf
      prval () = pf := rdlseg_v_none ()
    in true end else let
      prval rdlseg_v_some (pf1, pf_at) = pf
      prval () = pf := rdlseg_v_some (pf1, pf_at)
    in false end

// returns true if there is at least one element
// to the left of the cursor
implement{a} dlzipper_left_is_empty {lh,lf,lt} {l,r}
  (pf1 | ph, pf, pt) = let
  prval dllst_v_zip (pf_l, pf_at, pf_r) = pf1
  val b = rdlseg_is_empty (pf_l | ph, pf->prev)
  prval () = pf1 := dllst_v_zip (pf_l, pf_at, pf_r)
in
  b
end

// returns true if there is at least one element
// to the right of the cursor
implement{a} dlzipper_right_is_empty {lh,lf,lt} {l,r} (pf1 | ph, pf, pt) = let
  prval dllst_v_zip (pf_l, pf_at, pf_r) = pf1
  val b = dlseg_is_empty (pf_r | pf->next, pt)
  prval () = pf1 := dllst_v_zip (pf_l, pf_at, pf_r)
in
  b
end

// move the cursor one node right
implement{a} dlzipper_move_right {lh,lf,lt} {l} {r}
  (pf1 | ph, pf, pt) = let
  prval dllst_v_zip (pf1, pf_at, dlseg_v_some (pf1_at, pf2)) = pf1
  val () = pf := pf->next
  prval () = __assert () where {
    extern prfun __assert (): [lh <> null && lf <> null] void
  }
in
  (dllst_v_zip (rdlseg_v_some (pf1, pf_at), pf1_at, pf2) | ())
end

// move the cursor one node left
implement{a} dlzipper_move_left {lh,lf,lt} {l} {r} (
    pf1
  | ph, pf, pt
  ) = let
  prval dllst_v_zip (rdlseg_v_some (pf1, pf1_at), pf_at, pf2) = pf1
  val () = pf := pf->prev
  prval () = __assert () where {
    extern prfun __assert (): [lf <> null && lt <> null] void
  }
in
  (dllst_v_zip (pf1, pf1_at, dlseg_v_some (pf_at, pf2)) | ())
end

// insert before cursor
implement{a} dlzipper_cons {lh,lf,lt,le} {l,r} (
    pf1, pf_at
  | ph, pf, pt, e
  ) = let
  prval dllst_v_zip (pf_l, pf1_at, pf_r) = pf1
  val pr = pf->prev
in
  if pr = null then let
    prval rdlseg_v_none () = pf_l
    val () = e->prev := pr
    val () = pf->prev := e
    val () = e->next := pf
    val () = ph := e
  in
    (dllst_v_zip (rdlseg_v_some (rdlseg_v_none (), pf_at), pf1_at, pf_r) | ())
  end else let
    prval rdlseg_v_some (pf_l, pf2_at) = pf_l
    val () = e->prev := pr
    val () = pf->prev := e
    val () = e->next := pf
    val () = pr->next := e
  in
    (dllst_v_zip (rdlseg_v_some (rdlseg_v_some (pf_l, pf2_at), pf_at), pf1_at, pf_r) | ())
  end
end

// insert after cursor
implement{a} dlzipper_snoc {lh,lf,lt,le} {l,r} (
    pf1, pf_at
  | ph, pf, pt, e
  ) = let
  prval dllst_v_zip (pf_l, pf1_at, pf_r) = pf1
  val nx = pf->next
in
  if nx = null then let
    prval dlseg_v_none () = pf_r
    val () = e->next := nx
    val () = pf->next := e
    val () = e->prev := pf
    val () = pt := e
  in
    (dllst_v_zip (pf_l, pf1_at,
      dlseg_v_some (pf_at, dlseg_v_none ())) | ())
  end else let
    prval dlseg_v_some (pf2_at, pf_r) = pf_r
    val () = e->next := nx
    val () = pf->next := e
    val () = e->prev := pf
    val () = nx->prev := e
  in
    (dllst_v_zip (pf_l, pf1_at,
      dlseg_v_some (pf_at, dlseg_v_some (pf2_at, pf_r))) | ())
  end
end
