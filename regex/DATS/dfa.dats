
(* DFA construction using derivatives *)
// TODO: regular vectors

(* ****** ****** *)

staload "SATS/charset.sats"
staload "SATS/regexp.sats"
staload "SATS/dfa.sats"

staload M = "libats/SATS/linmap_avltree.sats"
staload _ = "libats/DATS/linmap_avltree.dats"

staload _ = "prelude/DATS/list_vt.dats"

dynload "libats/DATS/linmap_avltree.dats"

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)

(*
constructing a DFA (Q, q0, F, sigma)
where Q is the set of states, q0 is the start state,
F (a subset of Q) is the set of accepting states,
sigma is a transition function Q ^ E -> Q (represented
explicitly)

elements of Q have the form (id, RE) (for "id = RE")
*)

(* ****** ****** *)

// FIXME: it seems that guaranteeing that
// all indices range from 0 to some N is a tough
// problem -- nevertheless, can we accomplish this?
assume DFA = '{
  states= List_vt @(RE, size_t)
, start= size_t
, accept= List_vt size_t
, trans= List_vt @(@(size_t, charset), size_t)
}

(* ****** ****** *)

// algorithm from "Regular expression derivatives re-examined"
// (with character classes)
implement dfa_make (r) = let
  // states identified with regular expressions
  viewtypedef Q = $M.map (RE, size_t)
  // transitions
  viewtypedef sigma = $M.map ((size_t, charset), size_t)
  // accepting states
  viewtypedef F = List_vt size_t
  viewtypedef ENV = @{qs= Q, sig= sigma, f= F, id= size_t}

  fn cmp (x1: RE, x2: RE):<cloref> Sgn = 0

  implement $M.compare_key_key<RE> (x1, x2, _) = compare (x1, x2)

  fn cmp2 (x1: (size_t, charset), x2: (size_t, charset)):<cloref> Sgn = let
    val t = compare (int_of_size x1.0, int_of_size x2.0)
  in
    if t = 0 then compare (x1.1, x2.1)
    else t
  end

  fun{key:t@ype;itm:t@ype} linmap_replace .< >. (
      m: &($M.map (key, itm))
    , k0: key, x0: itm, cmp: $M.cmp key
    ) :<> void = let
    var res: itm
  in
    if :(res: itm?) => $M.linmap_insert (m, k0, x0, cmp, res) then () where {
      prval () = opt_unsome {itm} (res)
    } else () where {
      prval () = opt_unnone {itm} (res)
    } // end of [if]
  end // end of [linmap_replace]

  // [explore] and [goto] realize depth-first traversal of a directed (cyclic) graph
  // in: qid = lookup (qs, env.q)
  fun explore (env: &ENV, q: RE, qid: size_t): void = let
    fun loop {n:nat} .<n>. (env: &ENV, q: RE, qid: size_t, css: list_vt (charset, n)): void =
      case+ css of
      | ~list_vt_cons (cs, rcss) => begin
          goto (env, q, qid, cs);
          loop (env, q, qid, rcss)
        end
      | ~list_vt_nil () => ()
    // end of [loop]
    val () = if re_is_emp q then env.f := list_vt_cons (qid, env.f)
  in
    loop (env, q, qid, re_factoring q)
  end // end of [explore]

  // in: qid = lookup (env.qs, q)
  and goto (env: &ENV, q: RE, qid: size_t, cs: charset): void = let
    var c: char // uninitialized
    val b = charset_extract (cs, c)
  in
    if b then let
      val qc = re_deriv (q, c)
    in
      if ~re_is_phi qc then let // skip error states
        var q': size_t
      in
        if :(q': size_t?) => $M.linmap_search (env.qs, qc, cmp, q') then let
          prval () = opt_unsome {size_t} (q')
        in
          linmap_replace<(size_t, charset), size_t> (env.sig, (qid, cs), q', cmp2)
        end else let
          prval () = opt_unnone {size_t} (q')
        in
          // add new state associated to [qc]
          env.id := env.id+1;
          linmap_replace<RE, size_t> (env.qs, qc, env.id, cmp);
          // add transition from the old state to the new one
          linmap_replace<(size_t, charset), size_t> (env.sig, (qid, cs), env.id, cmp2);
          explore (env, qc, env.id)
        end // end of [if]
      end // end of [if ~re_is_phi ...]
    end // end of [if b ...]
  end // end of [goto]

  val start = size1_of_int1 0
  var env = @{
    qs= $M.linmap_make_nil {RE, size_t} ()
  , sig= $M.linmap_make_nil {@(size_t, charset), size_t} ()
  , f= list_vt_nil ()
  , id= size1_of_int1 0
  }
  val () = linmap_replace<RE, size_t> (env.qs, r, start, cmp)
  val () = explore (env, r, start)
in '{
  states= $M.linmap_listize_free<RE, size_t> (env.qs)
  // by our numbering scheme, initial state is always 0
, start= size1_of_int1 0
, accept= env.f
, trans= $M.linmap_listize_free<@(size_t, charset), size_t> (env.sig)
}
end

(* ****** ****** *)

implement dfa_free (d) = let
  val '{states= s, accept= a, trans= t, ...} = d
  typedef S = @(RE, size_t)
  typedef T = @(@(size_t, charset), size_t)
in
  list_vt_free<S> (s);
  list_vt_free<T> (t);
  list_vt_free<size_t> (a)
end

(* ****** ****** *)

implement print_dfa (d) = let
  val () = print "printing DFA:\n"
  val () = print "states:\n"
  typedef S = @(RE, size_t)
  typedef T = @(@(size_t, charset), size_t)
  val () = list_vt_foreach_fun<S> (d.states, lam x =<fun1> begin
    print "id: "; print x.1; print " "; print x.0; print_newline ()
  end)
  val () = print "accepting:\n"
  val () = list_vt_foreach_fun<size_t> (d.accept, lam x =<fun1> begin
    print x; print_newline ()
  end)
  val () = print "transitions:\n"
  val () = list_vt_foreach_fun<T> (d.trans, lam x =<fun1> begin
    print "id: "; print (x.0).0; print ", ";
    print (x.0).1; print " -> "; print x.1;
    print_newline ()
  end)
in
  (*empty*)
end
