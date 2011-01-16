(* this file contains solutions of exercises
 * originally intended to be completed in Twelf
 * (see http://twelf.plparty.org/wiki/Proving_metatheorems:Summary:_the_natural_numbers)
 * written by Artyom Shalkhakov on Dec 12, 2010
 *)

// natural numbers: zero and successor operation
datasort Nat = z | s of Nat

// propositional equality on naturals
dataprop nat_eq (Nat, Nat) = {N:Nat} nat_eq_refl (N, N)

// [plus (N, M, P)] holds iff [N+M = P]
dataprop plus (Nat, Nat, Nat) =
  | {N:Nat} plusz (z, N, N)
  | {N1,N2,N3:Nat} pluss (s N1, N2, s N3) of plus (N1, N2, N3)

// addition is a function
prfun plus_fun {A,B,C,C':Nat} .<A>.
  (pf1: plus (A, B, C), pf2: plus (A, B, C')):<> nat_eq (C, C') =
  case+ pf1 of
  | plusz () => let val plusz () = pf2 in nat_eq_refl () end
  | pluss pf1 => let
      val pluss pf2 = pf2
      val nat_eq_refl () = plus_fun (pf1, pf2)
    in nat_eq_refl () end

// addition is total
prfun plus_tot {N1,N2:Nat} .<N1>. (): [N3:Nat] plus (N1, N2, N3) =
  scase N1 of
  | z () => plusz ()
  | s (N1') => pluss (plus_tot {N1',N2} ())

// addition is commutative
prfun plus_comm {N1,N2,N3:Nat} .<N1>.
  (pf: plus (N1, N2, N3)):<> plus (N2, N1, N3) = let
  // lemma: for any number N, N+0 = N
  prfun plus_comm_z {N2:Nat} .<N2>. ():<> plus (N2, z, N2) = scase N2 of
    | z () => plusz ()
    | s (N2') => pluss (plus_comm_z {N2'} ())
  // lemma: if plus(N1,N2,N3) then plus(N1,s N2, s N3)
  prfun plus_comm_s {N1,N2,N3:Nat} .<N1>.
    (pf: plus (N1, N2, N3)):<> plus (N1, s N2, s N3) = case+ pf of
    | plusz () => plusz ()
    | pluss pf => pluss (plus_comm_s pf)
in
  case+ pf of
  | plusz () => plus_comm_z {N2} ()
  | pluss pf => plus_comm_s (plus_comm pf)
end

// [even N] holds iff [N] is an even number
dataprop even (Nat) =
  | evenz (z)
  | {N:Nat} evens (s (s N)) of even N

// [odd N] holds iff [N] is an odd number
dataprop odd (Nat) =
  | oddz (s z)
  | {N:Nat} odds (s (s N)) of odd N

// successor to an even number is odd
prfun succ_even {N:Nat} .<N>. (pf: even N):<> odd (s N) = case+ pf of
  | evenz () => oddz ()
  | evens pf => odds (succ_even pf)

// successor to an odd number is even
prfun succ_odd {N:Nat} .<N>. (pf: odd N):<> even (s N) = case+ pf of
  | oddz () => evens (evenz ())
  | odds pf => evens (succ_odd pf)

// sum of an even and an odd number is odd
prfun sum_even_odd {N1,N2,N3:Nat} .<N1>.
  (pf1: even N1, pf2: odd N2, pf3: plus (N1, N2, N3)):<> odd N3 = case+ pf1 of
  | evenz () => let prval plusz () = pf3 in pf2 end
  | evens pf => let
      prval pluss (pluss pf3) = pf3
    in
      odds (sum_even_odd (pf, pf2, pf3))
    end

// sum of an odd and an even number is odd
prfun sum_odd_even {N1,N2,N3:Nat} .<N1>.
  (pf1: odd N1, pf2: even N2, pf3: plus (N1, N2, N3)):<> odd N3 = case+ pf1 of
  | oddz () => sum_even_odd (pf2, pf1, plus_comm pf3)
  | odds pf1 => let
      prval pluss (pluss pf3) = pf3
    in
      odds (sum_odd_even (pf1, pf2, pf3))
    end

// sum of two odd numbers is even
prfun sum_odds {N1,N2,N3:Nat} .<N1>.
  (pf1: odd N1, pf2: odd N2, pf3: plus (N1, N2, N3)):<> even N3 = case+ pf1 of
  | oddz () => let
      prval pluss (plusz ()) = pf3
      prval pf4 = succ_odd (pf2)
    in
      pf4
    end
  | odds pf1 => let
      prval pluss (pluss pf3) = pf3
    in
      evens (sum_odds (pf1, pf2, pf3))
    end
