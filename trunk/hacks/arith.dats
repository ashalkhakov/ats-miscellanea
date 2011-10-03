(* this file contains solutions of exercises
 * originally intended to be completed in Twelf
 * (see http://twelf.plparty.org/wiki/Proving_metatheorems:Summary:_the_natural_numbers)
 * written by Artyom Shalkhakov on Dec 12, 2010
 *)

// natural numbers: zero and successor operation
datasort Nat = z | s of Nat

// [nat_eq (M, N)] holds iff [M = N]
dataprop nat_eq (Nat, Nat) =
  | nat_eqz (z, z)
  | {N1,N2:Nat} nat_eqs (s N1, s N2) of nat_eq (N1, N2)

dataprop nat_eq_prop (Nat, Nat) = {N:Nat} nat_eq_prop_refl (N, N)

// [plus (N, M, P)] holds iff [N+M = P]
dataprop plus (Nat, Nat, Nat) =
  | {N:Nat} plusz (z, N, N)
  | {N1,N2,N3:Nat} pluss (s N1, N2, s N3) of plus (N1, N2, N3)

// addition is a function
prfun plus_fun {A,B,C,C':Nat} .<A>.
  (pf1: plus (A, B, C), pf2: plus (A, B, C')):<> nat_eq (C, C') =
  case+ pf1 of
  | plusz () => let
      val plusz () = pf2
      extern prfun nat_eq_istot {N:Nat} ():<> nat_eq (N, N)
    in
      nat_eq_istot ()
    end
  | pluss pf1 => let
      val pluss pf2 = pf2
    in nat_eqs (plus_fun (pf1, pf2)) end

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

(* ****** ****** *)
// propositional equality on naturals

// equality is total (reflexive)
// (also an introduction rule)
prfun nat_eq_istot {N:Nat} .<N>. ():<> nat_eq (N, N) = scase N of
  | z () => nat_eqz ()
  | s (N') => nat_eqs (nat_eq_istot {N'} ())
 
prfun nat_eq_elim {N1,N2:Nat} .<N1>. (
    pf: nat_eq (N1,N2)
  ):<> nat_eq_prop (N1, N2) = case+ pf of
  | nat_eqz () => nat_eq_prop_refl ()
  | nat_eqs pf => let
      val+ nat_eq_prop_refl () = nat_eq_elim pf
    in
      nat_eq_prop_refl ()
    end // end of [nat_eq_elim]

// equality is symmetric: a=b <-> b=a
prfun nat_eq_symm {N1,N2:Nat} .<N1>. (
    pf: nat_eq (N1, N2)
  ):<> nat_eq (N2, N1) = case+ pf of
  | nat_eqz () => nat_eqz ()
  | nat_eqs pf => nat_eqs (nat_eq_symm pf)

// equality is transitive: a=b -> b=c -> a=c
prfun nat_eq_trans {N1,N2,N3:Nat} .<N1>. (
    pf1: nat_eq (N1, N2), pf2: nat_eq (N2, N3)
  ):<> nat_eq (N1, N3) = case+ pf1 of
  | nat_eqz () => pf2
  | nat_eqs pf1 => let
      val+ nat_eqs pf2 = pf2
    in
      nat_eqs (nat_eq_trans (pf1, pf2))
    end // end of [nat_eq_trans]

// injectivity of successor
prfun succ_inj {A,B:Nat} .<A>. (pf: nat_eq (s A, s B)):<> nat_eq (A, B) =
  case+ pf of nat_eqs pf' => pf'

// addition of some constant is injective
prfun plus_inj {K,A,B,X:Nat} .<K>. (
    pf1: plus (K, A, X)
  , pf2: plus (K, B, X)
  ):<> nat_eq (A, B) = case+ (pf1, pf2) of
  | (plusz (), plusz()) => nat_eq_istot ()
  | (pluss pf1, pluss pf2) => plus_inj (pf1, pf2)
// end of [plus_inj]

dataprop disj (a: prop, b: prop) =
  | inl (a, b) of a
  | inr (a, b) of b

// forall y. y=0 \/ exists x. Sx = y
prfun lemma0 {A:Nat} .< >. (): disj (nat_eq (A, z), [B:Nat] nat_eq (s B, A)) =
  scase A of
  | z () => inl (nat_eqz ())
  | s (B) => inr (nat_eq_istot {A} ())

// a+b=Z -> a=Z ^ b=Z
prfun lemma1 {A,B:Nat} .<A>. (pf: plus (A, B, z)):<> (nat_eq (A, z), nat_eq (B, z)) =
  case+ pf of
  | plusz () => (nat_eq_istot {A} (), nat_eq_istot {B} ())
  | pluss pf => lemma1 pf

// x+y=z+y -> x=z
// y+x=y+z -> x=z
prfun plus_left_cancel {A,B1,B2,C:Nat} .<A>. (
    pf1: plus (A, B1, C)
  , pf2: plus (A, B2, C)
  ):<> nat_eq (B1, B2) = case+ (pf1, pf2) of
  | (plusz (), plusz ()) => nat_eq_istot {C} ()
  | (pluss pf1, pluss pf2) => plus_left_cancel (pf1, pf2)
prfun plus_right_cancel {A1,A2,B,C:Nat} .< >. (
    pf1: plus (A1, B, C)
  , pf2: plus (A2, B, C)
  ):<> nat_eq (A1, A2) = let
  prval pf1' = plus_comm pf1 and pf2' = plus_comm pf2
in
  plus_left_cancel (pf1', pf2')
end

prfun succ_assoc {A,B,C:Nat} .< >. (pf: plus (s A, B, s C)):<> plus (A, s B, s C) = let
  prval pluss pf' = pf
in
  // plus (s A, B, s C)
  //  plus (A, B, C) (un-pluss)
  //  plus (B, A, C) (plus_comm)
  //  plus (s B, A, s C) (pluss)
  //  plus (A, s B, s C) (plus_comm)
  // plus (A, s B, C)
  plus_comm (pluss (plus_comm pf'))
end // end of [succ_assoc]

prfun plus_associate {X,Y,Z:Nat} {XY,YZ,XY_Z,X_YZ:Nat} .<X>. (
    pf1: plus (X, Y, XY)
  , pf2: plus (Y, Z, YZ)
  , pf3: plus (XY, Z, XY_Z)
  , pf4: plus (X, YZ, X_YZ)
  ) :<prf> nat_eq (XY_Z, X_YZ) = case+ (pf1, pf4) of
  | (plusz (), plusz ()) => let
      prval pf = plus_fun (pf2, pf3)
      prval nat_eq_prop_refl () = nat_eq_elim (pf)
    in
      nat_eq_istot () // X=z, so XY=Y, X_YZ=YZ and XY_Z=Y+Z=YZ
    end
  | (pluss pf1, pluss pf4) => let // X=s X'
      // pf1: plus (s X', Y, XY)
      // pf3: plus (XY, Z, XY_Z)
      prval pluss pf3 = pf3
      prval pf = plus_associate (pf1, pf2, pf3, pf4)
// plus (X', Y, X'Y) -- have
// plus (Y, Z, YZ)
// plus (X'Y, Z, X'Y_Z) -- infer from pf3
// plus (X', YZ, X'_YZ) -- have
// then a recursive call to infer nat_eq (X'Y_Z, X'_YZ)
// nat_eqs to the proof of nat_eq (X'Y_Z, X'_YZ)
     in
       nat_eqs pf
     end // end of [plus_associate]

(* ****** ****** *)
(* less-than relation on naturals *)

dataprop lte (Nat, Nat) =
  | {A:Nat} ltez (A, A)
  | {A,B:Nat} ltes (A, s B) of lte (A, B)

prfun lte_trans {A,B,C:Nat} .<B>. (
    pf1: lte (A, B)
  , pf2: lte (B, C)
  ):<> lte (A, C) = case+ pf1 of
  | ltez () => pf2 // pf1 : lte (A, A) where A=B
  | ltes pf1' => begin // pf1' : lte (A, B') where B=s B'
      case+ pf2 of
      | ltez () => pf1 // pf2 : lte (B, B) where C=B
      | ltes pf2' => let // pf2' : lte (B, C') where C=s C'
          prfun lemma {A,B:Nat} .<B>. (pf: lte (s A, B)):<> lte (A, B) =
            case+ pf of
            | ltez () => ltes (ltez ())
            | ltes pf => ltes (lemma pf)
          // end of [lemma]
        in
          ltes (lte_trans (pf1', lemma pf2'))
        end // end of [lte_trans]
    end

prfun eq_to_lte {A,B:Nat} .< >. (pf: nat_eq (A, B)):<> lte (A, B) = let
  prval nat_eq_prop_refl () = nat_eq_elim pf
in
  ltez ()
end // end of [eq_to_lte]

// another representation for lte:
// a <= b iff exists c. a+c=b
propdef lte_p (a:Nat, b:Nat) = [c:Nat] plus (c, a, b)
prfun lemma {A,B:Nat} .<B>. (pf: lte (A, B)):<> lte_p (A, B) =
  case+ pf of
  | ltez () => plusz ()
  | ltes pf => pluss (lemma pf)
prfun lemma_2 {A,B:Nat} .<B>. (pf: lte_p (A, B)):<> lte (A, B) =
  case+ pf of
  | plusz () => ltez ()
  | pluss pf => ltes (lemma_2 pf)

// a <= b -> a+c <= b+c
// rewritten: forall a,b,c. exists k. a+k=b -> (a+c)+k = (b+c)
//            plus(k,a,b) -> plus(k,a+c,b+c)
prfun lte_plus_stable {A,B,C:Nat} {X,Y:Nat} .<B>. (
    pf1: lte (A, B)
  , pf2: plus (A, C, X), pf3: plus (B, C, Y)
  ):<> lte (X, Y) = case+ pf1 of
  | ltez () => let
      prval nat_eq_prop_refl () = nat_eq_elim (plus_fun (pf2, pf3))
      prval nat_eq_prop_refl () = nat_eq_elim (plus_left_cancel (pf2, pf3))
    in
      ltez ()
    end
  | ltes pf1 => let
      prval pluss pf3 = pf3
    in
      ltes (lte_plus_stable (pf1, pf2, pf3))
    end // end of [lte_plus_stable]

(*

prfun lte_eq {A,B:Nat} (
  pf1: lte (A, B), pf2: lte (B, A)
):<> nat_eq (A, B)

*)
