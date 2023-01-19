(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

Require Import Arith Lia Euclid Utf8.

(* P is computationally decidable *)
Definition dec P := { P } + { ¬ P }.

Fact conj_dec (A B : Prop) : dec A → dec B → dec (A∧B).
Proof. unfold dec; tauto. Qed. 

Section minimizer.

  (* Minimization of a decidable and inhabited subset of nat, following
     Constructive Epsilon from the standard library 
   *)

  Variable (P : nat → Prop) (Pdec : ∀n, dec (P n)).

  Let Ω n m := n = S m ∧ ¬ P m.

  Section exP_Acc.

    Let HR1 n : P n → Acc Ω n.
    Proof. constructor; now intros ? (? & []). Qed.

    Let HR2 n : Acc Ω (S n) → Acc Ω n.
    Proof. constructor; now intros ? (-> & _). Qed. 

    Local Fact exP_Acc0 : (∃n, P n) → Acc Ω 0.
    Proof.
      intros (n & Hn%HR1); revert Hn.
      generalize 0 n (Nat.le_0_l n).
      induction 1; auto.
    Qed.

  End exP_Acc.

  (* NB n := P holds Not Before n 
     MIN := first value such that P *)
  Let NB m := ∀i, P i → i < m → False.
  Let MIN := { m | P m ∧ NB m }.

  Let NB_0 : NB 0.
  Proof. now intros _ _ ?%Nat.nlt_0_r. Qed.

  Let NB_S n : NB n → ¬ P n → NB (S n).
  Proof.
    intros H1 H2 i H3 H4%le_S_n.
    destruct H4.
    + apply H2, H3.
    + apply (H1 _ H3), le_n_S, H4.
  Qed.

  Let Fixpoint loop n (an : Acc Ω n) { struct an } : NB n → MIN.
    refine (match Pdec n with
    | left pn  => λ hn, exist _ n _
    | right pn => λ hn, loop (S n) (Acc_inv an _) _
    end); [ | red | ]; auto.
  Qed.

  (** Notice that this "mnimizer" principle cannot be proved by 
      induction on n only unless one assumes { n | P n } instead 
      of the (generally) weaker (∃n, P n). These two are here 
      equivalent because P is decidable over an enumerable type.

      The weaker form { n | P n } → MIN (or equivalently
      ∀n, P n → MIN) can be proved by induction on n and 
      this would be enough as a minimization principle 
      for the proof of √2 below. *)

  Definition minimizer : (∃n, P n) → MIN :=
    λ hn, loop 0 (exP_Acc0 hn) NB_0.

End minimizer.

Definition divides p q := ∃k, k*p = q.

Notation "p 'div' q" := (divides p q) (at level 70).

Fact remainder_is_zero p a b r : r < p → a*p = b*p+r → r = 0.
Proof.
  intros H1 H2.
  assert ((a-b)*p = r) as C.
  + rewrite Nat.mul_sub_distr_r; lia.
  + destruct (a-b); lia.
Qed.

Fact divides_dec p q : dec (p div q).
Proof.
  destruct p as [ | p ].
  + destruct q as [ | q ].
    * left; exists 0; auto.
    * right; intros (k & Hk); now rewrite Nat.mul_comm in Hk.
  + destruct (eucl_dev (S p)) with (m := q)
      as [ x [ | r ] Hr E ]; try lia.
    * left; exists x; lia.
    * right; intros (k & <-).
      apply remainder_is_zero in E; lia.
Qed.

(* Computes the quotient from assumption of divisibility *)
Fact quotient p q : 0 < p → p div q → { x | x*p = q }.
Proof.
  intros H1 H2.
  destruct (eucl_dev _ H1 q) as [ x r H3 H4 ].
  exists x.
  destruct H2 as (k & <-).
  generalize (remainder_is_zero _ _ _ _ H3 H4); lia.
Qed.

Section sqrt2.

  (** We assume a fraction p/q "equal" to √2, ie of which the square is 2 *)
  Variables (p q : nat) (Hq : 0 < q) (Hpq : p*p = 2*q*q).

  (** Below, we manipulate √2 in nat as p/q *)

  Let Hp : 0 < p.
  Proof. destruct p; lia. Qed.

  (* REMARKS & QUESTIONS: 
       1) we can replace the minimizer 
            ∀P, dec P → (∃n, P n) → { m | P m ∧ ∀i, P i → i < m → False }
          with the weaker form
            ∀P, dec P → ∀n, P n → { m | P m ∧ ∀i, P i → i < m → False }
          and the below proof would still work.
       2) the weaker minimizer can be proved by (strong) induction on n
       3) can we replace the use of the minimizer directly with strong
          induction on the proof below ? *)

  (** Let us build k minimal such that k√2 is strictly positive integer *)

  Let Q k := 0 < k ∧ q div k*p. 

  Let k_full : { k | Q k ∧ ∀i, Q i → i < k → False }.
  Proof.
    apply minimizer.
    + intro; apply conj_dec; [ apply lt_dec | apply divides_dec ].
    + exists q; split; auto.
      exists p; ring.
  Qed.

  Let k := proj1_sig k_full.

  Let Hk0 : 0 < k.
  Proof. apply (proj2_sig k_full). Qed.

  (* k√2 is integer *)
  Let Hk1 : q div k*p.
  Proof. apply (proj2_sig k_full). Qed.

  (* k is minimal for 0 < k and k√2 integer *)
  Let Hk2 : ∀i, Q i → i < k → False.
  Proof. apply (proj2_sig k_full). Qed.

  (** Let us build d = k√2 = kp/q *)

  Let d_full : { d | d*q = k*p }.
  Proof. now apply quotient. Qed.

  Let d := proj1_sig d_full.

  (* d = k√2 *)
  Let Hd0 : d*q = k*p.
  Proof. apply (proj2_sig d_full). Qed.

  (* d² = 2k² *)
  Let Hd1 : d*d = 2*k*k.
  Proof.
    rewrite <- Nat.mul_cancel_r with (p := q); try lia.
    rewrite <- (Nat.mul_assoc d), Hd0, Nat.mul_comm.
    rewrite <- Nat.mul_cancel_r with (p := q); try lia.
    rewrite <- (Nat.mul_assoc _ d), Hd0.
    rewrite (Nat.mul_comm k) at 2.
    rewrite Nat.mul_assoc, <- (Nat.mul_assoc k p), Hpq.
    ring.
  Qed.

  (* d is strictly larger than k *)
  Let Hd2 : k < d.
  Proof.
    destruct (le_lt_dec d k); auto.
    assert (2*k*k <= k*k) as C; try lia.
    rewrite <- Hd1.
    now apply Nat.mul_le_mono.
  Qed.

  (** Now we consider k' := k√2-k = k(√2-1) *)

  Let k' := d-k.

  (* k' is strictly below k *)
  Let Hk1' : k' < k.
  Proof.
    destruct (le_lt_dec k k') as [ C | ]; auto.
    apply Nat.mul_le_mono_l with (p := k) in C.
    unfold k' in C; rewrite !Nat.mul_sub_distr_l in C.
    lia.
  Qed.

  (* k' satisfies Q *)
  Let Hk2' : Q k'.
  Proof.
    split; unfold k'.
    + lia.
    + exists (2*k-d).
      unfold k'.
      rewrite !Nat.mul_sub_distr_r.
      f_equal; auto.
      rewrite <- Nat.mul_cancel_r with (p := d); try lia.
      rewrite <- !Nat.mul_assoc, (Nat.mul_comm q), Hd0, !Nat.mul_assoc, <- Hd1.
      ring.
  Qed.

  (* By minimality of k, we get a contradiction *)
  Theorem sqrt2_nat_false : False.
  Proof. exact (Hk2 _ Hk2' Hk1'). Qed.

  (** Concluding remarks: the above proof works as
      well (and nearly as is) for √3 but fails for eg √5.
      This is because while we have 1 < √2 (or √3) < 2, 
      √5 > 2 does not enjoy this property.

      Can we upgrade so proof to deal with √u where u is
      not a square integer? For instance, can we use this 
      proof to show √u = p/q (ie p² = uq²) to imply that
      there is r st u = r² ? 

      Can this even be upgraded to an algorithm for 
      computing the square root ? *) 

End sqrt2.

Check sqrt2_nat_false.
