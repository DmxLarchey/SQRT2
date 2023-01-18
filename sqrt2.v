(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

Require Import Arith Lia Euclid.

Section minimizer.

  (* Minimization of a decidable and inhabited subset of nat, following
     Constructive Epsilon from the standard library *)

  Variable (P : nat -> Prop) (Pdec : forall n, { P n } + { ~ P n }) (HP : ex P).

  Let R n m := n = S m /\ ~ P m.

  Let HR1 n : P n -> Acc R n.
  Proof. constructor; now intros ? (? & []). Qed.

  Let HR2 n : Acc R (S n) -> Acc R n.
  Proof. constructor; now intros ? (-> & _). Qed. 

  Let HR : ex P -> Acc R 0.
  Proof.
    intros (n & Hn).
    generalize 0 n (Nat.le_0_l n) (HR1 _ Hn).
    clear n Hn; induction 1; eauto.
  Qed.

  Local Lemma minimizer_from n : Acc R n -> { m | P m /\ n <= m /\ forall i, P i -> i < n \/ m <= i }.
  Proof.
    induction 1 as [ n _ IHn ].
    destruct (Pdec n) as [ H | H ].
    + exists n; repeat split; auto; intros; lia.
    + destruct (IHn (S n)) as (m & H1 & H2 & H3).
      * split; auto.
      * exists m; repeat split; auto; try lia.
        intros i Hi.
        destruct (H3 _ Hi) as [ H4%le_S_n | ]; try lia.
        destruct H4; (easy || lia).
  Qed.

  Theorem minimizer : ex P -> { n | P n /\ forall i, P i -> n <= i }.
  Proof.
    intros H%HR.
    destruct (minimizer_from _ H) as (m & H1 & _ & H2).
    exists m; split; auto.
    intros ? []%H2; lia.
  Qed.

End minimizer.

Definition divides p q := exists k, k*p = q.

Notation "p 'div' q" := (divides p q) (at level 70).

Fact remainder_is_zero p a b r : 
      r < p -> a*p = b*p+r -> r = 0.
Proof.
  intros H1 H2.
  assert ((a-b)*p = r) as C.
  + rewrite Nat.mul_sub_distr_r; lia.
  + destruct (a-b); lia.
Qed.

Fact divides_dec p q : { p div q } + { ~ p div q }.
Proof.
  destruct p as [ | p ].
  + destruct q as [ | q ].
    * left; exists 0; auto.
    * right; intros (k & Hk); now rewrite Nat.mul_comm in Hk.
  + destruct (eucl_dev (S p)) with (m := q)
      as [ x [ | r ] Hr E ]; try lia.
    * left; exists x; lia.
    * right.
      intros (k & <-).
      apply remainder_is_zero in E; lia.
Qed.

Fact conj_dec (A B : Prop) : 
       { A } + { ~ A } -> { B } + { ~ B } -> { A /\ B } + { ~ (A /\ B) }.
Proof. tauto. Qed. 

(* Computes the quotient from assumption of divisibility *)
Fact quotient p q : 0 < p -> p div q -> { x | x*p = q }.
Proof.
  intros H1 H2.
  destruct (eucl_dev _ H1 q) as [ x r H3 H4 ].
  exists x.
  destruct H2 as (k & <-).
  generalize H4; intros ->%remainder_is_zero; lia.
Qed.

Section sqrt2.

  Variables (p q : nat) (Hq : 0 < q) (Hpq : p*p = 2*q*q).

  (* So below, we manipulate √2 in nat as p/q *)

  Let Hp : 0 < p.
  Proof. destruct p; lia. Qed.

   (* Can we replace the use of the minimizer with
      strong induction ?? *)

  Let Q k := 0 < k /\ q div k*p. (* k√2 is integer *)

  Let mini : { k | Q k /\ forall i, Q i -> k <= i }.
  Proof. 
    apply minimizer.
    + intro i; unfold Q.
      apply conj_dec.
      * apply lt_dec.
      * apply divides_dec.
    + exists q; split; auto. 
      exists p; ring.
  Qed.

  Let k := proj1_sig mini.

  Let Hk0 : 0 < k.
  Proof. apply (proj2_sig mini). Qed.

  Let Hk1 : q div k*p.
  Proof. apply (proj2_sig mini). Qed.

  Let Hk2 : forall i, Q i -> k <= i.
  Proof. apply (proj2_sig mini). Qed.

  (* Let us build the nat d = k√2 *)

  Let d_full : { x | x*q = k*p }.
  Proof. now apply quotient. Qed.

  Let d := proj1_sig d_full.

  Let Hd0 : d*q = k*p.
  Proof. apply (proj2_sig d_full). Qed.

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

  Let Hd2 : k < d.
  Proof.
    destruct (le_lt_dec d k); auto.
    assert (2*k*k <= k*k) as C; try lia.
    rewrite <- Hd1.
    now apply Nat.mul_le_mono.
  Qed.

  (* Now we consider k' := k√2-k = k(√2-1) *)
  Let k' := d-k.

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

  (* Hence must be greater than k, contradiction *)
  Theorem sqrt2_nat_false : False.
  Proof. apply Hk2 in Hk2'; lia. Qed.

End sqrt2.

Check sqrt2_nat_false.
