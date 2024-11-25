(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Pythagorean Theorem

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/handin/<HemosID>/.  
 *)

Require Import Arith.
  (* You may use 'auto with arith'. *)
Require Import ArithRing.
  (* You may use the 'ring' tactic. *)
(*
Require Import Div2.
Require Import Even.
*)
Require Import Nat.
Require Import Wf_nat.
(* 
  The goal of this assignment is to prove the following theorem: 

    Theorem main_thm: forall (n p : nat), n * n = double (p * p) ->  p = 0.

  The function double is defined in the Div2 library. 

  For this assignment, you may use ***any*** library provided by Coq.  For
  example, the sample solution makes extensive use of the definitions and
  lemmas in the Div2 and Even libraries.  You may use other lemmas in the Div2
  and Even libraries if you find them useful in completing the proof.  You may
  also introduce additional lemmas if necessary. 

  Below we list those lemmas in the Div2 and Even libraries that the sample
  solution uses. 
 *)

(*
  The Div2 library defines:

  Fixpoint div2 
  Definition double 

  Lemma double_S : forall n, double (S n) = S (S (double n)).
  Lemma even_double : forall n, even n -> n = double (div2 n).
  Lemma double_even : forall n, n = double (div2 n) -> even n.
  Lemma lt_div2 : forall n, 0 < n -> div2 n < n.
  Lemma even_odd_double :
    forall n, (even n <-> n = double (div2 n)) /\ (odd n <-> n = S (double (div2 n))).
 *)

(*
  The Even library defines:

  Inductive even
  Inductive odd

  Lemma even_or_odd : forall n, even n \/ odd n.
  Lemma even_mult_inv_r : forall n m, even (n * m) -> odd n -> even m.
  Lemma even_mult_inv_l : forall n m, even (n * m) -> odd m -> even n.
  Lemma not_even_and_odd : forall n, even n -> odd n -> False.
 *)

(** 

Here are a few tactics that you may find useful.  

1. <tactic_1>; try solve <tactic_2> 

Suppose that <tactic_1> creates many subgoals some of which can be immediately
solved by <tactic_2>.  You could use <tactic_2> for each subgoal as follows:

  <tactic_1>.
  <tactic_2>  (* if the first subgoal is solved by <tactic_2>. *)
  <tactic_2>  (* if the second subgoal is solved by <tactic_2>. *)
  ... (a sequence of tactics) ... 
              (* the third subgoal is not solved by <tactic_2>, so we prove it separately. *)
  <tactic_2>  (* if the fourth subgoal is solved by <tactic_2>. *)
 
In the above example, using 

  <tactic_1>; try solve <tactic_2>

leaves only the second subgoal because all other subgoals are immdiately solved
by <tactic_2>.  Those subgoals that cannot be solved by <tactic_2> are left
intact.

2. remember <composite term> as <term variable> 

Suppose that you want to apply induction on a composite term, like 'tm_to_nat
t1'.  Once you apply induction, Coq performs case analysis on 'tm_to_nat t1',
introducing many terms that 'tm_to_nat t1' can expand to, like 'tm_true',
'tm_false', etc.  Coq, however, forgets that these terms originate from
'tm_to_nat t1', and sometimes you need to keep this information in order to
complete the proof.  In such a case, you want to remember that the term that
has been analyzed is 'tm_to_nat t1', which can be done by using the 'remember'
tactic. 

In the following example, we destruct term 'tm_to_nat t1' but also remember
that the term under analysis is indeed 'tm_to_nat t1'. 

  remember (tm_to_nat t1) as tt1.
  destruct tt1.

Please see the documentation on Coq for more details on this tactic.

3. subst

The tactic 'subst' exploits equalities in hypotheses to simplify all hypotheses
and goals. It is useful when there are lots of equality hypotheses that make it
difficult to read the relations between hypotheses and goals. 

Please see the documentation on Coq for more details on this tactic.
 *)

(*
  Some of the tactics that the sample solution uses:
    simpl
    unfold 
    auto, eauto
    ring
    remember 
    rewrite 
    destruct

  Examples of using some of these tactics in the sample solution: 
    remember (S m) as n.
    destruct (even_or_odd n) as [H1 | H2].
 *) 


(*
(** two properties of div2 and double *)

Theorem double_div2: forall (n : nat),  div2 (double n) = n.
Proof.
Qed.

Theorem double_inv: forall (n m : nat), double n = double m ->  n = m.
Proof.
Qed.

(** if n * n is even, then n is even *)

Theorem even_is_even_times_even: forall (n : nat), even (n * n) ->  even n.
Proof.
Qed.

(** if n is even, we have 4 * (n/2) * (n/2) = n * n. *)

Theorem even_square:
 forall (n : nat), even n ->  double (double (div2 n * div2 n)) = n * n.
 Proof.
 Qed.
  *)

(** main theorem: if n^2 = 2 * p^2, then p = 0. *) 
 
(*
  You should use complete induction on n to complete the proof.
  To use complete induction, use lt_wf_ind in the Wf_nat library. 

  Lemma lt_wf_ind :
    forall n (P:nat -> Prop), (forall n, (forall m, m < n -> P m) -> P n) -> P n.

  Alternatively you may prove the following lemma, where induction on m automatically
  performs complete induction on n.

Lemma main_thm_aux: forall (m : nat) (n : nat), 
  n < m 
  -> forall p, n * n = double (p * p) ->  p = 0.
Proof.
induction m.
...

  The instructor encourages students to try both approaches.
*)

Lemma mul_le : forall (n m a : nat), n <= m -> n * a <= m * a.
Proof.
  intros n m a H.
  induction a.
  - rewrite -> Nat.mul_0_r.
    apply Nat.le_0_l. 
  - rewrite -> Nat.mul_succ_r.
    rewrite -> Nat.mul_succ_r.
    apply Nat.add_le_mono.
    + apply IHa.
    + assumption.
Qed.

Lemma mul_same: forall (n m a: nat), a <> 0 -> n = m <-> a * n = a * m.
Proof.
    intros n m a H.
    split.
    - intro Heq.
      rewrite -> Heq.
      reflexivity.
    - intro Hml.
      apply Nat.mul_cancel_l with (p := a).
      + assumption.
      + assumption.
Qed.

Lemma mul_const_zero: forall (n m: nat), n * m = 0 -> n <> 0 -> m = 0.
Proof.
    intros n m H1 H2.
    destruct m.
    - reflexivity.
    - destruct n.
      + apply False_ind.
        apply H2.
        reflexivity.
      + discriminate H1.
Qed.

Lemma sqr_eq_0: forall (n: nat), n * n = 0 -> n = 0.
Proof.
    intros n H.
    destruct n.
    - reflexivity.
    - apply mul_const_zero with (n := S n) (m := S n) in H.
      + assumption.
      + apply Nat.neq_succ_0.
Qed.

Lemma even_odd_diff: forall (e o: nat), Nat.Even e -> Nat.Odd o -> e = o -> False.
Proof.
    intros n m HE HO Hf.
    apply Nat.Even_Odd_False with (x := n).
    - assumption.
    - rewrite -> Hf.
      assumption.
Qed.

Lemma mul_is_monotonic: forall (n k: nat), k <> 0 -> n <= k * (n).
Proof.
  intros n k H.
  induction k.
  - apply False_ind.
    apply H.
    reflexivity.
  - rewrite -> Nat.mul_comm.
    rewrite -> Nat.mul_succ_r.
    rewrite -> Nat.add_comm.
    apply Nat.le_add_r.
Qed.


Lemma square_even_then_root_even: forall n: nat, Nat.Even (n * n) -> Nat.Even n.
Proof.
  intros n H.
  destruct (Nat.Even_or_Odd n) as [He | Ho].
  - assumption.
  - apply False_ind.
    + apply Nat.Even_Odd_False with (x := n * n).
      * assumption.
      * apply Nat.Odd_mul with (n := n) (m := n) in Ho.
        -- assumption.
        -- assumption.
Qed.

Lemma mul_is_strictly_monotonic: forall (n k: nat), n <> 0 -> k <> 0 -> k <> 1 -> n < k * n.
Proof.
  intros n k N0 H0 H1.
  destruct k as [|[|m]].
  - apply False_ind.
    apply H0.
    reflexivity.
  - apply False_ind.
    apply H1.
    reflexivity.
  - replace n with (1 * n) at 1 by ring.
    apply Nat.mul_lt_mono_pos_r.
    + destruct Nat.eq_0_gt_0_cases with (n := n).
      * apply False_ind.
        apply N0.
        assumption.
      * assumption.
    + apply Nat.lt_pred_lt_succ.
      apply Nat.lt_0_succ.
Qed.


Lemma div2_even_mul2: forall n: nat, Nat.Even n -> 2 * (div2 n) = n.
Proof.
  intros n H.
  destruct H as [k Hk].
  rewrite Hk.
  rewrite -> Nat.div2_double.
  reflexivity.
Qed.

Lemma mul_is_monotonic': forall (n: nat), n <> 0 -> n < 2 * n.
Proof.
  intros n H.
  induction n.
  - simpl.
    apply False_ind.
    apply H.
    reflexivity.
  - rewrite -> Nat.mul_comm.
    rewrite -> Nat.mul_succ_r.
    rewrite -> Nat.add_comm.
    replace ((S n) * 1) with (S n) by ring.
    apply Nat.lt_add_pos_r.
    apply Nat.lt_0_succ.
Qed.

Lemma succ_minus_1: forall (n: nat), n = S n - 1.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    reflexivity.
Qed.

Lemma main_thm_aux: forall (m : nat) (n : nat), n < m -> forall p, n * n = double (p * p) ->  p = 0.
Proof.
  induction m.
    - intros n H p Hf.
      apply False_ind.
      rewrite -> Nat.lt_nge in H.
      apply H.
      apply Nat.le_0_l.
    - intros n H p Hf.
      destruct n.
      + simpl in Hf.
        unfold double in Hf.
        ring_simplify in Hf.
        apply sqr_eq_0.
        apply mul_same with (a := 2).
        * apply Nat.neq_succ_0.
        * ring_simplify.
        symmetry.
        assumption.
      + destruct (Nat.Even_or_Odd (S n)) as [HE | HO].
        * destruct HE as [k HEqv].
          remember (S n) as n'.
          assert (Hn'z: 0 < n'). {
            rewrite -> Heqn'.
            apply Nat.lt_0_succ.
          }
          assert (Hkn: k < n'). {
            rewrite -> HEqv.
            apply mul_is_monotonic'.
            unfold not.
            intro Hk0.
            rewrite -> Hk0 in HEqv.
            ring_simplify in HEqv.
            rewrite -> HEqv in Heqn'.
            discriminate Heqn'.
          }
          rewrite -> HEqv in Hf.
          unfold double in Hf.
          rewrite -> Nat.mul_assoc in Hf.
          ring_simplify in Hf.
          replace (4 * k * k) with (2 * (2 * k * k)) in Hf by ring.
          replace (2 * p * p) with (2 * (p * p)) in Hf by ring.
          rewrite -> Nat.mul_cancel_l with (p := 2) in Hf.

          assert (Hpeven: Nat.Even p). {
            apply square_even_then_root_even.
            rewrite <- Hf.
            exists (k * k).
            ring.
          }

          remember (div2 p) as l.

          assert (Hl2: 2 * l = p). {
            rewrite -> Heql.
            apply div2_even_mul2.
            assumption.
          }

          assert (Hne: Nat.Even n'). {
            rewrite -> HEqv.
            exists k.
            reflexivity.
          }

          rewrite <- Hl2 in Hf.
          rewrite -> Nat.mul_assoc in Hf.
          ring_simplify in Hf.

          replace (4 * l * l) with (2 * (2 * l * l)) in Hf by ring.
          replace (2 * k * k) with (2 * (k * k)) in Hf by ring.
          rewrite -> Nat.mul_cancel_l with (p := 2) in Hf.

          rewrite <- Hl2.
          replace 0 with (2 * 0) at 2 by ring.
          rewrite <- mul_same. 
          apply IHm with (n := k) (p := l).
          
          apply Nat.le_lt_trans with (n := k) (m := 2 * k - 1) (p := m).
          
          rewrite <- HEqv.
          rewrite -> Heqn'.
          rewrite <- succ_minus_1.
          apply Nat.lt_succ_r.
          rewrite <- Heqn'.
          apply Hkn.

          rewrite <- HEqv.
          rewrite -> Heqn'.
          rewrite <- succ_minus_1.
          rewrite -> Heqn' in H.
          rewrite -> Nat.succ_lt_mono.
          apply H.
          
          unfold double.
          replace (l * l + l * l) with (2 * l * l) by ring.
          apply Hf.

          apply Nat.neq_succ_0.
          apply Nat.neq_succ_0.
          apply Nat.neq_succ_0.
          
        * apply False_ind.
          apply even_odd_diff with (o := (S n) * (S n)) (e := (double (p * p))).
          --  exists (p * p).
              unfold double.
              ring_simplify.
              reflexivity.
          --  apply Nat.Odd_mul.
              ++  assumption.
              ++  assumption.
          --  symmetry in Hf.
              assumption.
Qed.


Theorem main_thm: forall (n p : nat), n * n = double (p * p) ->  p = 0.
Proof.
  intros n p H.
  destruct (Nat.lt_trichotomy n p) as [Hlt | [Heq | Hgt]].
  - apply main_thm_aux with (m := p) (n := n) (p := p).
    + apply Hlt.
    + assumption.
  - rewrite -> Heq in H.
    unfold double in H.
    rewrite Nat.add_cancel_r with (n := 0) (m := (p * p)) (p := (p * p)) in H.
    apply sqr_eq_0.
    symmetry.
    assumption. 
  - rewrite -> mul_same with (a := n).
    ring_simplify.
    replace (n * n * p) with (n * p * n) by ring.
    apply main_thm_aux with (m := n * n * n) (n := 2 * p * p) (p := n * p).
    + unfold double in H.
      ring_simplify in H.
      rewrite <- H.
      rewrite <- Nat.mul_assoc.

      assert (HEvenNN: Nat.Even (n * n)). {
        exists (p * p).
        ring_simplify.
        assumption.
      }

      assert (HEvenN: Nat.Even n). {
        apply square_even_then_root_even.
        assumption.
      }
      
      assert (HNnot0: n <> 0). {
        unfold not.
        intro Hf.
        rewrite -> Hf in Hgt.
        apply Nat.nlt_0_r with (n := p).
        assumption.
      }

      apply mul_is_strictly_monotonic with (k := n) (n := (n * n)).
      * unfold not.
        intro Hf.
        apply sqr_eq_0 in Hf.
        apply HNnot0.
        assumption.
      
      * assumption.

      * unfold not.
        intro Hf.
        apply Nat.Even_Odd_False with (x := n).
        --  assumption.
        --  exists 0.
            simpl.
            assumption.

    + unfold double.
      unfold double in H.
      ring_simplify.
      replace (2 * p * p * n * n) with (2 * p * p * (n * n)) by ring.
      ring_simplify in H.
      rewrite -> H.
      ring_simplify.
      reflexivity.
    + unfold not.
      intro Hf.
      rewrite -> Hf in Hgt.
      apply Nat.nlt_0_r with (n := p).
      assumption.
Qed.