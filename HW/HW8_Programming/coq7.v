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
Print LoadPath.
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
Lemma add_same: forall (n m a: nat), n = m -> n + a = m + a.
Proof.
    intros n m a H.
    rewrite H.
    reflexivity.
Qed.

Lemma mul_same: forall (n m a: nat), n = m -> a * n = a * m.
Proof.
    intros n m a H.
    rewrite H.
    reflexivity.
Qed.

Lemma or_reduce: forall (a: Prop), a \/ a -> a.
Proof.
    intros a H.
    destruct H as [H1 | H2].
    - assumption.
    - assumption.
Qed.

Theorem main_thm: forall (n p : nat), n * n = double (p * p) ->  p = 0.
Proof.
    intros n p H.
    generalize dependent p.
    apply lt_wf_ind.
    - assumption.
    - intros k IH.
      destruct n as [ | [ | ]].
      + intros p H.
        unfold double in H.
        ring_simplify in H.
        symmetry in H.
        destruct Nat.eq_mul_0 with (n := p) (m := p) as [Hf Hb] in H.
        apply or_reduce in Hf.
        * assumption.
        * rewrite <- Nat.mul_assoc in H.
          apply Nat.eq_mul_0 with (n := 2) (m := p * p) in H.
          destruct H as [H | H].
          ++ discriminate H.
          ++ assumption.
      + intros p H.
        apply False_ind.
        unfold double in H.
        ring_simplify in H.
        symmetry in H.
        rewrite <- Nat.mul_assoc in H.
        apply Nat.eq_mul_1 with (n := 2) (m := p * p) in H.
        destruct H as [Hcontr H].
        discriminate Hcontr.
      + intros p H.
        Sibal.
Qed.