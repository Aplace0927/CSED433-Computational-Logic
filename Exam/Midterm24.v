(**************************************************************)
(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Midterm, Fall 2024

  You may use any tactic/tactical/command and any standard library in Coq. 
  For example, the sample solution uses many lemmas as hints for auto/eauto tactics:

    Hint Constructors bvalue nvalue.
    Hint Resolve value_is_normal_form nvalue_is_normal_form.
    Hint Unfold value normal_form.

  You may also introduce any lemma.

  Remark on 'generalize dependent':
  Feel free to use 'generalize dependent' in your proof, but if you would like to avoid 
  using 'generalize dependent', you can introduce an auxiliary lemma/theorem.  
  For example, suppose that you want to prove 'eval_deterministic'.

Theorem eval_deterministic : forall t t' t'',
  eval t t' ->
  eval t t'' ->
  t' = t''.

  Perhaps you want to apply induction on _eval t t'_, but you also do not want to leave t'' fixed. 
  To avoid the use of 'generalize dependent', you could use the following auxiliary lemma:

Theorem eval_deterministic_aux : forall t t',
  eval t t' ->
  forall t'', 
    eval t t'' ->
    t' = t''.

  It's up to your proof style whether or not to use 'generalize dependent'. 
 *)
(**************************************************************)

(**************************************************************)
(** * Definition of the simple language over natural numbers and booleans *)
(**************************************************************)


(** terms 
*)

Inductive tm : Set :=
| tm_true : tm
| tm_false : tm
| tm_if : tm -> tm -> tm -> tm
| tm_zero : tm
| tm_succ : tm -> tm
| tm_pred : tm -> tm
| tm_iszero : tm -> tm.

(** values
*)

Inductive bvalue : tm -> Prop := 
| b_true : bvalue tm_true 
| b_false : bvalue tm_false.

Inductive nvalue : tm -> Prop :=
| n_zero : nvalue tm_zero
| n_succ : forall t,
    nvalue t ->
    nvalue (tm_succ t).

(* Use 'unfold value' to expand 'value' into its definition. *)
Definition value (t : tm) : Prop :=
  bvalue t \/ nvalue t.

(** small-step semantics 
*)

Inductive eval : tm -> tm -> Prop :=
| e_iftrue : forall t2 t3,
    eval (tm_if tm_true t2 t3) t2
| e_iffalse : forall t2 t3,
    eval (tm_if tm_false t2 t3) t3
| e_if : forall t1 t1' t2 t3,
    eval t1 t1' ->
    eval (tm_if t1 t2 t3) (tm_if t1' t2 t3)
| e_succ : forall t t',
    eval t t' ->
    eval (tm_succ t) (tm_succ t')
| e_predzero :
    eval (tm_pred tm_zero) tm_zero
| e_predsucc : forall t,
    nvalue t ->
    eval (tm_pred (tm_succ t)) t
| e_pred : forall t t',
    eval t t' ->
    eval (tm_pred t) (tm_pred t')
| e_iszerozero :
    eval (tm_iszero tm_zero) tm_true
| e_iszerosucc : forall t,
    nvalue t ->
    eval (tm_iszero (tm_succ t)) tm_false
| e_iszero : forall t t',
    eval t t' ->
    eval (tm_iszero t) (tm_iszero t').

(** normal form
*)

(* Use 'unfold normal_form' to expand 'normal_form' into its definition. *)
Definition normal_form (t : tm) : Prop :=
  ~ exists t', eval t t'.

(**************************************************************)
(** * Deterministic reduction *)
(*
  The goal is to prove eval_deterministic.
  We list some lemmas that are used in the sample solution. 
 *)
(**************************************************************)

Lemma value_is_normal_form : forall v,
  value v ->
  normal_form v.
Proof.
    intros v [HBool | HNat] [t H].
    - destruct HBool; inversion H.
    - generalize dependent t.
      induction HNat; intros n Hn'.
        + inversion Hn'.
        + inversion Hn'.
          subst.
          destruct (IHHNat t').
          assumption.
Qed.

Lemma bvalue_is_normal_form : forall v,
  bvalue v ->
  normal_form v.
Proof.
    intros b H.
    assert (value b). {
        left.
        assumption.
    }
    apply value_is_normal_form.
    assumption.
Qed.

Lemma nvalue_is_normal_form : forall v,
  nvalue v ->
  normal_form v.
Proof.
    intros n H.
    assert (value n). {
        right.
        assumption.
    }
    apply value_is_normal_form.
    assumption.
Qed.

(** * Theorem eval_deterministic *)

Theorem eval_deterministic : forall t t' t'',
  eval t t' ->
  eval t t'' ->
  t' = t''.
Proof.
    intros t t' t'' HEtt' HEtt''.
    generalize dependent t''.
    induction HEtt'; intros t'' E; inversion E; subst.
    - reflexivity.
    - inversion H3.
    - reflexivity.
    - inversion H3.
    - inversion HEtt'.
    - inversion HEtt'.
    - specialize IHHEtt' with (t'' := t1'0).
      apply IHHEtt' in H3.
      subst.
      reflexivity.
    - specialize IHHEtt' with (t'' := t'0).
      apply IHHEtt' in H0.
      subst.
      reflexivity.
    - reflexivity.
    - inversion H0.
    - reflexivity.
    - remember (nvalue_is_normal_form (tm_succ t)) as HsuccN.
      remember (n_succ t H) as HtN.
      destruct HsuccN.
      + assumption.
      + exists t'.
        assumption.
    - inversion HEtt'.
    - remember (nvalue_is_normal_form (tm_succ t'')) as HsuccN.
      remember (n_succ t'' H0) as HtN.
      destruct HsuccN.
      + assumption.
      + exists t'.
        assumption.
    - specialize IHHEtt' with (t'' := t'0).
      apply IHHEtt' in H0.
      subst.
      reflexivity.
    - reflexivity.
    - inversion H0.
    - reflexivity.
    - remember (nvalue_is_normal_form (tm_succ t)) as HsuccN.
      remember (n_succ t H) as HtN.
      destruct HsuccN.
      + assumption.
      + exists t'.
        assumption.
    - inversion HEtt'.
    - remember (nvalue_is_normal_form (tm_succ t0)) as HsuccN.
      remember (n_succ t0 H0) as HtN.
      destruct HsuccN.
      + assumption.
      + exists t'.
        assumption.
    - specialize IHHEtt' with (t'' := t'0).
      apply IHHEtt' in H0.
      subst.
      reflexivity.
Qed.

(**************************************************************)
(** * Verifying the interpreter *)
(*
  The goal is to prove interp_reduces and interp_fully_reduces. 
  We list some lemmas that are used in the sample solution. 
 *)
(**************************************************************)

(** multi-step evaluation 
*)

Inductive eval_many : tm -> tm -> Prop :=
| m_refl : forall t,
    eval_many t t
| m_step : forall t t' u,
    eval t t' ->
    eval_many t' u ->
    eval_many t u.

Inductive nat_option : Set :=
| some_nat : nat -> nat_option
| no_nat : nat_option.

Fixpoint tm_to_nat (t : tm) {struct t} : nat_option :=
  match t with
  | tm_zero => some_nat O
  | tm_succ t1 =>
      match tm_to_nat t1 with
      | some_nat n => some_nat (S n)
      | no_nat => no_nat
      end
  | _ => no_nat
  end.

(** returns the normal form of its argument according to the small-step
    semantics given by eval.
*)

Fixpoint interp (t:tm) {struct t} : tm :=
match t with
| tm_true => tm_true
| tm_false => tm_false
| tm_if t1 t2 t3 => 
  match interp t1 with
  | tm_true => interp t2
  | tm_false => interp t3
  | t1' => tm_if t1' t2 t3
  end
| tm_zero => tm_zero
| tm_succ t' => tm_succ (interp t')
| tm_pred t' => 
  match interp t' with
  | tm_zero => tm_zero
  | tm_succ t'' => 
    match tm_to_nat t'' with
    | some_nat _ => t''
    | no_nat => tm_pred (tm_succ t'')
    end
  | t'' => tm_pred t''
  end
| tm_iszero t' => 
  match interp t' with
  | tm_zero => tm_true
  | tm_succ t'' =>
    match tm_to_nat t'' with
    | some_nat _ => tm_false
    | no_nat => tm_iszero (tm_succ t'')
    end
  | t'' => tm_iszero t''
  end
end.

(** * Lemmas *)


Lemma m_one : forall t1 t2,
  eval t1 t2 ->
  eval_many t1 t2.
Proof.
    intros t1 t2 H.
    apply m_step with (t := t1) (t' := t2).
    - assumption.
    - apply m_refl. 
Qed.

Lemma m_trans : forall t t' u,
  eval_many t t' ->
  eval_many t' u ->
  eval_many t u.
Proof.
    intros t t' u H1 H2.
    induction H1.
    - assumption.
    - apply m_step with (t := t) (t' := t') (u := u).
      + assumption.
      + apply IHeval_many.
        assumption.
Qed.

Lemma m_if : forall t1 u1 t2 t3,
  eval_many t1 u1 ->
  eval_many (tm_if t1 t2 t3) (tm_if u1 t2 t3).
Proof.
    intros t1 u1 tT tF H.
    induction H.
    - apply m_refl.
    - apply m_step with (t := (tm_if t tT tF)) (t' := (tm_if t' tT tF)) (u := (tm_if u tT tF)). 
      + apply e_if.
        assumption.
      + assumption.
Qed.

Lemma m_pred : forall t u,
  eval_many t u ->
  eval_many (tm_pred t) (tm_pred u).
Proof.
    intros t u H.
    induction H.
    - apply m_refl.
    - apply e_pred in H. 
        apply m_step with (t := (tm_pred t)) (t' := (tm_pred t')) (u := (tm_pred u)).
        + assumption.
        + assumption.
Qed.

Lemma m_succ : forall t u,
  eval_many t u ->
  eval_many (tm_succ t) (tm_succ u).
Proof.
    intros t u H.
    induction H.
    - apply m_refl.
    - apply e_succ in H.
        apply m_step with (t := (tm_succ t)) (t' := (tm_succ t')) (u := (tm_succ u)).
        + assumption.
        + assumption.
Qed.

Lemma m_iszero : forall t u,
  eval_many t u ->
  eval_many (tm_iszero t) (tm_iszero u).
Proof.
    intros t u H.
    induction H.
    - apply m_refl.
    - apply e_iszero in H.
        apply m_step with (t := (tm_iszero t)) (t' := (tm_iszero t')) (u := (tm_iszero u)).
        + assumption.
        + assumption.
Qed.

Lemma tm_to_nat_dom_only_nvalue : forall v n,
  tm_to_nat v = some_nat n -> nvalue v.
Proof.
    intros v.
    induction v; intros n H.
    - inversion H.
    - inversion H.
    - inversion H.
    - apply n_zero.
    - apply n_succ.
      simpl in H.
      destruct tm_to_nat.
      + inversion H.
        apply IHv with (n := n0).
        reflexivity.
      + apply IHv with (n := n).
        rewrite <- H.
        reflexivity.
    - inversion H.
    - inversion H.
Qed.

Lemma tm_to_nat_dom_only_nvalue_inv : forall v,
  nvalue v -> exists n, tm_to_nat v = some_nat n.
Proof.
    intros v H.
    induction H.
    - exists O.
      reflexivity.
    - destruct IHnvalue.
      exists (S x).
      simpl.
      rewrite -> H0.
      reflexivity.
Qed.

Lemma nat_option_coexists: forall n: nat, some_nat n = no_nat -> False.
Proof.
    intros n H.
    inversion H.
Qed.

Lemma bvalue_cannot_eval : forall t t',
  bvalue t ->
  eval t t' ->
  False.
Proof.
    intros t t' Hb He.
    apply bvalue_is_normal_form in Hb.
    unfold normal_form in Hb.
    apply Hb.
    exists t'.
    assumption.
Qed.

Lemma nvalue_cannot_eval : forall t t',
  nvalue t ->
  eval t t' ->
  False.
Proof.
    intros t t' Hn He.
    apply nvalue_is_normal_form in Hn.
    unfold normal_form in Hn.
    apply Hn.
    exists t'.
    assumption.
Qed.

(** * Theorem interp_reduces *)

Theorem interp_reduces : forall t,
  eval_many t (interp t).
Proof.
    intros t.
    induction t.
    - apply m_refl.
    - apply m_refl.
    - simpl.
      destruct interp.
      + apply m_trans with (t := (tm_if t1 t2 t3)) (t' := (tm_if tm_true t2 t3)) (u := (interp t2)).
        * apply m_if.
          assumption.
        * apply m_trans with (t := (tm_if tm_true t2 t3)) (t' := t2) (u := (interp t2)).
          -- apply m_one.
             apply e_iftrue.
          -- assumption.
      + apply m_trans with (t := (tm_if t1 t2 t3)) (t' := (tm_if tm_false t2 t3)) (u := (interp t3)).
        * apply m_if.
          assumption.
        * apply m_trans with (t := (tm_if tm_false t2 t3)) (t' := t3) (u := (interp t3)).
          -- apply m_one.
             apply e_iffalse.
          -- assumption.
      + apply m_if. 
        assumption.
      + apply m_if.
        assumption.
      + apply m_if.
        assumption.
      + apply m_if.
        assumption.
      + apply m_if.
        assumption.
    - simpl.
      apply m_refl.
    - simpl.
      destruct interp.
      + apply m_succ.
        assumption.
      + apply m_succ.
        assumption.
      + apply m_succ.
        assumption.
      + apply m_succ.
        assumption.
      + apply m_succ.
        assumption.
      + apply m_succ.
        assumption.
      + apply m_succ.
        assumption.
    - simpl.
      destruct interp.
      + apply m_pred.
        assumption.
      + apply m_pred.
        assumption.
      + apply m_pred.
        assumption.
      + apply m_pred in IHt.
        apply m_trans with (t := (tm_pred t)) (t' := (tm_pred tm_zero)) (u := tm_zero).
        * assumption.
        * apply m_one.
          apply e_predzero.
      + remember (tm_to_nat t0) as HN. 
        destruct HN.
        * apply m_pred in IHt.
          apply m_trans with (t := (tm_pred t)) (t' := (tm_pred (tm_succ t0))) (u := t0).
          --  assumption.
          --  apply m_one.
              apply e_predsucc.
              apply tm_to_nat_dom_only_nvalue with (n := n).
              symmetry.
              assumption.
        * apply m_pred in IHt.
          assumption.
      + apply m_pred.
        assumption.
      + apply m_pred.
        assumption.
    - simpl.
      destruct interp.
      + apply m_iszero.
        assumption.
      + apply m_iszero.
        assumption.
      + apply m_iszero.
        assumption.
      + apply m_trans with (t := (tm_iszero t)) (t' := (tm_iszero tm_zero)) (u := tm_true).
        * apply m_iszero.
          assumption.
        * apply m_one.
          apply e_iszerozero.
      + remember (tm_to_nat t0) as HN. 
        destruct HN.
        * apply m_iszero in IHt.
          apply m_trans with (t := (tm_iszero t)) (t' := (tm_iszero (tm_succ t0))) (u := tm_false).
          --  assumption.
          --  apply m_one.
              apply e_iszerosucc.
              apply tm_to_nat_dom_only_nvalue with (n := n).
              symmetry.
              assumption.
        * apply m_iszero in IHt.
          assumption.
      + apply m_iszero.
        assumption.
      + apply m_iszero.
        assumption. 
Qed.

(** * Lemmas *)

(** * Theorem interp_fully_reduces *)

Theorem interp_fully_reduces : forall t,
  normal_form (interp t).
Proof.
  intro t.
  induction t.
  - apply bvalue_is_normal_form.
    apply b_true.
  - apply bvalue_is_normal_form.
    apply b_false.
  - simpl.
    destruct interp; intros [tev Hev].
    + destruct IHt2.
      exists tev.
      assumption.
    + destruct IHt3.
      exists tev.
      assumption.
    + destruct IHt1.
      inversion Hev.
      exists t1'.
      assumption.
    + destruct IHt1.
      inversion Hev.
      exists t1'.
      assumption.
    + destruct IHt1.
      inversion Hev.
      exists t1'.
      assumption.
    + destruct IHt1.
      inversion Hev.
      exists t1'.
      assumption.
    + destruct IHt1.
      inversion Hev.
      exists t1'.
      assumption.
  - apply nvalue_is_normal_form.
    apply n_zero.
  - simpl.
    destruct interp; intros [tev Hev].
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
  - simpl.
    destruct interp; intros [tev Hev].
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
    + remember (tm_to_nat t0) as HN.
      destruct HN.
      * destruct IHt.
        exists (tm_succ tev).
        apply e_succ.      
        assumption.
      * inversion Hev; subst.
        --  apply tm_to_nat_dom_only_nvalue_inv with (v := tev) in H0.
            inversion H0.
            apply nat_option_coexists with (n := x).
            rewrite -> HeqHN.
            symmetry.
            assumption.
        --  destruct IHt.
            exists t'.
            assumption. 
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
  - simpl.
    destruct interp; intros [tev Hev].
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + apply bvalue_cannot_eval with (t := tm_true) (t' := tev).
      * apply b_true.
      * assumption.
    + remember (tm_to_nat t0) as HN.
      destruct HN.
      * inversion Hev.
      * inversion Hev; subst.
        --  apply tm_to_nat_dom_only_nvalue_inv with (v := t0) in H0.
            inversion H0.
            apply nat_option_coexists with (n := x).
            rewrite -> HeqHN.
            symmetry.
            assumption.
        --  destruct IHt.
            exists t'.
            assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
    + inversion Hev.
      destruct IHt.
      exists t'.
      assumption.
Qed.