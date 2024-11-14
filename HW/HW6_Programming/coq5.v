(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Inductive Predicate 

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/handin/<HemosID>/.  
 *)

Section InductivPredicate. 

Inductive nat : Set := 
| O : nat
| S : nat -> nat.

Inductive lt : nat -> nat -> Prop :=
| lt_O : forall n:nat, lt O (S n)
| lt_S : forall (m:nat) (n:nat), lt m n -> lt (S m) (S n).

Inductive eq : nat -> nat -> Prop :=
| eq_O : eq O O
| eq_S : forall (m n:nat), eq m n -> eq (S m) (S n).

(**********)
(* Part 1 *)
(**********) 

Lemma lt_one_two : lt (S O) (S (S O)).
Proof.
    apply lt_S.
    apply lt_O.
Qed.

Lemma no_lt_zero : forall (m:nat), ~(lt m O).
Proof.
    intro m.
    unfold not.
    intro H.
    inversion H.
Qed.

Lemma exists_greater : forall (x:nat), exists y:nat, lt x y.
Proof.
  apply nat_ind. 
  - exists (S O).
    apply lt_O.
  - intros n H.
    destruct H.
    exists (S x).
    apply lt_S.
    apply H.
(* use nat_ind; do not use elim/induction. *)
Qed.

Lemma exists_greater' : forall (x:nat), exists y:nat, lt x y.
Proof.
  intro x.
  induction x.
  - exists (S O).
    apply lt_O.
  - destruct IHx.
    exists (S x0).
    apply lt_S.
    apply H. 
Qed.

Lemma eq_nat : forall x:nat, eq x x.
Proof.
  apply nat_ind.
  - apply eq_O.
  - intros n H.
    apply eq_S.
    apply H.
(* use nat_ind; do not use elim/induction. *)
Qed.

Lemma eq_nat' : forall x:nat, eq x x.
Proof.
  intro x.
  induction x as [| x IHx].
  - apply eq_O.
  - apply eq_S.
    apply IHx.
Qed.

Lemma eq_trans : forall (x y z:nat), eq x y -> eq y z -> eq x z.
Proof.
  intros x y z Hxy Hyz.
  revert z Hyz.
  induction Hxy as [n | m n Hmn IH].
  - intros z Hyz. 
    apply Hyz.
  - intros z Hyz.
    inversion Hyz as [a | b Hnb IH']; subst.
    apply eq_S.
    apply IH.
    apply IH'.
Qed.

Lemma eq_succ : forall x:nat, ~(eq x O) -> exists y:nat, eq (S y) x.
Proof.
  intros x H.
  induction x.
  - apply False_ind.
    apply H.
    apply eq_O.
  - exists x.
    apply eq_S.
    apply eq_nat.
Qed.

(**********)
(* Part 2 *)
(**********) 

Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_S : forall (m n:nat), le m n -> le m (S n).

Lemma le_zero : forall n:nat, le O n.
Proof.
  intro n.
  induction n.
  - apply le_n.
  - apply le_S.
    apply IHn.
Qed.

Lemma le_n_S : forall n m:nat, le n m -> le (S n) (S m).
Proof.
(* use le_ind; do not use elim/induction. *)
  apply le_ind.
  - intro n.
    apply le_n.
  - intros m n Hmn Hsmsn.
    apply le_S.
    apply Hsmsn. 
Qed.

Lemma lt_le : forall (m n:nat), lt m n -> le m n.
Proof.
(* use lt_ind; do not use elim/induction. *)
  apply lt_ind.
  - intro n.
    apply le_zero.
  - intros m n Hlt Hle.
    apply le_n_S.
    apply Hle. 
Qed.

Lemma lt_le' : forall (m n:nat), lt m n -> le m n.
Proof.
  intros m n Hlt.
  induction Hlt as [n | m n Hlt IH].
  - apply le_zero.
  - apply le_n_S.
    apply IH.
Qed.

(**********)
(* Part 3 *)
(**********) 

Lemma lt_succ : forall (m n:nat), lt m n -> lt m (S n).
Proof.
  intros m n Hlt.
  induction Hlt as [n | m n Hlt IH].
  - apply lt_O.
  - apply lt_S.
    apply IH.
Qed.

Lemma eq_lt : forall (m n:nat), eq m n -> lt m (S n).
Proof.
  intros m n Heq.
  induction Heq as [| m n Heq IH].
  - apply lt_O.
  - apply lt_S.
    apply IH.
Qed.

Theorem le_lt_eq : forall (m n:nat), le m n -> lt m n \/ eq m n.
Proof.
  intros m n Hle.
  induction Hle as [n | m n Hle IH].
  - right.
    apply eq_nat.
  - destruct IH as [Hlt | Heq].
    + left.
      apply lt_succ.
      apply Hlt.
    + left.
      apply eq_lt.
      apply Heq. 
Qed.

(**********)
(* Part 4 *)
(**********) 

Inductive le' (n:nat) : nat -> Prop :=
| le_n' : le' n n
| le_S' : forall m:nat, le' n m -> le' n (S m).

Lemma le_le' : forall (m n:nat), le m n -> le' m n.
Proof.
  intros m n Hle.
  induction Hle as [n | m n Hle Hle'].
  - apply le_n'.
  - apply le_S'.
    apply Hle'.
Qed.

Lemma le'_le : forall (m n:nat), le' m n -> le m n.
Proof.
  intros m n Hle'.
  induction Hle' as [n | n Hle' Hle].
  - apply le_n.
  - apply le_S.
    apply Hle.
Qed.

End InductivPredicate. 

