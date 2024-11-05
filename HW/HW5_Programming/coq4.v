(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Inductive Datatypes, Part 1 

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/handin/<HemosID>/.  
 *)

Section InductiveDatatype.

(* inductive datatype nat *) 
 
Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(* recursive functions plus, mult, double, sum_n *)

Fixpoint plus (m n:nat) {struct m} : nat :=
match m with
| O => n
| S m' => S (plus m' n)
end.

Fixpoint mult (m n:nat) {struct m} : nat :=
match m with
| O => O
| S m' => plus n (mult m' n)
end.

Fixpoint double (m:nat) : nat :=
match m with
| O => O
| S m' => S (S (double m'))
end.

Fixpoint sum_n (n:nat) {struct n} : nat :=
match n with
| O => O
| S n' => plus (S n') (sum_n n')
end.

(* Problem 1 *)

(* You do not need to use induction to prove plus_O_n. *)
Lemma plus_O_n : forall n:nat, n = plus O n.
Proof.
    intro n.
    simpl.
    reflexivity.
Qed.

(* You need to use induction to prove plus_n_O. *)
Lemma plus_n_O : forall n:nat, n = plus n O.
Proof.
    intro n.
    induction n.
    - simpl; reflexivity.
    - simpl; rewrite <- IHn; reflexivity.
Qed.

Lemma plus_n_S : forall n m:nat, S (plus n m) = plus n (S m).
Proof.
    intros n m.
    induction n.
    induction m.
    - simpl; reflexivity.
    - simpl; reflexivity.
    - simpl; rewrite <- IHn; reflexivity.
Qed.

Lemma plus_com : forall n m:nat, plus n m = plus m n.
Proof.
    intros n m.
    induction n.
    - induction m.
        -- reflexivity.
        -- simpl; rewrite <- IHm; simpl; reflexivity.
    - induction m.
        -- simpl; rewrite -> IHn; simpl; reflexivity.
        -- simpl; rewrite -> IHn; simpl; rewrite <- plus_n_S; reflexivity.
Qed.

Lemma plus_assoc : forall (m n l:nat), plus (plus m n) l = plus m (plus n l).
Proof.
    intros m n l.
    induction l.
    - rewrite <- plus_n_O; rewrite <- plus_n_O; reflexivity.
    - rewrite <- plus_n_S; rewrite <- plus_n_S; rewrite <- plus_n_S; rewrite <- IHl; reflexivity.
Qed.

(* Problem 2 *)

(* Introduce lemmas as necessary. *)

Lemma double_is_add_twice: forall n:nat, double n = plus n n.
Proof.
    intro n.
    induction n.
    - simpl; reflexivity.
    - simpl; rewrite -> IHn; rewrite <- plus_n_S; reflexivity.
Qed.

Lemma double_is_distributive: forall (m n: nat), double (plus m n) = plus (double m) (double n).
Proof.
    intros m n.
    induction n.
    induction m.
    - simpl; reflexivity.
    - simpl; rewrite -> IHm; simpl; reflexivity.
    - rewrite <- plus_n_S;
      simpl; rewrite -> double_is_add_twice; rewrite <- plus_n_S; rewrite <- plus_n_S.
      rewrite <- IHn; rewrite <- double_is_add_twice; reflexivity.
Qed.

Theorem mult_comm_lemma: forall (m n: nat), plus m (mult m n) = mult m (S n).
Proof.
    intros m n.
    induction m.
    - simpl; reflexivity.
    - simpl; rewrite <- IHm; rewrite <- plus_assoc. rewrite <- plus_assoc; rewrite <- plus_com; rewrite <- plus_com; rewrite <- (plus_com m n); reflexivity.
Qed.

Theorem sum_n_plus : forall n:nat, double (sum_n n) = plus n (mult n n).
Proof.
    intro n.
    induction n.
    - simpl; reflexivity.
    - simpl. rewrite -> double_is_distributive. rewrite -> double_is_add_twice. 
      rewrite -> plus_assoc. rewrite <- plus_n_S. rewrite -> IHn. rewrite <- mult_comm_lemma. reflexivity.
Qed.

End InductiveDatatype. 
