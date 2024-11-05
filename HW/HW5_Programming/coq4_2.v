(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Inductive Datatypes, Part 2 

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/handin/<HemosID>/.  
 *)

Section InductiveDatatypeTwo.

(* 
  The inductive datatype nat and its two operations plus and mult are already defined in the default environment.
  Moreover you may use infix operators + and * for plus and mult, respectively. 
 *)

(* O + S O is another way of writing plus O (S O). *)
Eval compute in O + S O.
Eval compute in plus O (S O).

(* S (S O) * S (S O) is another way of writing mult (S (S O)) (S (S O)). *)
Eval compute in S (S O) * S (S O).
Eval compute in mult (S (S O)) (S (S O)).

(* We define 'double m' as 'm + m'.*)
Definition double (m:nat) : nat := m + m.

Fixpoint sum_n (n:nat) {struct n} : nat :=
match n with
| O => O
| S n' => (S n') + (sum_n n')
end.

(* Problem 3 *)

(* Prove the same lemmas that are given in Part 1, but using the datatype nat provided in the default environment. 
   In most cases, you should be able to reuse the proofs from Part 1. 
 *)

Lemma plus_n_O : forall n:nat, n = n + O.
Proof.
    intro n.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite <- IHn. reflexivity.
Qed.

Lemma plus_n_S : forall n m:nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  induction m.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Lemma plus_com : forall n m:nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
  - induction m.
    + reflexivity.
    + simpl. rewrite <- IHm.
      simpl. reflexivity.
  - induction m.
    + simpl. rewrite -> IHn.
      simpl. reflexivity.
    + simpl. rewrite -> IHn.
      simpl. rewrite plus_n_S. reflexivity.
Qed.

Lemma plus_assoc : forall (m n l:nat), (m + n) + l = m + (n + l).
Proof.
  intros m n l.
  induction l.
  - rewrite <- plus_n_O. rewrite <- plus_n_O. reflexivity.
  - rewrite <- plus_n_S. rewrite <- plus_n_S. rewrite <- plus_n_S. rewrite <- IHl. reflexivity.
Qed.

(* Problem 4 *)

(* Prove the same theorem sum_n_plus given in Part 1, but using the datatype nat provided in the default environment. 
   Introduce additional lemmas as necessary. 
 *)
Lemma double_as_plus: forall n:nat, double n = n + n.
Proof.
  intro n.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite -> plus_com.
    rewrite -> plus_n_S.
    reflexivity.
Qed.

Lemma mult_identity: forall n:nat, n * O = O.
Proof.
  intro n.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity. 
Qed.

Lemma mult_one: forall n: nat, n * (S O) = n.
Proof.
  intro n.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed. 

Lemma mult_comm_lemma: forall (m n:nat), m + m * n = m * S n.
Proof.
  intros m n.
  induction m.
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHm.
    rewrite <- plus_assoc.
    rewrite <- plus_assoc.
    rewrite <- plus_com.
    rewrite <- plus_com.
    rewrite <- (plus_com m n).
    reflexivity.
Qed.

Theorem sum_n_plus : forall n:nat, double (sum_n n) = n + n * n.
Proof.
  intro n.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite <- plus_n_S.
    rewrite <- plus_assoc.
    unfold double.
    rewrite <- plus_n_S.
    rewrite <- plus_assoc.
    rewrite <- plus_com.
    rewrite <- (plus_com (sum_n n) n).
    rewrite <- plus_assoc.
    rewrite <- plus_n_S.
    rewrite <- plus_assoc.
    rewrite <- double_as_plus.
    rewrite -> IHn.
    simpl.
    rewrite <- mult_comm_lemma.
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    rewrite -> (plus_com (n * n) (n + n)).
    rewrite -> (plus_assoc n n (n * n)).
    reflexivity.
Qed.
(* Problem 5 *)

(* We will use the Coq library Arith which provides various theorems on the datatype nat. 
   All the previous lemmas are already provided the Arith library.
   You can search for appropriate lemmas by using the commands SearchPattern and SearchRewrite. 
 *)
Require Import Arith.

(* Lemma plus_n_S : forall n m:nat, S (n + m) = n + (S m). *)
(* We do not need to prove the lemma plus_n_S, as it is already provided by the Arith library. *)
SearchPattern (S (_ + _) = _ + (S _)).
SearchRewrite (S (_ + _)).
SearchRewrite (_ + (S _)).

(* Lemma plus_com : forall n m:nat, n + m = m + n. *)
SearchPattern (_ + _ = _ + _).
SearchRewrite (_ + _).

(* Lemma plus_assoc : forall (m n l:nat), (m + n) + l = m + (n + l). *)
SearchPattern (_ + _ + _ = _ + (_ + _)).
SearchRewrite ((_ + _) + _).
SearchRewrite (_ + (_ + _)).
SearchRewrite (_ + _ + _).

(* Prove the same theorem sum_n_plus, but using the Arith library. 
   You can find in the Arith library all the lemmas that you need to complete the proof. *)
(****** Do not introduce new lemmas. ******)

Theorem sum_n_plus' : forall n:nat, double (sum_n n) = n + n * n.
Proof.
 intro n.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite <- Nat.add_succ_l.
    rewrite <- Nat.add_succ_l.
    rewrite -> Nat.mul_comm.
    rewrite -> Nat.mul_succ_l.
    rewrite -> (Nat.add_comm (n * n) (n)).
    rewrite <- IHn.
    unfold double.
    rewrite <- Nat.add_succ_l.
    rewrite -> Nat.add_assoc.
    rewrite -> (Nat.add_comm (S n) (sum_n n + sum_n n)).
    rewrite -> Nat.add_assoc.
    rewrite -> Nat.add_assoc.
    rewrite -> (Nat.add_comm (S n + sum_n n + sum_n n) (S n)).
    rewrite -> (Nat.add_comm (S n + sum_n n) (sum_n n)).
    rewrite -> Nat.add_assoc.
    rewrite -> Nat.add_assoc.
    reflexivity.
Qed.

(* Problem 6 *)

(* We will use the Coq library ArithRing which provides an automation tactic ring and ring_simplify. 
 *)
Require Import ArithRing.

(* Prove the same theorem sum_n_plus using the tactic 'ring_simplify.'
   Instead of the tactic 'ring', use the tactic 'ring_simplify' which displays how arithmetic expressions are 
   transformed. 
  *)
(****** Do not introduce new lemmas. ******)

Theorem sum_n_plus'' : forall n:nat, double (sum_n n) = n + n * n.
Proof.
  intro n.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite <- Nat.add_succ_l.
    rewrite <- Nat.add_succ_l.
    rewrite -> Nat.mul_comm.
    rewrite -> Nat.mul_succ_l.
    rewrite -> (Nat.add_comm (n * n) (n)).
    rewrite <- IHn.
    unfold double.
    ring_simplify.
    reflexivity.
Qed.

End InductiveDatatypeTwo.