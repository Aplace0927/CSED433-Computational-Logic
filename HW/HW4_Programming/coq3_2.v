(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- first order logic 

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/<HemosID>/.
 *)

Section FirstOrder. 

Variable Term : Set.

Variables A B : Term -> Prop.

Variable O : Term.
Variable S : Term -> Term.

Variable Nat : Term -> Prop.
Variable Eq : Term -> Term -> Prop.
Variable Lt : Term -> Term -> Prop.

(* 
 * Axioms
 *)

Hypothesis Zero : Nat O.
Hypothesis Succ : forall x : Term, Nat x -> Nat (S x).
Hypothesis Eqi : forall x : Term, Eq x x.
Hypothesis Eqt : forall (x : Term) (y : Term) (z: Term), (Eq x y /\ Eq x z) -> Eq y z.
Hypothesis Lts : forall x : Term, Lt x (S x).
Hypothesis Ltn : forall (x : Term) (y : Term), Eq x y -> ~ Lt x y.

(* 
 * Part 0 - Please redo the exercise given in the handout. 
 *)

Theorem forall_and : 
(forall x : Term, A x /\ B x) -> (forall x : Term, A x)  /\ (forall x : Term, B x).
Proof.
  intro w.
  split.
  intro a; apply (w a).
  intro b; apply (w b).
Qed.

Theorem exist_neg : (exists x : Term, ~ A x) -> (~ forall x : Term, A x).
Proof.
  intro ext.
  intro fal.
  elim ext.
  intros a nA.
  elim nA.
  apply fal.
Qed.

Theorem not_weird : forall y : Term, (forall x : Term, A x) -> (exists x : Term, A x).
Proof.
  intros a fal.
  exists a.
  apply (fal a).
Qed.

(* 
 * Part 1
 *)

Theorem Nat_ex : forall x : Term, Nat x -> exists y : Term, Nat y /\ Eq x y.
Proof.
  intros n natof.
  exists n.
  split.
  apply natof.
  apply (Eqi n).
Qed.

Theorem Eq_refl : forall (x : Term) (y : Term), Eq x y -> Eq y x.
Proof.
  intros x y eqxy.
  apply (Eqt x y x).
  split.
  apply eqxy.
  apply (Eqi x). 
Qed.

Theorem Eq_not : ~ exists x : Term, Eq x O /\ Eq x (S O).
Proof.
  intro ext.
  destruct ext as [n [eq_n eq_sn]].
  apply (Ltn (O) (S O)).
  apply (Eqt n (O) (S O)).
  split.
  apply eq_n.
  apply eq_sn.
  apply (Lts O).
  Qed.

(*
 * Part 2
 *)

Theorem Nat_succ2 : forall x : Term, Nat x -> Nat (S (S x)).
Proof.
  intros x natx.
  apply (Succ (S x)).
  apply (Succ x).
  apply natx.
Qed.

Theorem Lt_Neq : forall (x : Term) (y : Term), Lt x y -> ~ Eq x y.
Proof.
  intros x y ltxy.
  intro eqxy.
  apply (Ltn x y).
  apply eqxy.
  apply ltxy.
Qed.

Theorem Not_EqLt : ~ exists x : Term, exists y : Term, Eq x y /\ Lt x y.
Proof.
  intro hyp.
  destruct hyp as [x ext_y].
  destruct ext_y as [y conj].
  apply (Ltn x y).
  apply conj.
  apply conj.
Qed.

End FirstOrder. 