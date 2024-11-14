(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Inductive Proofs 

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/handin/<HemosID>/.  
 *)

Section Paren. 

Inductive E : Set :=
| LP : E
| RP : E.

Inductive T : Set := 
| eps : T
| cons : E -> T -> T.

Fixpoint concat (s1 s2:T) {struct s1} : T :=
match s1 with
| eps => s2
| cons e s2' => cons e (concat s2' s2) end.

(* You may use the following notations if you would like to learn the Notation command of Coq. 
 *)
(* for Coq 8.3 *)
(*
Notation " s :: t " := (cons s t) (at level 65, right associativity).
Notation " s ++ t " := (concat s t) (at level 66, left associativity).
 *)
(* for Coq 8.2 *)
Notation " s ::: t " := (cons s t) (at level 65, right associativity).
Notation " s +++ t " := (concat s t) (at level 66, left associativity).
Notation LPs := (cons LP eps).
Notation RPs := (cons RP eps).

Inductive mparen : T -> Prop :=

Inductive lparen : T -> Prop :=

Inductive tparen : T -> Prop :=

(*
Suppose that you want to prove the following lemma:

  Lemma tparenConcat : forall (s s':T), tparen s -> tparen s' -> tparen (concat s s').

You will find that in order to prove this lemma, you want to apply induction on
tparen s', not on tparen s.  So, you may try the following sequence of tactics:

  Lemma tparenConcat : forall (s s':T), tparen s -> tparen s' -> tparen (concat s s').
  Proof.
  intros s s' H H'.
  induction H'.

Unfortunately when you apply induction on H', s becomes fixed because the
hypothesis of tparen s appears before the hypothesis tparen s'.  What you want
is to apply induction on H' while s remains a variable ranging over datatype T.
In other words, what you realy want to do is to prove the following lemma 

  Lemma tparenConcat' : forall (s':T), tparen s' -> forall (s:T), tparen s -> tparen (concat s s').

by applying induction on tparen s':

  Lemma tparenConcat' : forall (s':T), tparen s' -> forall (s:T), tparen s -> tparen (concat s s').
  Proof.
  intros s' H'.
  induction H'.

Note that both tparenConcat and tparenConcat' state the same logical formula. 

Then how can we complete the proof of tparenConcat? 

The common solution is to use the 'generalize dependent' tactic.  Executing
'generalize dependent x' moves term x as well as all its related hypotheses
back to the goal.  See the example below to see how it works:

  Lemma tparenConcat : forall (s s':T), tparen s -> tparen s' -> tparen (concat s s').
  Proof.
  intros s s' H H'.
  generalize dependent s.
  generalize dependent s'.

The goal has changed to tparenConcat' and you can apply induction on s' now. 

The second solution is not to use the 'generalize dependent' tactic at all but
instead to rewrite the goal. For example, instead of proving tparenConcat, you
could prove tparenConcat' instead, which is no harder to prove than
tparenConcat.  If you find yourself trying the 'generalize dependent' tactic,
you could rewrite rewriting the theorem and dispense with the use of the
'generalize dependent' tactic. 
*)

Theorem mparen2lparen : forall s:T, mparen s -> lparen s.
Proof.
Qed.

Theorem lparen2mparen : forall s:T, lparen s -> mparen s.
Proof.
Qed.

Theorem mparen2tparen : forall s:T, mparen s -> tparen s.
Proof.
Qed.

Theorem tparen2lparen : forall s:T, tparen s -> lparen s.
Proof.
Qed.

End Paren.
