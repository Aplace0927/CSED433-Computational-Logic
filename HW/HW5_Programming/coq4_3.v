(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Inductive Datatypes, Part 3

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/handin/<HemosID>/.  
 *)

Section InductiveDatatypeThree.

(* 
  1. 
  We use the inductive datatype nat defined in the default environment.

  2. 
  You may use the inequality operation 'm <> n' which is defined as:
  
    m = n -> False

  3. 
  For this assignment, you might need a new tactic 'inversion' or 'discriminate'.

  In Coq, you give only introduction rules and not elimination rules because
  Coq provides the tactic 'inversion'.  Let us assume that 'e' holds a proof of
  a predicate 'A'.  'inversion e' basically applies appropriate elimination
  rules to the predicate 'A' and generates new hypotheses.  Since elimination
  rules are all derived from introduction rules, we can think of 'inversion e'
  as inverting the introduction rules to derive all the necessary conditions
  that should hold in order for the predicate 'A' to be proved.  Thus, whenever
  you need to apply an elimination rule to a judgment, you may need to consider
  this tactic.

  For example, suppose that you want to prove:

    S n <> O

  You can apply first 'intro' which generates a new hypothesis 'S n = 0'. Then
  you apply 'inversion' to this hypothesis, which instantly completes the proof
  because there is no way to prove 'S n = 0'. It's like eliminating an
  assumption that is impossible to prove.  

  Alternatively you can apply 'discriminate', which inspects the two operands
  of <> and checks if they cannot be equal. Since 'S n' cannot be equal to '0'
  syntactically (because the two constructors are different), applying
  'discriminate' instantly completes the proof.  

  See the following script:

Lemma foo : forall n:nat, S n <> O.
Proof.
intro n.
unfold not.
intro H.
inversion H.
Qed. 

Lemma bar : forall n:nat, S n <> O.
Proof.
intro n.
discriminate.
Qed.
 *)

(** Part 1.

    Consider a different, more efficient representation of natural numbers
    using a binary rather than unary system.  That is, instead of saying that
    each natural number is either zero or the successor of a natural number, we
    can say that each binary number is either
      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    First, write an inductive definition of the type [bin] corresponding to
    this description of binary numbers. 

    Recall that the definition of [nat], 

        Inductive nat : Set :=
        | O : nat
        | S : nat -> nat.
    
    says nothing about what [O] and [S] "mean".  It just says "[O] is a nat
    (whatever that is), and if [n] is a nat then so is [S n]".  The intended
    meaning of [O] as zero and [S] as successor/plus one comes from the way
    that we use nat values, by writing functions to do things with them,
    proving things about them, and so on.  Your definition of [bin] should be
    correspondingly simple; it is the functions you will write next that will
    give it mathematical meaning.

    Next, write an increment function for binary numbers, and a function to
    convert binary numbers to unary numbers.

    Finally, prove that your increment and binary-to-unary functions commute:
    that is, incrementing a binary number and then converting it to unary
    yields the same result as first converting it to unary and then
    incrementing.
*)

Inductive bin : Set := 
| Z : bin
| I : bin -> bin
| D : bin -> bin.

Fixpoint increment_bin (m:bin) : bin :=
match m with
| Z => I Z
| I m' => I m'.
| D m' => D m'.
end.

Fixpoint binary_to_unary (m:bin) : nat := (* FILL IN HERE *)

Lemma increment_bin_binary_to_unary_comm: forall m,
  binary_to_unary (increment_bin m) = S (binary_to_unary m).
Proof.
Qed. 

(** Part 2. 
 
    First, write a function to convert natural numbers to binary numbers.  Then
    prove that starting with any natural number, converting to binary, then
    converting back yields the same natural number you started with.

    You might naturally think that we should also prove the opposite direction:
    that starting with a binary number, converting to a natural, and then back to
    binary yields the same number we started with. However, it is not true! Explain
    what the problem is.

    Define a function normalize from binary numbers to binary numbers such that for
    any binary number b, converting to a natural and then back to binary yields
    (normalize b). Prove it.
*)

Fixpoint unary_to_binary (m:nat) : bin := (* FILL IN HERE *)

Lemma unary_binary_unary_eq: forall m,
  binary_to_unary (unary_to_binary m) = m.
Proof.
Qed.

Fixpoint normalize (m:bin) : bin := (* FILL IN HERE *).

Lemma binary_unary_binary_eq: forall m,
  unary_to_binary (binary_to_unary m) = normalize m.
Proof.
Qed. 

End InductiveDatatypeThree.

