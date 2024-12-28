(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Type safety of the simply typed lambda-calculus

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/handin/<HemosID>/.  
 *)

(*
  For this assignment, you may use any tactic and library functions.
  Here are excerpts from the sample solution, which you might find helpful in learning new Coq tactics. 

    - eapply 
    eapply IHk with (e':={y::~>Y**A}e2); auto. 

    - firstorder 
    induction e; simpl; try case_var; simpl; firstorder.

    - congruence 
    case_var; inversion H; subst; exists (n :: emptyset); split; auto; simpl; case_var; try congruence; auto.

    - forwards (from LibTactics.v, similar to pose) 
    forwards Ha : (IHe _ _ _ _ H2).
    forwards Ha : (IHe1 _ _ _ _ H3); destruct Ha as [Sa [? ?]].

    - f_equal 
    simpl in H; f_equal; firstorder.

    - destruct with ? 
    destruct Ha as [x [A0 [e0 ?]]].

    - v62 (library)  
    induction e; intros; simpl; try case_var; simple; eauto using list_always_incl_emptyset with v62.
  
    - assert ... by. 
    assert (k1 < S (max k1 k2)) by auto with arith.
    assert (size_e e2 <= size_e e1 + size_e e2) by auto with arith.

    - The following sequence of tactics creates a fresh parameter not found in [(X, C)::~>e']e) ++ (X :: emptyset). 
    set (L := param ([(X, C)::~>e']e) ++ (X :: emptyset)).
    destruct (pick_fresh L) as [Y Hfresh].
    unfold L in Hfresh.
 *)

(*
  Type safety of simply typed lambda-calculus 
 *)

Set Implicit Arguments.

Require Import List.
Require Import Arith.
Require Import Max. 
Require Import LibTactics.    (* See LibTactics.v *)  
Require Import LibNat.        (* See LibNat.v. You may use any lemmas in LibNat.v. *) 

(** generating fresh nats *)

Section Exist_fresh.
  Fixpoint MAX (L : list nat) : nat :=
    match L with
    | nil        => O
    | cons hd tl => max hd (MAX tl)
    end.
  
  Lemma ex_fresh_var_1 : forall x L,
    In x L -> (x <= MAX L).
  Proof.
  induction L; intros.
    inversion H; simpl.
    destruct (max_dec a (MAX L)); destruct H; simpl.
        subst; rewrite e; apply le_refl.
        eapply le_trans; [ apply IHL; trivial | apply le_max_r].
        subst; apply le_max_l.
        eapply le_trans; [apply IHL; trivial | apply le_max_r].
  Qed.
      
  Lemma ex_fresh_var_2 : forall x L,
    MAX L < x -> ~ In x L.
  Proof.
  induction L; intuition; simpl.
    inversion H0; simpl; subst.
      eelim (le_not_lt). eapply ex_fresh_var_1. apply H0. trivial.
    apply IHL. apply le_lt_trans with (m := (MAX (a :: L))). simpl; apply le_max_r. assumption.
    inversion H0; subst.
      eelim le_not_lt. eapply ex_fresh_var_1. apply H0. trivial.
      trivial.
  Qed.

  Lemma pick_fresh : forall (L : list nat),
    exists n : nat, ~ In n L.
  Proof.
  induction L; intros.
    exists O; auto.
    exists (S (MAX (a :: L))); intuition.
    elim ex_fresh_var_2 with (x := (S (MAX (a :: L)))) (L := (a :: L)).
      apply lt_n_Sn.
      trivial.
  Qed.
(* Now you can use 
      destruct (pick_fresh L) as [Y Hfresh].
   to generate a fresh natural number Y not found in the set L. *)  
End Exist_fresh.

(** 
  Definitions and rules 
 *)

(** types *)
Inductive typ : Set :=
  | typ_top   : typ                     (* dummy base type *)
  | typ_arrow : typ -> typ -> typ.      (* function type *) 
Notation " A --> B " := (typ_arrow A B) (at level 65).

(** variables and parameters *) 
Notation var := nat.     (* variables *)
Notation par := nat.     (* parameters *)  

(** terms *) 
Inductive tm : Set := 
| tm_var : var -> tm                  (* variables *)
| tm_par : par -> typ -> tm           (* parameters annotated with a type *)
| tm_abs : var -> typ -> tm -> tm     (* lambda abstraction *)
| tm_app : tm -> tm -> tm.            (* lambda application *) 
(* parameter X annotated with type A *)
Notation " X ** A " := (tm_par X A) (at level 65).   

(* equality *) 

Lemma typ_dec : forall A B : typ, {A = B} + {A <> B}.
Proof.
  decide equality; apply eq_nat_dec.
Qed.

Lemma par_dec : forall (X Y : (par * typ)), {X = Y} + {X <> Y}.
Proof.
  decide equality; [apply typ_dec | apply eq_nat_dec ].
Qed.

Notation "p ==== q" := (par_dec p q) (at level 70).
(* Now you can use 'if p ==== q then ... else ...', 'destruct (p ==== q)', etc
   where you compare two parameters annotated with types. 
   Remember that you can compare two var's, or two par's, using 'x == y'. *)

(** list of parameters in a given term e. *)
Fixpoint param (e:tm) : list par :=
  (* to be filled by students *)
  end.

(** substitution of e' for x in e0 *) 
Fixpoint lsubst (x : var) (e' : tm) (e0 : tm) {struct e0} : tm :=
  (* to be filled by students *)
  (* Here you can use 'if x == y then ... else'. *)
  end.
Notation "{ x ::~> e0 } e " := (lsubst x e0 e) (at level 67).

(** substitution of e' for (X ** A) in e0 *)
Fixpoint fsubst (X : par) (A:typ) (e' e0: tm) {struct e0} : tm :=
  (* to be filled by students *)
  end.
Notation "[ ( X , A ) ::~> e ] e0 " := (fsubst X A e e0) (at level 67).

(** size of term e0 *) 
Fixpoint size_e (e0 : tm) : nat :=
  (* to be filled by students *)
  end.

(** values.
    'value t' means that term t is a value *)
Inductive value : tm -> Prop :=
  (* to be filled by students *)

(** one-step reduction.
    'red t1 t2' means that term t1 reduces to term t2. *)
Inductive red : tm -> tm -> Prop :=
  (* to be filled by students *)

(** locally closed terms.
    'lclosed S t' means that S is the list of temporarily unbound variables in term t. *) 
Inductive lclosed : list var -> tm -> Prop := 
  (* to be filled by students *)
  (* You might find 'remove eq_nat_dec' useful. *)    

(** typing relation.
    'typing t A' means that term t has type A. *)
Inductive typing : tm -> typ -> Prop :=
  (* to be filled by students *)
  (* Hint: see typingLH below *)

Hint Constructors value.
Hint Constructors red.
Hint Constructors lclosed.
Hint Constructors typing.

(** tactic destructing equality cases *)
Ltac case_var :=
  let ldestr X Y := destruct (X == Y); [try subst X | idtac] in
  let hdestr p q := destruct (p ==== q); [try subst p | idtac] in
  match goal with
  | |- context [?X == ?Y]      => ldestr X Y
  | H: context [?X == ?Y] |- _ => ldestr X Y
  | |- context [?p ==== ?q]      => hdestr p q
  | H: context [?p ==== ?q] |- _ => hdestr p q
  end.

(** 
  Type safety 
 *)

(** typing relation with sizes.
  We need typingLH because sometimes we need to perform induction on the size of typing judgments. 
 *)
Inductive typingLH : nat -> tm -> typ -> Prop :=
| typing_parLH : forall X A,
  typingLH O (tm_par X A) A
| typing_absLH : forall x A B e X k,
  ~ In X (param e) 
  -> typingLH k (lsubst x (tm_par X A) e) B 
  -> typingLH (S k) (tm_abs x A e) (A --> B)
| typing_appLH : forall e e' A B k1 k2,
  typingLH k1 e (A --> B) 
  -> typingLH k2 e' A 
  -> typingLH (S (max k1 k2)) (tm_app e e') B.

Hint Constructors typingLH.

(* 

Lemma typing_typingLH : forall e A,
  typing e A -> exists n : nat, typingLH n e A.

Lemma size_nochange : forall x X A e,
  size_e ({x ::~> X**A}e) = size_e e.

Lemma lclosed_var_split : forall e S0 x X A,
  lclosed S0 ({x ::~> X ** A}e) -> 
    (exists S, lclosed S e /\ remove eq_nat_dec x S = S0). 

Lemma typing_subst_par_nochange : forall e e' X A,
  ~ In X (param e) -> [(X, A) ::~> e']e = e.

Lemma subst_var_nochange : forall e S x e',
  lclosed S e ->
  ~ In x S ->
  {x ::~> e'}e = e.

Lemma subst_var_var : forall e x X A y Y B,
  x <> y -> {y ::~> Y**B}({x ::~> X**A}e) = {x ::~> X**A}({y ::~> Y**B}e).

Lemma subst_par_var : forall e e' x X A Y B,
  lclosed emptyset e' -> 
  X <> Y -> 
  [(Y, B) ::~> e']({x ::~> X**A}e) = {x ::~> X**A}([(Y, B) ::~> e']e).

Lemma subst_seq_par_var : forall e e' x X A,
  ~ In X (param e) -> 
  [(X, A) ::~> e']({x ::~> X**A}e) = {x ::~> e'}e.

Lemma typing_lclosed : forall e A,
  typing e A -> lclosed emptyset e.

Lemma param_sum : forall e e' x,
  incl (param ({x ::~> e'} e)) (param e ++ param e').

 *)

(** renaming lemma 
  You want to first perform induction on k, as in:
    induction k.
    intros; elim (lt_n_O (l + size_e e)); auto.
  *)
Lemma typingLH_rename_par : forall k e e' y Y Z A B l,
  l + size_e e < k
  -> typingLH l e' B 
  -> e' = ({y ::~> Y**A}e) 
  -> typingLH l ({y ::~> Z**A}e) B.
Proof.
Qed.

Lemma typingLH_subst_par : forall m n e A e' X C, 
  n < m 
  -> typingLH n e A 
  -> typing e' C 
  -> typing ([(X, C) ::~> e']e) A.
Proof.
Qed.

Lemma typing_subst_par : forall e A e' X C, 
  typing e A -> typing e' C -> typing ([(X, C) ::~> e']e) A.
Proof.
Qed.

Lemma typing_subst_var_par : forall x X A e e' B,
  ~ In X (param e) 
  -> typing ({x ::~> X**A}e) B
  -> typing e' A
  -> typing ({x ::~> e'}e) B.
Proof.
Qed.

(* 
Lemma preservation_typ_aux : forall e C, 
  typing e C -> 
  forall e', red e e' -> typing e' C.

Lemma preservation_fv_aux : forall e e',
  red e e' -> incl (param e') (param e).
 *)

(** preservation theorem *) 
Lemma preservation : forall e C, 
  typing e C -> 
  forall e', red e e' -> typing e' C /\ incl (param e') (param e).
Proof.
Qed.

(*
(** canonical forms lemma *)
Lemma canonical_form_abs : forall e A B,
  value e 
  -> typing e (A --> B)
  -> exists x A0 e0, e = tm_abs x A0 e0.
 *) 

(** progress theorem *)
Lemma progress : forall e A,
  typing e A -> 
  param e = emptyset -> 
  value e \/ exists e', red e e'.
Proof.
Qed.
