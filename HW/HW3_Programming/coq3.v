(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Proof terms 

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/<HemosID>/.
 *)

Section ProofTerm.

Variables A B C D : Prop.

(*
 * Tactics 
 *)

Definition impl_distr : (A -> B) -> (A -> C) -> A -> B -> C :=
  fun (x: A->B) (y: A->C) (z: A) (w: B) => (y z).

Definition impl_comp : (A -> B) -> (B -> C) -> A -> C :=
  fun (x: A->B) (y: B->C) (z: A) => y (x z).

Definition impl_perm : (A -> B -> C) -> B -> A -> C :=
  fun (x: A->B->C) (y: B) (z: A) => (x z) y.

Definition impl_conj : A -> B -> A /\ B :=
  fun (x: A) (y: B) => conj x y.

Definition conj_elim_l : A /\ B -> A :=
  fun (f: A /\ B) =>
    and_ind (fun (x: A) (y: B) => x) f.

Definition disj_intro_l : A -> A \/ B :=
  fun (x: A) => or_introl B x.

Definition disj_elim : A \/ B -> (A -> C) -> (B -> C) -> C :=
  fun (x: A \/ B) (a: A->C) (b: B->C) => or_ind a b x.

Definition diamond : (A -> B) -> (A -> C) -> (B -> C -> D) -> A -> D := 
  fun (ab: A->B) (ac: A->C) (bcd: B->C->D) (a: A) => bcd (ab a) (ac a).
  
Definition weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B :=
  fun (f: (((A->B)->A)->A)->B) => 
    f (fun (g: (A->B)->A) => 
      g (fun (a: A) =>
        f (fun (x: (A->B)->A) => a)
        )
      ).
  
Definition disj_impl_dist : (A \/ B -> C) -> (A -> C) /\ (B -> C) :=
  fun (f: A \/ B -> C) =>
    conj
      (fun (a: A) => f (or_introl B a))
      (fun (b: B) => f (or_intror A b)).

Definition disj_impl_dist_inv : (A -> C) /\ (B -> C) -> A \/ B -> C :=
  fun (f: (A -> C) /\ (B -> C)) =>
    fun (ab: A \/ B) =>
      or_ind 
        (and_ind (fun (a: A->C) (b: B->C) => a) f)
        (and_ind (fun (a: A->C) (b: B->C) => b) f)
        ab.

Definition curry : (A /\ B -> C) -> A -> B -> C :=
  fun (f: A /\ B -> C) (a: A) (b: B) => f (conj a b).

Definition uncurry : (A -> B -> C) -> A /\ B -> C :=
  fun (f: A -> B -> C) (ab: A /\ B) =>
    f (and_ind (fun (a: A) (b: B) => a) ab) (and_ind (fun (a: A) (b: B) => b) ab).

(*
 * Negation
 *)

Definition contrapositive : (A -> B) -> (~B -> ~A) :=
  fun (ab: A -> B) =>
    fun (nb: ~B) =>
      fun (a: A) =>
        nb (ab a).


Definition neg_double : A -> ~~A :=
  fun (a: A) (f: A -> False) => f a.

Definition tneg : ~~~A -> ~A :=
  fun (tna: ~~~A) (a: A) => 
    tna (fun (af: ~A) => af a).

Definition weak_dneg : ~~(~~A -> A) :=
  fun (f : ~(~~A -> A)) => f (
    fun (g : ~~A) => False_ind A (
      g 
      (fun (h: A) => (f (fun x => h)))
    )
  ).

(*
 * Classical logic
 *)

Definition em_peirce : A \/ ~A -> ((A -> B) -> A) -> A := 
  fun (ana: A \/ ~A) (aba: (A->B)->A) =>
    or_ind
      (fun (a: A) => a)
      (fun (na: ~A) => 
        aba (fun (a': A) => 
          False_ind B (na a')
        )
      )
      ana.

Definition peirce_dne : (((A -> False) -> A) -> A) -> ~~A -> A :=
  fun (f: ((A->False)->A)->A) (nna: ~~A) => f (
    fun (af: A->False) => False_ind 
    A (nna (fun (a: A) => af a))
  ).


Definition dne_em : (~~(B \/ ~B) -> (B \/ ~B)) -> B \/ ~B :=
  fun (f: ~~(B \/ ~B) -> (B \/ ~B)) => f (
    fun (bn: ~(B \/ ~B)) => bn (
      or_intror (B) (fun (b: B) => bn (or_introl (~B) b))
    )
  ).

End ProofTerm. 
