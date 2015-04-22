Require Export Assignment06_04.

(* problem #05: 20 points *)

(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all_nil : all P []
  | all_add : forall (x : X) (l : list X), (P x) /\ (all P l) -> (all P (cons x l))
.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.
Proof.
  intros. split.
  - intros. induction l.
    + apply all_nil.
    + apply all_add. split.
      * simpl in H. destruct (P x).
        reflexivity.
        destruct (forallb P l).
        simpl in H. inversion H.
        simpl in H. inversion H.
      * apply IHl. simpl in H. destruct (forallb P l).
        reflexivity.
        destruct (P x).
        simpl in H. inversion H.
        simpl in H. inversion H.
  - intros. induction l.
    + simpl. reflexivity.
    + simpl. inversion H. destruct H1. apply IHl in H3. rewrite H1. rewrite H3. reflexivity.
Qed.

(** [] *)

