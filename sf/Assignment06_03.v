Require Export Assignment06_02.

(* problem #03: 10 points *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  - intros.
    inversion H as [x Hx]. inversion Hx. 
    + left. exists x. apply H0.
    + right. exists x. apply H0.
  - intros. inversion H. 
    + inversion H0 as [x Hx]. exists x. left. apply Hx.
    + inversion H0 as [x Hx]. exists x. right. apply Hx.
Qed.
(** [] *)


