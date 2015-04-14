Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)
Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros.
  inversion H.
Qed.

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  intros. unfold not in H. generalize dependent m. induction n.
  - destruct m.
    + intros. simpl. apply ex_falso_quodlibet. apply H. reflexivity.
    + simpl. reflexivity.
  - destruct m.
    + simpl. reflexivity.
    + intros. simpl. apply IHn. intros. apply H. apply f_equal. apply H0.
Qed.

(** [] *)




