Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  intros. unfold not in H. generalize dependent m. induction n.
  - induction m.
    + intros. simpl. Admitted.

(** [] *)




