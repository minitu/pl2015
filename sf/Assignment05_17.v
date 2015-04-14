Require Export Assignment05_16.

(* problem #17: 10 points *)





(** 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  induction m.
  - intros. simpl. apply b_0.
  - intros. simpl. apply b_sum.
    + apply H.
    + apply IHm. apply H.
Qed.
(** [] *)




