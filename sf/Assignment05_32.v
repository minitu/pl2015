Require Export Assignment05_31.

(* problem #32: 10 points *)

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros. generalize dependent n. induction m.
  - intros. inversion H.
    + apply le_n.
    + inversion H2.
  - intros. inversion H.
    + apply le_n.
    + apply le_S. apply IHm in H2. apply H2.
Qed.

