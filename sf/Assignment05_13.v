Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros. unfold not. intros.
  rewrite H0 in H. rewrite <- beq_nat_refl in H.
  inversion H.
Qed.
(** [] *)



