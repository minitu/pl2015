Require Export Assignment05_03.

(* problem #04: 10 points *)



Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  destruct H. destruct H0. split.
  - intros. apply H in H3. apply H0 in H3. apply H3.
  - intros. apply H2 in H3. apply H1 in H3. apply H3.
Qed.


