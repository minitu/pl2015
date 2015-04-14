Require Export Assignment05_32.

(* problem #33: 10 points *)

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  intros. induction b.
  - rewrite plus_comm. simpl. apply le_n.
  - rewrite plus_comm. simpl. apply le_S. rewrite plus_comm. apply IHb.
Qed.

