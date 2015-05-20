Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof. 
  unfold atrans_sound. unfold aequiv. intros.
  induction a; try reflexivity; try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  destruct a1; destruct a2;
  try (simpl in *; try rewrite IHa1; try rewrite IHa2; reflexivity);
  destruct n; try destruct n0; simpl in *; omega.
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

