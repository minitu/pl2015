Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv. unfold cequiv. split; intros.
  - inversion H2.
    subst. rewrite H in H8. apply E_IfTrue. assumption.
    rewrite <- H0. assumption. 
    subst. rewrite H in H8. apply E_IfFalse. assumption.
    rewrite <- H1. assumption.
  - inversion H2.
    subst. rewrite <- H in H8. apply E_IfTrue. assumption.
    rewrite H0. assumption.
    subst. rewrite <- H in H8. apply E_IfFalse. assumption.
    rewrite H1. assumption.
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

