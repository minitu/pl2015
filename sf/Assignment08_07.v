Require Export Assignment08_06.

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (IFB_false)  *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.
Proof.
  unfold bequiv. unfold cequiv. intros. simpl in H. split.
  - intros. inversion H0. 
    + subst. rewrite H in H6. inversion H6.
    + subst. apply H7.
  - intros. apply E_IfFalse. specialize H with st.
    + assumption.
    + assumption.
Qed.

(*-- Check --*)
Check IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.

