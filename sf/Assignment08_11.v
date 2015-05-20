Require Export Assignment08_10.

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
  split; intros.
  - inversion H0. subst. assert (st' = (update st' X (aeval st' e))).
    unfold aequiv in H. rewrite <- H. simpl. apply functional_extensionality.
    intros. unfold update. destruct (eq_id_dec X x). subst. reflexivity. reflexivity.
    rewrite H1 at 2. constructor. reflexivity.
  - inversion H0. subst. replace (update st X (aeval st e)) with st.
    constructor. apply functional_extensionality. intros. unfold aequiv in H.
    rewrite <- H. simpl. unfold update. destruct (eq_id_dec X x). subst. reflexivity. reflexivity.
Qed. 

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).

