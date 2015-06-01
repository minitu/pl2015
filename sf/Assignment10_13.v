Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  induction n; intros.
  - exists st. split.
    apply multi_refl. assumption. 
  - apply IHn in H. inversion H as [st' Hst'].
    exists (update st' X (S n)).
    split.
    + inversion Hst'. eapply multi_trans.
      apply H0. eapply par_body_n__Sn. assumption.
    + split.
      * rewrite update_eq. reflexivity.
      * inversion Hst'. destruct H1. rewrite update_neq.
        assumption.
        destruct (eq_id_dec X Y) eqn:Hxy. inversion Hxy. assumption.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

