Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  induction c.
  - intros. exists st. constructor.
  - intros. exists (update st i (aeval st a)). constructor. reflexivity.
  - intros. inversion NOWHL. rewrite andb_true_iff in H0. destruct H0.
    assert (exists st1, c1 / st || st1) as c1_term.
    apply IHc1. assumption. inversion c1_term as [st1 c_st1].
    assert (exists st2, c2 / st1 || st2) as c2_term.
    apply IHc2. assumption. inversion c2_term as [st2 c_st2].
    exists st2. apply E_Seq with st1. assumption. assumption.
  - intros. inversion NOWHL. rewrite andb_true_iff in H0. destruct H0.
    assert (exists st1, c1 / st || st1) as c1_term.
    apply IHc1. assumption. inversion c1_term as [st1 c_st1].
    assert (exists st2, c2 / st || st2) as c2_term.
    apply IHc2. assumption. inversion c2_term as [st2 c_st2].
    remember (beval st b) as beval_b. destruct beval_b.
    exists st1. apply E_IfTrue. symmetry. assumption. assumption.
    exists st2. apply E_IfFalse. symmetry. assumption. assumption.
  - intros. inversion NOWHL.
Qed.

(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

