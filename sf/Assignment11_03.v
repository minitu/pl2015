Require Export Assignment11_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros. generalize dependent y2. induction H; intros;
  inversion H0; subst; try (solve by inversion); try reflexivity.
  - rewrite (IHstep t1'0). reflexivity. assumption.
  - rewrite (IHstep t1'0). reflexivity. assumption.
  - assert (value t1). right. assumption.
    apply value_is_nf in H1. unfold normal_form, not in H1.
    inversion H2; subst. exfalso. apply H1...
  - assert (value y2). right. assumption.
    apply value_is_nf in H1. unfold normal_form, not in H1.
    inversion H; subst. exfalso. apply H1...
  - rewrite (IHstep t1'0). reflexivity. assumption.
  - assert (value t1). right. assumption.
    apply value_is_nf in H1. unfold normal_form, not in H1.
    inversion H2; subst. exfalso. apply H1...
  - assert (value t0). right. assumption.
    apply value_is_nf in H1. unfold normal_form, not in H1.
    inversion H; subst. exfalso. apply H1...
  - rewrite (IHstep t1'0). reflexivity. assumption.
Qed.

(*-- Check --*)
Check step_deterministic:
  deterministic step.

