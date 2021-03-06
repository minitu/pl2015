Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Lemma arrow_inv : ~ (exists T T', TArrow T T' = T).
Proof.
  intro Hc. inversion Hc. induction x; intros; try solve by inversion 2.
  inversion H. inversion H0. eauto.
Qed.

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
  intros Hc. destruct Hc as [S [T H]].
  inversion H; subst; clear H.
  inversion H5; subst; clear H5.
  inversion H2; subst; clear H2.
  inversion H4; subst; clear H4.
  rewrite extend_eq in H1. rewrite extend_eq in H2. rewrite H1 in H2. inversion H2.
  remember arrow_inv as H0c. clear HeqH0c. eauto.
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).

