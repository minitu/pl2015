Require Export Assignment12_04.

(* problem #05: 20 points *)

(** Translate this informal recursive definition into one using [fix]:
<<
   halve = 
     \x:Nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
*)

Notation x := (Id 0).
Notation f := (Id 1).

Definition halve : tm :=
  tfix (tabs f (TArrow TNat TNat) (tabs x TNat (tif0 (tvar x) (tnat 0) (tif0 (tpred (tvar x)) (tnat 0) (tsucc (tapp (tvar f) (tpred (tpred (tvar x))))))))).

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
  (* unfold halve; eauto 10. *)
  unfold halve; eauto 10.
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
  (* unfold halve; normalize. *)
  unfold halve; normalize.
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
  (* unfold halve; normalize. *)
  unfold halve; normalize.
Qed.

Lemma multi_succ_congru: forall t t',
  t ==>* t' -> tsucc t ==>* tsucc t'.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply multi_step with (tsucc y). apply ST_Succ1. assumption. assumption.
Qed.

Lemma multi_succ: forall t n,
  t ==>* tnat n -> tsucc t ==>* tnat (S n).
Proof.
  intros. eapply multi_trans with (tsucc (tnat n)).
  apply multi_succ_congru. assumption. (* induction H; eauto. *)
  eapply multi_step. apply ST_SuccNat. apply multi_refl.
Qed.

Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
  induction n.
  - unfold halve. normalize.
  - unfold halve in *. simpl. rewrite plus_comm. simpl.
    eapply multi_step. apply ST_AppFix; auto.
    eapply multi_step. apply ST_App1. auto. simpl.
    eapply multi_step. apply ST_AppAbs. auto. simpl.
    eapply multi_step. apply ST_If0Nonzero.
    eapply multi_step. apply ST_If01. apply ST_PredNat. simpl.
    eapply multi_step. apply ST_If0Nonzero.
    eapply multi_step. apply ST_Succ1. apply ST_App2. auto. apply ST_Pred. apply ST_PredNat. simpl.
    eapply multi_step. apply ST_Succ1. apply ST_App2. auto. apply ST_PredNat. simpl.
    apply multi_succ. assumption.
Qed.

(*-- Check --*)

Check conj halve_type (conj halve_10 halve_11) :
  empty |- halve \in TArrow TNat TNat /\
  tapp halve (tnat 10) ==>* tnat 5 /\ 
  tapp halve (tnat 11) ==>* tnat 5.

Check halve_correct: forall n,
   tapp halve (tnat (n + n)) ==>* tnat n.

