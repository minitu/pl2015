Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
  intros. eapply hoare_consequence.
  apply hoare_while. eapply hoare_consequence_pre.
  apply hoare_seq with (Q := ((fun st => st X + st Y = n + m)[X |-> (AMinus (AId X) (ANum 1))])).
  apply hoare_asgn. apply hoare_asgn.
  unfold assert_implies, assn_sub, update. simpl. intros.
  destruct H. apply negb_true in H0. apply beq_nat_false in H0. omega.
  unfold assert_implies, assn_sub, update. intros.
  destruct H. omega.
  unfold assert_implies, assn_sub, update. intros.
  destruct H. simpl in H0. apply negb_false in H0. apply beq_nat_true in H0. omega.
Qed.

(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.

