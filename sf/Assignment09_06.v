Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
  intros.
  eapply hoare_seq with (Q:= (fun st => st X + st Y = m)).
  eapply hoare_consequence_post. apply hoare_while.
  eapply hoare_seq. apply hoare_asgn. eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assert_implies, assn_sub, update. simpl. intros. destruct H.
  rewrite negb_true_iff in H0. rewrite beq_nat_false_iff in H0. omega.
  unfold assert_implies, assn_sub, update. simpl. intros. destruct H.
  rewrite negb_false_iff in H0. rewrite beq_nat_true_iff in H0. omega.
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assert_implies, assn_sub, update. simpl. intros. omega.
Qed.

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  
