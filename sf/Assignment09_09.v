Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{ 1 * X! = m! }}
  Y ::= 1;;
    {{ Y * X! = m! }}
  WHILE X <> 0
  DO   {{ Y * X! = m! /\ X <> 0 }} ->>
       {{ Y * X * (X - 1)! = m! }}
     Y ::= Y * X;;
       {{ Y * (X - 1)! = m! }}
     X ::= X - 1
       {{ Y * X! = m! }}
  END
    {{ Y * X! = m! /\ ~(X <> 0) }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros.
  apply hoare_seq with (fun st => st Y * fact (st X) = fact m).
  eapply hoare_consequence_post. apply hoare_while.
  eapply hoare_seq. apply hoare_asgn.
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assert_implies, assn_sub, update. simpl. intros.
  destruct H. apply negb_true in H0. apply beq_nat_false in H0. rewrite <- H.
  assert (st X * fact (st X - 1) = fact (st X)).
  induction (st X). tauto. simpl. rewrite <- minus_n_O. reflexivity.
  rewrite <- mult_assoc. rewrite H1. reflexivity.
  unfold assert_implies, assn_sub, update. simpl. intros.
  destruct H. apply negb_false in H0. apply beq_nat_true in H0. rewrite <- H.
  rewrite H0. simpl. omega.
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assert_implies, assn_sub, update. simpl. intros.
  rewrite H. omega.
Qed.

(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

