Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{ c = 0 + c /\ 0 = 0}}
  X ::= 0;;
    {{ c = X + c /\ 0 = 0 }}
  Y ::= 0;;
    {{ c = X + c /\ Y = 0 }}
  Z ::= c;;
    {{ Z = X + c /\ Y = 0 }}
  WHILE X <> a DO
      {{ Z = X + c /\ Y = 0 /\ x <> a }} ->>
      {{ Z + 1 = (X + 1) + c /\ Y = 0 }}
    X ::= X + 1;;
      {{ Z + 1 = X + c /\ Y = 0 }}
    Z ::= Z + 1
      {{ Z = X + c /\ Y = 0 }}
  END;;
    {{ Z = X + c /\ Y = 0 /\ X = a }} ->>
    {{ Z = Y + a + c }}
  WHILE Y <> b DO
      {{ Z = Y + a + c /\ Y <> b }} ->>
      {{ Z + 1 = (Y + 1) + a + c }}
    Y ::= Y + 1;;
      {{ Z + 1 = Y + a + c }}
    Z ::= Z + 1
      {{ Z = Y + a + c }}
  END
    {{ Z = Y + a + c /\ Y = b }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros.
  eapply hoare_consequence_post.
  apply hoare_seq with ((fun st => st Z = st X + c /\ st Y = 0) [Z |-> ANum c][Y |-> ANum 0]).
  apply hoare_seq with ((fun st => st Z = st X + c /\ st Y = 0)[Z |-> ANum c]).
  apply hoare_seq with (fun st => st Z = st X + c /\ st Y = 0).
  apply hoare_seq with (fun st => st Z = st Y + a + c).
  apply hoare_while. eapply hoare_consequence_pre. eapply hoare_seq.
  apply hoare_asgn. apply hoare_asgn.
  intros st H. destruct H. simpl in H0. apply negb_true in H0. apply beq_nat_false in H0.
  unfold assn_sub, update. simpl. omega.
  eapply hoare_consequence_post.
  apply hoare_while. eapply hoare_consequence_pre. eapply hoare_seq.
  apply hoare_asgn. apply hoare_asgn.
  intros st H. destruct H. simpl in H0. apply negb_true in H0. apply beq_nat_false in H0.
  unfold assn_sub, update. simpl. omega.
  intros st H. destruct H. destruct H. simpl in H0. apply negb_false in H0. apply beq_nat_true in H0. omega.
  apply hoare_asgn. apply hoare_asgn.
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros st H. unfold assn_sub, update. simpl. omega.
  intros st H. destruct H. simpl in H0. apply negb_false in H0. apply beq_nat_true in H0. omega.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

