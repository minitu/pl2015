Require Export Assignment11_09.

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)
Print tm.
Fixpoint tycheck (t: tm) (T: ty) : bool :=
  match t with
  | ttrue => match T with
             | TBool => true
             | _ => false
             end
  | tfalse => match T with
              | TBool => true
              | _ => false
              end
  | tif t1 t2 t3 => if (andb (tycheck t1 TBool) (andb (tycheck t2 T) (tycheck t3 T))) then true else false
  | tzero => match T with
             | TNat => true
             | _ => false
             end
  | tsucc t => if (tycheck t TNat) then match T with
                                        | TNat => true
                                        | _ => false
                                        end
                                   else false
  | tpred t => if (tycheck t TNat) then match T with
                                        | TNat => true
                                        | _ => false
                                        end
                                   else false
  | tiszero t => if (tycheck t TNat) then match T with
                                          | TBool => true
                                          | _ => false
                                          end
                                     else false
end.

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true.
Proof. reflexivity. Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false.
Proof. reflexivity. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
  induction t; intros; destruct T; try constructor; try (solve by inversion);
  inversion TYCHK; try (apply andb_prop in H0; destruct H0; clear H0;
  apply andb_prop in H; destruct H; apply andb_prop in H0; destruct H0; auto);
  destruct (tycheck t TNat) eqn:tc; try (solve by inversion); auto.  
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
  induction t; induction T; intros; auto; try solve by inversion;
  try (inversion HASTY; subst; simpl; apply IHt1 in H2; apply IHt2 in H4; apply IHt3 in H5;
  rewrite H2; rewrite H4; rewrite H5; reflexivity);
  inversion HASTY; subst; apply IHt in H0; simpl; rewrite H0; reflexivity.
Qed.

(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
