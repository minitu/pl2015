Require Export Assignment07_01.

(* problem #02: 10 points *)

Fixpoint optimize_1mult (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus e1 e2 =>
      APlus (optimize_1mult e1) (optimize_1mult e2)
  | AMinus e1 e2 =>
      AMinus (optimize_1mult e1) (optimize_1mult e2)
  | AMult (ANum 1) e2 =>
      optimize_1mult e2
  | AMult e1 (ANum 1) =>
      optimize_1mult e1
  | AMult e1 e2 =>
      AMult (optimize_1mult e1) (optimize_1mult e2)
  end.

(** Hint:
    If you use the tacticals [;], [try] and [omega] well,
    you can prove the following theorem in 5 lines.
 **)

Theorem optimize_1mult_sound: forall a,
  aeval (optimize_1mult a) = aeval a.
Proof.
  induction a; try (reflexivity); try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  destruct a1, a2.
  - destruct n; destruct n0.
    + reflexivity.
    + destruct n0.
      * reflexivity.
      * reflexivity.
    + destruct n.
      * reflexivity.
      * reflexivity.
    + destruct n, n0.
      * reflexivity.
      * simpl in *. omega.
      * simpl in *. omega.
      * reflexivity.
  - destruct n.
    + reflexivity.
    + destruct n.
      * simpl in *. omega.
      * simpl in *. rewrite IHa2. reflexivity.
  - destruct n.
    + reflexivity.
    + destruct n.
      * simpl in *. omega.
      * simpl in *. rewrite IHa2. reflexivity.
  - destruct n.
    + reflexivity.
    + destruct n.
      * simpl in *. omega.
      * simpl in *. rewrite IHa2. reflexivity.
  - destruct n.
    + simpl in *. omega.
    + destruct n.
      * simpl in *. omega.
      * simpl in *. rewrite IHa1. reflexivity.
  - simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
  - destruct n.
    + simpl in *. omega.
    + destruct n.
      * simpl in *. omega.
      * simpl in *. rewrite IHa1. reflexivity.
  - simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
  - destruct n.
    + simpl in *. omega.
    + destruct n.
      * simpl in *. omega.
      * simpl in *. rewrite IHa1. reflexivity.
  - simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
Qed. 
      