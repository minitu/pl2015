Require Export Assignment08_04.

(* problem #05: 20 points *)

(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)
Print aexp.
Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SPlus]
  | AMinus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMinus]
  | AMult e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMult]
  end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Lemma s_execute_app : forall (st : state) (prog1 prog2 : list sinstr) (stack : list nat),
  s_execute st stack (prog1 ++ prog2) = s_execute st (s_execute st stack prog1) prog2.
Proof.
  intros st prog1. induction prog1.
  - intros. reflexivity.
  - intros. destruct a; try (simpl; apply IHprog1);
    destruct stack as [| n1 stack1]; try (simpl; apply IHprog1);
    destruct stack1 as [| n2 stack2]; try (simpl; apply IHprog1).
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  generalize dependent (@nil nat).
  intros. generalize dependent l.
  induction e; intros.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. repeat rewrite s_execute_app. rewrite IHe1. rewrite IHe2. simpl. reflexivity.
  - simpl. repeat rewrite s_execute_app. rewrite IHe1. rewrite IHe2. simpl. reflexivity.
  - simpl. repeat rewrite s_execute_app. rewrite IHe1. rewrite IHe2. simpl. reflexivity.
Qed.

(*-- Check --*)
Check s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].

Check s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].

