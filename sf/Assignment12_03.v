Require Export Assignment12_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (types_unique)  *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)

Lemma type_is_unique: forall t G T T'
    (TYPED: G |- t \in T)
    (TYPED': G |- t \in T'),
  T = T'.
Proof with auto.
  intros. generalize dependent T'. induction TYPED; intros; inversion TYPED'; subst; auto.
  - rewrite H in H2. inversion H2...
  - apply IHTYPED in H4. rewrite H4...
  - apply IHTYPED1 in H2. inversion H2...
  - apply IHTYPED1 in H2. apply IHTYPED2 in H4. rewrite H2. rewrite H4...
  - apply IHTYPED in H1. inversion H1...
  - apply IHTYPED in H1. inversion H1...
  - apply IHTYPED1 in H4. subst. apply IHTYPED2 in H5...
  - apply IHTYPED in H3. rewrite H3...
  - apply IHTYPED in H3. rewrite H3...
  - apply IHTYPED1 in H6. inversion H6; subst. clear H6. apply IHTYPED2 in H7...
  - apply IHTYPED in H1. inversion H1; subst...
Qed.

(*-- Check --*)
Check type_is_unique: forall t G T T'
    (HTyped: G |- t \in T)
    (HTyped': G |- t \in T'),
  T = T'.

