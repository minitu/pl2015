Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  induction b; eauto; right; try (rename a into a1; rename a0 into a2);
  try (remember (aexp_strong_progress st a1) as Ha1; clear HeqHa1;
    remember (aexp_strong_progress st a2) as Ha2; clear HeqHa2;
    destruct Ha1 as [[? ?] | [? ?]];
    destruct Ha2 as [[? ?] | [? ?]]; subst; eauto).
  - destruct IHb as [[? | ?] | [? ?]]; subst; eauto.
  - destruct IHb1 as [[? | ?] | [? ?]]; destruct IHb2 as [[? | ?] | [? ?]]; subst; eauto.
Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.

