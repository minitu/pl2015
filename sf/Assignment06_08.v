Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros. generalize dependent l2.
  induction l1.
  - simpl. reflexivity.
  - simpl. intros. rewrite <- IHl1. reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros. induction H.
  - exists []. simpl. exists l. reflexivity.
  - inversion IHappears_in as [l1 Hl1]. inversion Hl1 as [l2 Hl2].
    rewrite Hl2. exists (b :: l1). exists l2. reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | rep_here : forall (x : X) (l : list X), appears_in x l -> repeats (x :: l)
  | rep_later : forall (x : X) (l : list X), repeats l -> repeats (x :: l)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Lemma ai_app_comm : forall (X : Type) (x : X) (l1 l2 : list X),
  appears_in x (l1 ++ l2) -> appears_in x (l2 ++ l1).
Proof.
  intros. SearchAbout appears_in. apply app_appears_in.
  apply or_commut. apply appears_in_app. apply H.
Qed.

Lemma ai_drop_if_diff : forall (X : Type) (x y : X) (l : list X),
  x <> y -> appears_in x (y :: l) -> appears_in x l.
Proof.
  intros.
  inversion H0.
  - rewrite H2 in H. unfold not in H. apply ex_falso_quodlibet. apply H. reflexivity.
  - apply H2.
Qed.

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros X l1. induction l1 as [|x l1'].
   - intros l2 em H Hlen. inversion Hlen.
   - intros l2 em H Hlen. remember (em (appears_in x l1')) as em'. destruct em'.
     + apply rep_here. apply a.
     + apply rep_later. destruct (appears_in_app_split X x l2) as [lw Pf].
       * apply H. apply ai_here.
       * destruct Pf as [lw' Pf'].
         apply IHl1' with (lw ++ lw').
         apply em.
         intros. assert (appears_in x0 l2).
         apply H. apply ai_later. apply H0.
         assert (x <> x0).
         unfold not. unfold not in n. intros. apply n. rewrite H2. apply H0.
         rewrite Pf' in H1. apply ai_app_comm in H1. simpl in H1.
         apply ai_drop_if_diff in H1. apply ai_app_comm. apply H1.
         destruct (em (x=x0)).
         rewrite H3 in H2. unfold not in H2. apply ex_falso_quodlibet. apply H2. reflexivity.
         unfold not. unfold not in H2. intros. apply H2. rewrite H4. reflexivity.
         rewrite Pf' in Hlen. simpl in Hlen. assert (length (lw ++ x :: lw') = S (length (lw ++ lw'))). rewrite app_length. simpl. rewrite <- plus_n_Sm.
         rewrite app_length. reflexivity.
         rewrite H0 in Hlen. unfold lt in Hlen. unfold lt. apply Sn_le_Sm__n_le_m in Hlen. apply Hlen.
Qed.

