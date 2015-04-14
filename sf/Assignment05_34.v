Require Export Assignment05_33.

(* problem #34: 10 points *)

Lemma plus_lt_aux : forall a b c,
  a + b <= c -> a <= c.
Proof.
  induction b.
  - intros. rewrite plus_comm in H. simpl in H. apply H.
  - intros. apply IHb. apply le_trans with (m:=a+b) (n:=a+(S b)) (o:=c).
    + rewrite plus_comm with (n:=a) (m:=(S b)). simpl. apply le_S. rewrite plus_comm. apply le_n.
    + apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
  unfold lt. intros. split.
  - rewrite <- plus_Sn_m in H. apply plus_lt_aux in H. apply H.
  - rewrite plus_comm in H. rewrite <- plus_Sn_m in H. apply plus_lt_aux in H. apply H.
Qed.

