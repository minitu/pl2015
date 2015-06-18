Require Export Assignment12_05.

(* problem #06: 10 points *)

Theorem MoreStlc_value_is_nf: forall v t,
  value v -> v ==> t -> False.
Proof with eauto.
  intros; generalize dependent t; assert (normal_form step v)...
  unfold normal_form; intros; induction H; intros contra; destruct contra;
  try solve by inversion; try inversion H0; try inversion H1; subst...
Qed.

Hint Resolve MoreStlc_value_is_nf.

Theorem MoreStlc_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic; intros; generalize dependent y2;
  induction H as [| |? ? ? ? P| | | | | |? ? ? ? P| | | | | |? ? ? ? P| |? ? ? P|
  |? ? ? P| | | | | | | | |? ? ? ? P| | | ? ? ? ? ? ? P| |? ? ? P]; intros;
  inversion H0; subst; try solve by inversion;
  try replace t0'0 with t0';
  try replace t1'0 with t1';
  try replace t2'0 with t2';
  eauto; exfalso...
Qed.

(* MoreStlc_value_is_nf & MoreStlc_deterministic
   from https://github.com/snu-sf/pl2015/issues/154 *)

Lemma tloop_back: exists p q, tapp tloop (tnat 0) ==> p /\ p ==> q /\ q ==> tapp tloop (tnat 0).
  eexists. eexists. unfold tloop. split.
  - eauto.
  - split.
    + eauto.
    + simpl. constructor. constructor.
Qed.

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof.
  intros Hc. destruct Hc as [t H]. destruct H.
  remember tloop_back. clear Heqe. destruct e as [p [q [H1 [H2 H3]]]].
  unfold normal_form in H0. apply H0. clear H0.
  generalize dependent p. generalize dependent q.
  induction H; intros. exists p. assumption.
  inversion H0; subst. remember MoreStlc_deterministic. unfold deterministic in d.
  assert (p = z). eapply d. apply H1. apply H. subst.
  eapply IHmulti. apply H. apply H2. apply H3. 
  remember MoreStlc_deterministic; unfold deterministic in d.
  assert (y = p). eapply d. apply H. apply H1. subst.
  eapply IHmulti. apply H. apply H2. apply H3.
Qed.

(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.

