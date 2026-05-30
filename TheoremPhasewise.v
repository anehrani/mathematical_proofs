From Stdlib Require Import List Arith Lia.
Import ListNotations.

Section PhasewiseBound.

Definition state := (nat * nat)%type.

Definition bounded_state (m : nat) (s : state) : Prop :=
  fst s < m /\ snd s < m.

Definition phase_space (m : nat) : list state :=
  list_prod (seq 0 m) (seq 0 m).

Lemma bounded_in_phase_space :
  forall m i j,
    i < m ->
    j < m ->
    In (i, j) (phase_space m).
Proof.
  intros m i j Hi Hj.
  unfold phase_space.
  apply in_prod.
  - apply in_seq. lia.
  - apply in_seq. lia.
Qed.

Lemma bounded_list_in_phase_space :
  forall m states,
    Forall (bounded_state m) states ->
    incl states (phase_space m).
Proof.
  intros m states Hbounded s Hin.
  apply Forall_forall with (x := s) in Hbounded; [| exact Hin].
  destruct Hbounded as [Hs1 Hs2].
  destruct s as [i j].
  simpl in *.
  apply bounded_in_phase_space; assumption.
Qed.

Lemma phase_space_length :
  forall m,
    length (phase_space m) = m * m.
Proof.
  intro m.
  unfold phase_space.
  change (length (list_prod (seq 0 m) (seq 0 m)) = m * m).
  rewrite length_prod.
  rewrite !length_seq.
  lia.
Qed.

Theorem theorem_phasewise_bound :
  forall m visited forbidden,
    NoDup visited ->
    NoDup forbidden ->
    (forall s, In s visited -> ~ In s forbidden) ->
    Forall (bounded_state m) visited ->
    Forall (bounded_state m) forbidden ->
    length forbidden = m - 1 ->
    length visited <= m * m - m + 1.
Proof.
  intros m visited forbidden HnodupV HnodupF Hdisj HboundedV HboundedF HlenF.
  assert (HnodupVF : NoDup (visited ++ forbidden)).
  {
    apply NoDup_app.
    - exact HnodupV.
    - exact HnodupF.
    - intros s HinV HinF.
      exact (Hdisj s HinV HinF).
  }
  assert (Hincl : incl (visited ++ forbidden) (phase_space m)).
  {
    intros s Hin.
    apply in_app_or in Hin.
    destruct Hin as [HinV | HinF].
    - apply (bounded_list_in_phase_space _ _ HboundedV); exact HinV.
    - apply (bounded_list_in_phase_space _ _ HboundedF); exact HinF.
  }
  pose proof (NoDup_incl_length HnodupVF Hincl) as Hcount.
  rewrite length_app in Hcount.
  rewrite phase_space_length in Hcount.
  rewrite HlenF in Hcount.
  lia.
Qed.

End PhasewiseBound.