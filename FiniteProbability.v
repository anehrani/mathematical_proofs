From Stdlib Require Import List Lia Reals Lra ClassicalDescription.
Import ListNotations.

Section FiniteProbability.

Variable Omega : Type.
Variable universe : list Omega.
Hypothesis universe_nonempty : universe <> [].

Definition indicator (P : Prop) : nat :=
  if excluded_middle_informative P then 1 else 0.

Fixpoint count_event (A : Omega -> Prop) (xs : list Omega) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => indicator (A x) + count_event A xs'
  end.

Definition Pr (A : Omega -> Prop) : R :=
  INR (count_event A universe) / INR (length universe).

Lemma indicator_complement :
  forall P,
    indicator P + indicator (~ P) = 1.
Proof.
  intro P.
  unfold indicator.
  destruct (excluded_middle_informative P) as [HP|HnP].
  - destruct (excluded_middle_informative (~ P)) as [Hnp|Hnnp].
    + exfalso.
      apply Hnp.
      exact HP.
    + reflexivity.
  - destruct (excluded_middle_informative (~ P)) as [Hnp|Hnnp].
    + reflexivity.
    + exfalso.
      apply Hnnp.
      exact HnP.
Qed.

Lemma count_event_complement :
  forall A xs,
    count_event A xs + count_event (fun w => ~ A w) xs = length xs.
Proof.
  intros A xs.
  induction xs as [|x xs IH].
  - simpl.
    lia.
  - simpl.
    pose proof (indicator_complement (A x)) as Hic.
    lia.
Qed.

Lemma count_event_monotone :
  forall A B xs,
    (forall w, A w -> B w) ->
    count_event A xs <= count_event B xs.
Proof.
  intros A B xs Himp.
  induction xs as [|x xs IH].
  - simpl.
    lia.
  - simpl.
    assert (Hhead : indicator (A x) <= indicator (B x)).
    {
      unfold indicator.
      destruct (excluded_middle_informative (A x)) as [HAx|HnAx].
      - destruct (excluded_middle_informative (B x)) as [HBx|HnBx].
        + lia.
        + exfalso.
          apply HnBx.
          apply Himp.
          exact HAx.
      - destruct (excluded_middle_informative (B x)) as [HBx|HnBx].
        + lia.
        + lia.
    }
    lia.
Qed.

Lemma length_universe_pos :
  (length universe > 0)%nat.
Proof.
  destruct universe as [|x xs].
  - exfalso.
    apply universe_nonempty.
    reflexivity.
  - simpl.
    lia.
Qed.

Lemma Pr_complement_rule :
  forall A,
    (Pr A + Pr (fun w => ~ A w) = 1)%R.
Proof.
  intro A.
  unfold Pr.
  set (d := INR (length universe)).
  assert (Hnz : d <> 0%R).
  {
    apply not_0_INR.
    intro Hlen0.
    apply universe_nonempty.
    destruct universe as [|x xs].
    - reflexivity.
    - simpl in Hlen0.
      lia.
  }
  unfold d.
  unfold Rdiv.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- plus_INR.
  rewrite count_event_complement.
  field.
  exact Hnz.
Qed.

Lemma Pr_monotone :
  forall A B,
    (forall w, A w -> B w) ->
    (Pr A <= Pr B)%R.
Proof.
  intros A B Himp.
  unfold Pr.
  assert (Hden : INR (length universe) <> 0%R).
  {
    apply not_0_INR.
    pose proof length_universe_pos as Hpos.
    lia.
  }
  apply Rmult_le_reg_r with (r := INR (length universe)).
  - apply lt_0_INR.
    exact length_universe_pos.
  - unfold Rdiv.
    field_simplify.
    + apply le_INR.
      apply count_event_monotone.
      exact Himp.
    + exact Hden.
    + exact Hden.
Qed.

End FiniteProbability.
