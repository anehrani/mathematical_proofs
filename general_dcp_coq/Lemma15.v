From Stdlib Require Import List Lia Permutation.
Require Import Lemma1.
Require Import Lemma2.
Import ListNotations.

Section AlignmentSufficiency.

Context {A B : Type}.

Definition tt_trace (ps : list (A * B)) : list (A * B * outcome) :=
  map (fun p => (fst p, snd p, TT)) ps.

Lemma play_all_ties_from_pairs :
  forall (phi : A -> B -> outcome) ps,
    Forall (fun p => phi (fst p) (snd p) = TT) ps ->
    play phi
      {| deck_A := map fst ps; deck_B := map snd ps |}
      (tt_trace ps)
      {| deck_A := []; deck_B := [] |}.
Proof.
  intros phi ps Hties.
  induction ps as [|[a b] ps IH].
  - simpl.
    apply PlayNil.
  - simpl in Hties.
    inversion Hties as [|p ps' Hp Hrest]; subst p ps'.
    simpl.
    eapply PlayTT.
    + exact Hp.
    + exact (IH Hrest).
Qed.

Definition admits_terminating_ordering
  (phi : A -> B -> outcome) (as_ : list A) (bs : list B) : Prop :=
  exists da db tr,
    Permutation as_ da /\
    Permutation bs db /\
    game_trace phi {| deck_A := da; deck_B := db |} tr.

Theorem lemma15_alignment_sufficiency_general :
  forall (phi : A -> B -> outcome) (as_ : list A) (bs : list B),
    NoDup as_ ->
    NoDup bs ->
    admits_terminating_ordering phi as_ bs <->
    exists ps, perfect_matching_on phi as_ bs ps.
Proof.
  intros phi as_ bs HnodupA HnodupB.
  split.
  - intros [da [db [tr [HpermA0 [HpermB0 Hgame]]]]].
    assert (HnodupDa : NoDup da).
    {
      eapply Permutation_NoDup.
      - exact HpermA0.
      - exact HnodupA.
    }
    assert (HnodupDb : NoDup db).
    {
      eapply Permutation_NoDup.
      - exact HpermB0.
      - exact HnodupB.
    }
    destruct (lemma2_tie_matching phi {| deck_A := da; deck_B := db |} tr HnodupDa HnodupDb Hgame)
      as [Hforall [HpermA [HpermB [HndA HndB]]]].
    exists (tie_pairs tr).
    unfold perfect_matching_on.
    repeat split.
    + exact Hforall.
    + eapply Permutation_trans.
      * exact HpermA0.
      * exact HpermA.
    + eapply Permutation_trans.
      * exact HpermB0.
      * exact HpermB.
    + exact HndA.
    + exact HndB.
  - intros [ps Hpm].
    exists (map fst ps), (map snd ps), (tt_trace ps).
    unfold perfect_matching_on in Hpm.
    destruct Hpm as [Hforall [HpermA [HpermB [_ _]]]].
    split.
    + exact HpermA.
    + split.
      * exact HpermB.
      * unfold game_trace.
        apply play_all_ties_from_pairs.
        exact Hforall.
Qed.

End AlignmentSufficiency.

Definition canonical_cards (n : nat) : list nat := seq 0 n.

Definition E_n (n : nat) (phi : nat -> nat -> outcome) : Prop :=
  admits_terminating_ordering phi (canonical_cards n) (canonical_cards n).

Definition tie_set_contains_perfect_matching
  (n : nat) (phi : nat -> nat -> outcome) : Prop :=
  exists ps, perfect_matching_on phi (canonical_cards n) (canonical_cards n) ps.

Theorem lemma15_alignment_sufficiency_definition7 :
  forall n phi,
    E_n n phi <-> tie_set_contains_perfect_matching n phi.
Proof.
  intros n phi.
  unfold E_n, tie_set_contains_perfect_matching.
  apply lemma15_alignment_sufficiency_general.
  - unfold canonical_cards.
    apply seq_NoDup.
  - unfold canonical_cards.
    apply seq_NoDup.
Qed.
