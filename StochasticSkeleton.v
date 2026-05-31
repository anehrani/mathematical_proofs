From Stdlib Require Import List Arith Lia Permutation.
Require Import LowerBound.
Import ListNotations.

Section StochasticSkeleton.

Definition canonical_start (n : nat) : LowerBound.config :=
  {| LowerBound.deck_A := seq 0 n;
     LowerBound.deck_B := seq 0 n |}.

Definition term_event (n : nat) (phi : nat -> nat -> LowerBound.outcome) : Prop :=
  exists os,
    LowerBound.game phi (canonical_start n) os.

Definition feasibility_event (n : nat) (phi : nat -> nat -> LowerBound.outcome) : Prop :=
  exists da db os,
    Permutation (seq 0 n) da /\
    Permutation (seq 0 n) db /\
    LowerBound.game phi {| LowerBound.deck_A := da; LowerBound.deck_B := db |} os.

Definition all_diagonal_tt (n : nat) (phi : nat -> nat -> LowerBound.outcome) : Prop :=
  forall i,
    i < n ->
    phi i i = LowerBound.TT.

Lemma runs_all_diagonal_tt_from_offset :
  forall n k phi,
    (forall i, i < n -> phi (k + i) (k + i) = LowerBound.TT) ->
    LowerBound.runs phi
      {| LowerBound.deck_A := seq k n;
         LowerBound.deck_B := seq k n |}
      (repeat LowerBound.TT n)
      {| LowerBound.deck_A := []; LowerBound.deck_B := [] |}.
Proof.
  induction n as [|n IH]; intros k phi Hdiag.
  - simpl.
    apply LowerBound.RunsNil.
  - simpl.
    eapply LowerBound.RunsCons.
    + assert (Hk : phi k k = LowerBound.TT).
      {
        assert (Hk0 : phi (k + 0) (k + 0) = LowerBound.TT).
        {
          apply Hdiag.
          lia.
        }
        replace (k + 0) with k in Hk0 by lia.
        replace (k + 0) with k in Hk0 by lia.
        exact Hk0.
      }
      apply (LowerBound.StepTT phi k (seq (S k) n) k (seq (S k) n)).
      exact Hk.
    + assert (Hdiag_tail : forall i, i < n -> phi (S k + i) (S k + i) = LowerBound.TT).
      {
        intros i Hi.
        replace (S k + i) with (k + S i) by lia.
        replace (S k + i) with (k + S i) by lia.
        apply Hdiag.
        lia.
      }
      specialize (IH (S k) phi Hdiag_tail).
      exact IH.
Qed.

Theorem all_diagonal_tt_implies_game_canonical :
  forall n phi,
    all_diagonal_tt n phi ->
    LowerBound.game phi (canonical_start n) (repeat LowerBound.TT n).
Proof.
  intros n phi Hdiag.
  unfold LowerBound.game, canonical_start.
  apply runs_all_diagonal_tt_from_offset.
  intros i Hi.
  apply Hdiag.
  exact Hi.
Qed.

Corollary all_diagonal_tt_implies_term_event :
  forall n phi,
    all_diagonal_tt n phi ->
    term_event n phi.
Proof.
  intros n phi Hdiag.
  exists (repeat LowerBound.TT n).
  apply all_diagonal_tt_implies_game_canonical.
  exact Hdiag.
Qed.

Theorem term_event_implies_feasibility_event :
  forall n phi,
    term_event n phi ->
    feasibility_event n phi.
Proof.
  intros n phi [os Hgame].
  exists (seq 0 n), (seq 0 n), os.
  repeat split.
  - apply Permutation_refl.
  - apply Permutation_refl.
  - exact Hgame.
Qed.

Corollary all_diagonal_tt_implies_feasibility_event :
  forall n phi,
    all_diagonal_tt n phi ->
    feasibility_event n phi.
Proof.
  intros n phi Hdiag.
  apply term_event_implies_feasibility_event.
  apply all_diagonal_tt_implies_term_event.
  exact Hdiag.
Qed.

Corollary all_diagonal_tt_implies_duration_n :
  forall n phi,
    all_diagonal_tt n phi ->
    exists os,
      LowerBound.game phi (canonical_start n) os /\
      LowerBound.duration os = n.
Proof.
  intros n phi Hdiag.
  exists (repeat LowerBound.TT n).
  split.
  - apply all_diagonal_tt_implies_game_canonical.
    exact Hdiag.
  - unfold LowerBound.duration.
    rewrite repeat_length.
    reflexivity.
Qed.

End StochasticSkeleton.
