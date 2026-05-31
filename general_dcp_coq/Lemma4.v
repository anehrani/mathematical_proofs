From Stdlib Require Import List.
Require Import Lemma1.
Require Import Lemma3.
Import ListNotations.

Section PhaseTransitionRule.

Context {A B : Type}.

Notation rotateA := (@move_top_to_bottom A).
Notation rotateB := (@move_top_to_bottom B).

Definition phase_state
    (initial_A : list A)
    (initial_B : list B)
    (i j : nat)
    (c : config) : Prop :=
  deck_A c = Nat.iter i rotateA initial_A /\
  deck_B c = Nat.iter j rotateB initial_B.

Theorem lemma4_phase_transition_rule :
  forall phi initial_A initial_B i j c1 o c2,
    phase_state initial_A initial_B i j c1 ->
    step phi c1 o c2 ->
    match o with
    | WA => phase_state initial_A initial_B i (S j) c2
    | WB => phase_state initial_A initial_B (S i) j c2
    | NN => phase_state initial_A initial_B (S i) (S j) c2
    | TT => True
    end.
Proof.
  intros phi initial_A initial_B i j c1 o c2 Hstate Hstep.
  destruct Hstate as [HA HB].
  inversion Hstep; subst; simpl in *.
  - split.
    + exact HA.
    + change (bs ++ [b] = rotateB (Nat.iter j rotateB initial_B)).
      rewrite <- HB.
      reflexivity.
  - split.
    + change (as_ ++ [a] = rotateA (Nat.iter i rotateA initial_A)).
      rewrite <- HA.
      reflexivity.
    + exact HB.
  - exact I.
  - split.
    + change (as_ ++ [a] = rotateA (Nat.iter i rotateA initial_A)).
      rewrite <- HA.
      reflexivity.
    + change (bs ++ [b] = rotateB (Nat.iter j rotateB initial_B)).
      rewrite <- HB.
      reflexivity.
Qed.

End PhaseTransitionRule.