From Stdlib Require Import Reals Lra Lia.
Require Import LowerBound StochasticSkeleton.

Open Scope R_scope.

Section StochasticBounds.

Variable n : nat.
Hypothesis Hn : (n >= 1)%nat.

Variable Omega : Type.
Variable phi_of : Omega -> nat -> nat -> LowerBound.outcome.

Definition term_event (w : Omega) : Prop :=
  exists os,
    LowerBound.game (phi_of w) (canonical_start n) os.

Definition diag_tt_event (w : Omega) : Prop :=
  all_diagonal_tt n (phi_of w).

(* Abstract event corresponding to the final-phase fresh TT condition used in Lemma 16. *)
Variable final_phase_fresh_tie_event : Omega -> Prop.

Variable Pr : (Omega -> Prop) -> R.
Variable p : R.

(* Paper-facing feasibility event E_n: existence of some terminating initial ordering. *)
Variable feasibility_event : Omega -> Prop.

Hypothesis Pr_monotone :
  forall A B : Omega -> Prop,
    (forall w, A w -> B w) ->
    Pr A <= Pr B.

Hypothesis Pr_diag_tt_event :
  Pr diag_tt_event = p ^ n.

Hypothesis term_implies_final_phase_fresh_tie :
  forall w,
    term_event w ->
    final_phase_fresh_tie_event w.

Hypothesis Pr_final_phase_fresh_tie_le_p :
  Pr final_phase_fresh_tie_event <= p.

Hypothesis term_implies_feasibility_event :
  forall w,
    term_event w ->
    feasibility_event w.

Lemma diag_tt_event_implies_term_event :
  forall w,
    diag_tt_event w -> term_event w.
Proof.
  intros w Hdiag.
  unfold diag_tt_event in Hdiag.
  unfold term_event.
  apply all_diagonal_tt_implies_term_event.
  exact Hdiag.
Qed.

Theorem lemma17_termination_floor :
  p ^ n <= Pr term_event.
Proof.
  pose proof (Pr_monotone diag_tt_event term_event diag_tt_event_implies_term_event) as Hmono.
  rewrite Pr_diag_tt_event in Hmono.
  lra.
Qed.

Theorem lemma16_termination_ceiling :
  Pr term_event <= p.
Proof.
  eapply Rle_trans.
  - apply (Pr_monotone term_event final_phase_fresh_tie_event).
    exact term_implies_final_phase_fresh_tie.
  - exact Pr_final_phase_fresh_tie_le_p.
Qed.

Definition termination_probability : R := Pr term_event.

Definition feasibility_probability : R := Pr feasibility_event.

Theorem termination_subset_feasibility_event :
  forall w,
    term_event w ->
    feasibility_event w.
Proof.
  intros w Hterm.
  apply term_implies_feasibility_event.
  exact Hterm.
Qed.

Theorem termination_probability_le_feasibility_probability :
  Pr term_event <= Pr feasibility_event.
Proof.
  apply (Pr_monotone term_event feasibility_event).
  exact termination_subset_feasibility_event.
Qed.

Theorem termination_vs_feasibility_paper_form :
  termination_probability <= feasibility_probability.
Proof.
  unfold termination_probability, feasibility_probability.
  apply termination_probability_le_feasibility_probability.
Qed.

Theorem lemma16_paper_form :
  termination_probability <= p.
Proof.
  unfold termination_probability.
  apply lemma16_termination_ceiling.
Qed.

Theorem lemma17_paper_form :
  p ^ n <= termination_probability.
Proof.
  unfold termination_probability.
  apply lemma17_termination_floor.
Qed.

Theorem lemmas16_17_paper_form :
  p ^ n <= termination_probability <= p.
Proof.
  split.
  - apply lemma17_paper_form.
  - apply lemma16_paper_form.
Qed.

Corollary lemma16_uniform_ceiling :
  p = (1 / 4) ->
  Pr term_event <= (1 / 4).
Proof.
  intro Hp.
  rewrite <- Hp.
  apply lemma16_termination_ceiling.
Qed.

Corollary lemma17_uniform_floor :
  p = (1 / 4) ->
  (1 / 4) ^ n <= Pr term_event.
Proof.
  intro Hp.
  rewrite <- Hp.
  apply lemma17_termination_floor.
Qed.

Corollary termination_probability_sandwich_uniform :
  p = (1 / 4) ->
  (1 / 4) ^ n <= Pr term_event <= (1 / 4).
Proof.
  intro Hp.
  split.
  - apply lemma17_uniform_floor.
    exact Hp.
  - apply lemma16_uniform_ceiling.
    exact Hp.
Qed.

Corollary termination_probability_sandwich :
  p ^ n <= Pr term_event <= p.
Proof.
  split.
  - apply lemma17_termination_floor.
  - apply lemma16_termination_ceiling.
Qed.

End StochasticBounds.

Section StochasticBoundsConcrete.

Variable n : nat.
Variable Omega : Type.
Variable phi_of : Omega -> nat -> nat -> LowerBound.outcome.
Variable Pr : (Omega -> Prop) -> R.

Hypothesis Pr_monotone_concrete :
  forall A B : Omega -> Prop,
    (forall w, A w -> B w) ->
    Pr A <= Pr B.

Definition term_event_concrete (w : Omega) : Prop :=
  StochasticBounds.term_event n Omega phi_of w.

Definition feasibility_event_concrete (w : Omega) : Prop :=
  StochasticSkeleton.feasibility_event n (phi_of w).

Definition termination_probability_concrete : R := Pr term_event_concrete.
Definition feasibility_probability_concrete : R := Pr feasibility_event_concrete.

Theorem term_event_concrete_implies_feasibility_event_concrete :
  forall w,
    term_event_concrete w ->
    feasibility_event_concrete w.
Proof.
  intros w Hterm.
  unfold term_event_concrete, feasibility_event_concrete in *.
  apply (StochasticSkeleton.term_event_implies_feasibility_event n (phi_of w)).
  exact Hterm.
Qed.

Theorem termination_probability_le_feasibility_probability_concrete :
  termination_probability_concrete <= feasibility_probability_concrete.
Proof.
  unfold termination_probability_concrete, feasibility_probability_concrete.
  apply (Pr_monotone_concrete term_event_concrete feasibility_event_concrete).
  exact term_event_concrete_implies_feasibility_event_concrete.
Qed.

End StochasticBoundsConcrete.
