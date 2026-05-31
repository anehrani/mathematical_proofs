From Stdlib Require Import List Reals Lra.
Require Import Lemma1 Proposition1 FiniteProbability.
Import ListNotations.

Open Scope R_scope.

Section Proposition1Finite.

Variable Omega : Type.
Variable universe : list Omega.
Hypothesis universe_nonempty : universe <> [].

Variable phi_of : Omega -> nat -> nat -> Lemma1.outcome.
Variable binom : nat -> nat -> nat.
Variable hall_obstruction_event : nat -> Omega -> Prop.

Hypothesis hall_obstruction_reduction :
  forall n w,
    ~ Proposition1.E_event Omega phi_of n w -> hall_obstruction_event n w.

Hypothesis hall_obstruction_bound :
  forall n,
    FiniteProbability.Pr Omega universe (hall_obstruction_event n)
    <= Proposition1.hall_union_bound binom n (3 / 4).

Theorem proposition1_via_hall_obstruction_finite :
  forall n,
    1 - Proposition1.hall_union_bound binom n (3 / 4)
    <= FiniteProbability.Pr Omega universe (Proposition1.E_event Omega phi_of n).
Proof.
  intro n.
  eapply Proposition1.proposition1_via_hall_obstruction
    with
      (hall_obstruction_event := hall_obstruction_event)
      (Pr := FiniteProbability.Pr Omega universe)
      (phi_of := phi_of)
      (binom := binom).
  - exact (FiniteProbability.Pr_complement_rule Omega universe universe_nonempty).
  - exact (FiniteProbability.Pr_monotone Omega universe universe_nonempty).
  - exact (hall_obstruction_reduction n).
  - exact (hall_obstruction_bound n).
Qed.

Theorem feasibility_probability_paper_form_finite :
  forall n,
    FiniteProbability.Pr Omega universe (fun w => ~ Proposition1.E_event Omega phi_of n w)
    <= Proposition1.hall_union_bound binom n (3 / 4) ->
    1 - Proposition1.hall_union_bound binom n (3 / 4)
    <= FiniteProbability.Pr Omega universe (Proposition1.E_event Omega phi_of n).
Proof.
  intros n Hhall.
  eapply Proposition1.proposition1_feasibility_probability_explicit
    with
      (Pr := FiniteProbability.Pr Omega universe)
      (phi_of := phi_of)
      (binom := binom)
      (n := n).
  - exact (FiniteProbability.Pr_complement_rule Omega universe universe_nonempty).
  - exact Hhall.
Qed.

End Proposition1Finite.

Section Proposition1FiniteDirect.

Variable Omega : Type.
Variable universe : list Omega.
Hypothesis universe_nonempty : universe <> [].

Variable phi_of : Omega -> nat -> nat -> Lemma1.outcome.
Variable binom : nat -> nat -> nat.

Theorem proposition1_from_failure_bound_finite :
  forall n,
    FiniteProbability.Pr Omega universe
      (fun w => ~ Proposition1.E_event Omega phi_of n w)
      <= Proposition1.hall_union_bound binom n (3 / 4) ->
    1 - Proposition1.hall_union_bound binom n (3 / 4)
    <= FiniteProbability.Pr Omega universe (Proposition1.E_event Omega phi_of n).
Proof.
  intros n Hfail.
  pose proof
    (FiniteProbability.Pr_complement_rule
      Omega universe universe_nonempty
      (Proposition1.E_event Omega phi_of n)) as Hcomp.
  lra.
Qed.

Theorem feasibility_probability_paper_form_from_failure_bound_finite :
  forall n,
    FiniteProbability.Pr Omega universe
      (fun w => ~ Proposition1.E_event Omega phi_of n w)
      <= Proposition1.hall_union_bound binom n (3 / 4) ->
    1 - Proposition1.hall_union_bound binom n (3 / 4)
    <= FiniteProbability.Pr Omega universe (Proposition1.E_event Omega phi_of n).
Proof.
  intros n Hfail.
  apply proposition1_from_failure_bound_finite.
  exact Hfail.
Qed.

End Proposition1FiniteDirect.
