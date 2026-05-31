From Stdlib Require Import Reals Lra Lia Arith.
Require Import Lemma1 Lemma15.

Open Scope R_scope.

Section Proposition1.

Variable Omega : Type.
Variable phi_of : Omega -> nat -> nat -> Lemma1.outcome.
Variable Pr : (Omega -> Prop) -> R.
Variable binom : nat -> nat -> nat.

Definition E_event (n : nat) (w : Omega) : Prop :=
  E_n n (phi_of w).

Definition hall_union_bound (n : nat) (q : R) : R :=
  sum_f_R0
    (fun i => INR (binom n (S i) * binom n i) * q ^ (S i * (n - i)))
    (Nat.pred n).

Variable hall_obstruction_event : nat -> Omega -> Prop.

Hypothesis complement_rule :
  forall A : Omega -> Prop,
    Pr A + Pr (fun w => ~ A w) = 1.

Hypothesis Pr_monotone :
  forall A B : Omega -> Prop,
    (forall w, A w -> B w) ->
    Pr A <= Pr B.

Lemma proposition1_from_failure_upper_bound :
  forall n UB,
    Pr (fun w => ~ E_event n w) <= UB ->
    1 - UB <= Pr (E_event n).
Proof.
  intros n UB Hfail.
  pose proof (complement_rule (E_event n)) as Hcomp.
  lra.
Qed.

Theorem proposition1_feasibility_probability_explicit :
  forall n,
    Pr (fun w => ~ E_event n w) <= hall_union_bound n (3 / 4) ->
    1 - hall_union_bound n (3 / 4) <= Pr (E_event n).
Proof.
  intros n Hhall.
  eapply proposition1_from_failure_upper_bound.
  exact Hhall.
Qed.

Theorem proposition1_failure_bound_from_hall_obstruction :
  forall n,
    (forall w, ~ E_event n w -> hall_obstruction_event n w) ->
    Pr (hall_obstruction_event n) <= hall_union_bound n (3 / 4) ->
    Pr (fun w => ~ E_event n w) <= hall_union_bound n (3 / 4).
Proof.
  intros n Hreduce Hhall.
  eapply Rle_trans.
  - apply (Pr_monotone (fun w => ~ E_event n w) (hall_obstruction_event n)).
    exact Hreduce.
  - exact Hhall.
Qed.

Theorem proposition1_via_hall_obstruction :
  forall n,
    (forall w, ~ E_event n w -> hall_obstruction_event n w) ->
    Pr (hall_obstruction_event n) <= hall_union_bound n (3 / 4) ->
    1 - hall_union_bound n (3 / 4) <= Pr (E_event n).
Proof.
  intros n Hreduce Hhall.
  apply proposition1_feasibility_probability_explicit.
  eapply proposition1_failure_bound_from_hall_obstruction.
  - exact Hreduce.
  - exact Hhall.
Qed.

End Proposition1.
