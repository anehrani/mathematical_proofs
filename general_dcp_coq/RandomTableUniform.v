From Stdlib Require Import List Arith Reals.
Require Import Lemma1 Proposition1 FiniteProbability RandomTableModel.
Import ListNotations.

Open Scope R_scope.

Section RandomTableUniform.

Definition failure_event (n : nat) (w : RandomTableModel.table) : Prop :=
  ~ Proposition1.E_event RandomTableModel.table RandomTableModel.phi_of_table n w.

Definition failure_ratio (n : nat) (universe : list RandomTableModel.table) : R :=
  INR (FiniteProbability.count_event RandomTableModel.table (failure_event n) universe)
  / INR (length universe).

Lemma failure_ratio_eq_probability :
  forall n universe,
    failure_ratio n universe =
    FiniteProbability.Pr RandomTableModel.table universe (failure_event n).
Proof.
  intros n universe.
  unfold failure_ratio, FiniteProbability.Pr.
  reflexivity.
Qed.

Theorem proposition1_table_from_failure_ratio :
  forall (universe : list RandomTableModel.table) (binom : nat -> nat -> nat),
    universe <> [] ->
    forall n,
      failure_ratio n universe <= Proposition1.hall_union_bound binom n (3 / 4) ->
      1 - Proposition1.hall_union_bound binom n (3 / 4)
      <= FiniteProbability.Pr RandomTableModel.table universe
           (Proposition1.E_event RandomTableModel.table RandomTableModel.phi_of_table n).
Proof.
  intros universe binom Huniv n Hratio.
  apply RandomTableModel.proposition1_table_from_failure_bound with (binom := binom).
  - exact Huniv.
  - change (FiniteProbability.Pr RandomTableModel.table universe (failure_event n)
      <= Proposition1.hall_union_bound binom n (3 / 4)).
    rewrite <- failure_ratio_eq_probability.
    exact Hratio.
Qed.

Theorem proposition1_table_from_failure_count_ratio :
  forall (universe : list RandomTableModel.table) (binom : nat -> nat -> nat),
    universe <> [] ->
    forall n,
      (INR (FiniteProbability.count_event
              RandomTableModel.table
              (failure_event n)
              universe)
       / INR (length universe))
      <= Proposition1.hall_union_bound binom n (3 / 4) ->
      1 - Proposition1.hall_union_bound binom n (3 / 4)
      <= FiniteProbability.Pr RandomTableModel.table universe
           (Proposition1.E_event RandomTableModel.table RandomTableModel.phi_of_table n).
Proof.
  intros universe binom Huniv n Hcount.
  apply proposition1_table_from_failure_ratio with (binom := binom).
  - exact Huniv.
  - unfold failure_ratio.
    exact Hcount.
Qed.

End RandomTableUniform.
