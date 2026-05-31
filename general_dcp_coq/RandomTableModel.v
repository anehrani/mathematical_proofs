From Stdlib Require Import List Arith Reals Bool.
Require Import Lemma1 Proposition1 Proposition1Finite FiniteProbability.
Import ListNotations.

Open Scope R_scope.

Section RandomTableModel.

Definition cell := (nat * nat)%type.
Definition table := list (cell * Lemma1.outcome).

Fixpoint lookup_table (w : table) (i j : nat) : option Lemma1.outcome :=
  match w with
  | [] => None
  | ((i', j'), o) :: ws =>
      if Nat.eqb i i' && Nat.eqb j j' then Some o else lookup_table ws i j
  end.

Definition phi_of_table (w : table) (i j : nat) : Lemma1.outcome :=
  match lookup_table w i j with
  | Some o => o
  | None => Lemma1.WA
  end.

Theorem proposition1_table_from_failure_bound :
  forall (universe : list table) (binom : nat -> nat -> nat),
    universe <> [] ->
    forall n,
      FiniteProbability.Pr table universe
        (fun w => ~ Proposition1.E_event table phi_of_table n w)
      <= Proposition1.hall_union_bound binom n (3 / 4) ->
      1 - Proposition1.hall_union_bound binom n (3 / 4)
      <= FiniteProbability.Pr table universe
           (Proposition1.E_event table phi_of_table n).
Proof.
  intros universe binom Huniv n Hfail.
  eapply Proposition1Finite.proposition1_from_failure_bound_finite
    with
      (Omega := table)
      (universe := universe)
      (phi_of := phi_of_table)
      (binom := binom).
  - exact Huniv.
  - exact Hfail.
Qed.

End RandomTableModel.
