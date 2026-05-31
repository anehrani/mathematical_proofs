From Stdlib Require Import List Arith Lia Reals Lra ClassicalDescription.
Require Import Lemma1 Proposition1 FiniteProbability RandomTableModel RandomTableUniform.
Import ListNotations.

Open Scope R_scope.

Section RandomTableEnumeration.

Definition all_outcomes : list Lemma1.outcome :=
  [Lemma1.WA; Lemma1.WB; Lemma1.TT; Lemma1.NN].

Definition cells_n (n : nat) : list RandomTableModel.cell :=
  list_prod (seq 0 n) (seq 0 n).

Fixpoint all_tables_on_cells (cs : list RandomTableModel.cell)
  : list RandomTableModel.table :=
  match cs with
  | [] => [[]]
  | c :: cs' =>
      flat_map
        (fun rest => map (fun o => (c, o) :: rest) all_outcomes)
        (all_tables_on_cells cs')
  end.

Definition tables_n (n : nat) : list RandomTableModel.table :=
  all_tables_on_cells (cells_n n).

Lemma all_outcomes_length :
  length all_outcomes = 4%nat.
Proof.
  reflexivity.
Qed.

Lemma length_flat_map_table_extensions :
  forall (c : RandomTableModel.cell) (rs : list RandomTableModel.table),
    length
      (flat_map
         (fun rest => map (fun o => (c, o) :: rest) all_outcomes)
         rs)
    = (length all_outcomes * length rs)%nat.
Proof.
  intros c rs.
  induction rs as [|r rs IH].
  - reflexivity.
  - cbn [flat_map].
    rewrite length_app.
    rewrite length_map.
    rewrite IH.
    set (a := length all_outcomes).
    set (b := length rs).
    change (a + a * b = a * S b)%nat.
    rewrite Nat.mul_succ_r.
    lia.
Qed.

Lemma all_tables_on_cells_length :
  forall cs,
    length (all_tables_on_cells cs)
    = Nat.pow (length all_outcomes) (length cs).
Proof.
  induction cs as [|c cs IH].
  - reflexivity.
  - cbn [all_tables_on_cells].
    rewrite length_flat_map_table_extensions.
    rewrite IH.
    simpl.
    lia.
Qed.

Lemma list_prod_length :
  forall (A B : Type) (xs : list A) (ys : list B),
    length (list_prod xs ys) = (length xs * length ys)%nat.
Proof.
  intros A B xs ys.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl.
    rewrite length_app.
    rewrite length_map.
    rewrite IH.
    lia.
Qed.

Lemma cells_n_length :
  forall n,
    length (cells_n n) = (n * n)%nat.
Proof.
  intro n.
  unfold cells_n.
  change (length (list_prod (seq 0 n) (seq 0 n)) = (n * n)%nat).
  rewrite list_prod_length.
  rewrite !length_seq.
  lia.
Qed.

Lemma tables_n_length :
  forall n,
    length (tables_n n) = Nat.pow 4%nat (n * n)%nat.
Proof.
  intro n.
  unfold tables_n.
  rewrite all_tables_on_cells_length.
  rewrite cells_n_length.
  rewrite all_outcomes_length.
  reflexivity.
Qed.

Lemma all_tables_on_cells_inhabited :
  forall cs,
    exists t, In t (all_tables_on_cells cs).
Proof.
  induction cs as [|c cs IH].
  - exists [].
    simpl.
    left.
    reflexivity.
  - destruct IH as [rest Hrest].
    exists ((c, Lemma1.WA) :: rest).
    simpl.
    apply in_flat_map.
    exists rest.
    split.
    + exact Hrest.
    + simpl.
      left.
      reflexivity.
Qed.

Lemma tables_n_nonempty :
  forall n,
    tables_n n <> [].
Proof.
  intros n Hnil.
  unfold tables_n in Hnil.
  pose proof (all_tables_on_cells_inhabited (cells_n n)) as [t Hin].
  rewrite Hnil in Hin.
  inversion Hin.
Qed.

Definition failure_count_n (n : nat) : nat :=
  FiniteProbability.count_event
    RandomTableModel.table
    (RandomTableUniform.failure_event n)
    (tables_n n).

Lemma indicator_le_one :
  forall P,
    (FiniteProbability.indicator P <= 1)%nat.
Proof.
  intro P.
  unfold FiniteProbability.indicator.
  destruct (excluded_middle_informative P); lia.
Qed.

Lemma count_event_le_length :
  forall (A : RandomTableModel.table -> Prop) xs,
    (FiniteProbability.count_event RandomTableModel.table A xs <= length xs)%nat.
Proof.
  intros A xs.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl.
    pose proof (indicator_le_one (A x)) as Hind.
    lia.
Qed.

Theorem failure_count_n_le_tables_n_length :
  forall n,
    (failure_count_n n <= Nat.pow 4%nat (n * n)%nat)%nat.
Proof.
  intro n.
  unfold failure_count_n.
  rewrite <- tables_n_length.
  apply count_event_le_length.
Qed.

Lemma tables_n_length_pos :
  forall n,
    (0 < length (tables_n n))%nat.
Proof.
  intros n.
  destruct (tables_n n) as [|t ts] eqn:Huniv.
  - exfalso.
    apply (tables_n_nonempty n).
    exact Huniv.
  - simpl.
    lia.
Qed.

Lemma failure_ratio_tables_n_pow4 :
  forall n,
    RandomTableUniform.failure_ratio n (tables_n n)
    = INR (failure_count_n n) / INR (Nat.pow 4%nat (n * n)%nat).
Proof.
  intro n.
  unfold RandomTableUniform.failure_ratio, failure_count_n.
  rewrite tables_n_length.
  reflexivity.
Qed.

Lemma failure_ratio_tables_n_le_1 :
  forall n,
    RandomTableUniform.failure_ratio n (tables_n n) <= 1.
Proof.
  intro n.
  rewrite failure_ratio_tables_n_pow4.
  set (d := INR (Nat.pow 4%nat (n * n)%nat)).
  assert (Hdpos : 0 < d).
  {
    unfold d.
    rewrite <- tables_n_length.
    apply lt_0_INR.
    apply tables_n_length_pos.
  }
  assert (Hdneq : d <> 0) by lra.
  apply Rmult_le_reg_r with (r := d).
  - exact Hdpos.
  - unfold Rdiv.
    rewrite Rmult_1_l.
    field_simplify.
    + apply le_INR.
      apply failure_count_n_le_tables_n_length.
    + exact Hdneq.
Qed.

Theorem proposition1_tables_n_from_failure_ratio_bound :
  forall n (binom : nat -> nat -> nat),
    RandomTableUniform.failure_ratio n (tables_n n)
      <= Proposition1.hall_union_bound binom n (3 / 4) ->
    1 - Proposition1.hall_union_bound binom n (3 / 4)
      <= FiniteProbability.Pr
           RandomTableModel.table
           (tables_n n)
           (Proposition1.E_event
              RandomTableModel.table
              RandomTableModel.phi_of_table
              n).
Proof.
  intros n binom Hratio.
  apply (RandomTableUniform.proposition1_table_from_failure_ratio
           (tables_n n)
           binom).
  - apply tables_n_nonempty.
  - exact Hratio.
Qed.

Theorem proposition1_tables_n_from_failure_count_ratio_bound :
  forall n (binom : nat -> nat -> nat),
    (INR (failure_count_n n) / INR (length (tables_n n)))
      <= Proposition1.hall_union_bound binom n (3 / 4) ->
    1 - Proposition1.hall_union_bound binom n (3 / 4)
      <= FiniteProbability.Pr
           RandomTableModel.table
           (tables_n n)
           (Proposition1.E_event
              RandomTableModel.table
              RandomTableModel.phi_of_table
              n).
Proof.
  intros n binom Hcount.
  apply (RandomTableUniform.proposition1_table_from_failure_count_ratio
           (tables_n n)
           binom).
  - apply tables_n_nonempty.
  - unfold failure_count_n.
    exact Hcount.
Qed.

Theorem proposition1_tables_n_from_failure_count_ratio_bound_pow4 :
  forall n (binom : nat -> nat -> nat),
    (INR (failure_count_n n) / INR (Nat.pow 4%nat (n * n)%nat))
      <= Proposition1.hall_union_bound binom n (3 / 4) ->
    1 - Proposition1.hall_union_bound binom n (3 / 4)
      <= FiniteProbability.Pr
           RandomTableModel.table
           (tables_n n)
           (Proposition1.E_event
              RandomTableModel.table
              RandomTableModel.phi_of_table
              n).
Proof.
  intros n binom Hcount.
  apply proposition1_tables_n_from_failure_count_ratio_bound.
  rewrite tables_n_length.
  exact Hcount.
Qed.

Theorem proposition1_tables_n_from_hall_bound_ge_1 :
  forall n (binom : nat -> nat -> nat),
    1 <= Proposition1.hall_union_bound binom n (3 / 4) ->
    1 - Proposition1.hall_union_bound binom n (3 / 4)
      <= FiniteProbability.Pr
           RandomTableModel.table
           (tables_n n)
           (Proposition1.E_event
              RandomTableModel.table
              RandomTableModel.phi_of_table
              n).
Proof.
  intros n binom Hub1.
  apply proposition1_tables_n_from_failure_ratio_bound.
  eapply Rle_trans.
  - apply failure_ratio_tables_n_le_1.
  - exact Hub1.
Qed.

Theorem proposition1_tables_n_from_failure_count_upper_bound :
  forall n (binom : nat -> nat -> nat) (k : nat),
    (failure_count_n n <= k)%nat ->
    (INR k / INR (Nat.pow 4%nat (n * n)%nat))
      <= Proposition1.hall_union_bound binom n (3 / 4) ->
    1 - Proposition1.hall_union_bound binom n (3 / 4)
      <= FiniteProbability.Pr
           RandomTableModel.table
           (tables_n n)
           (Proposition1.E_event
              RandomTableModel.table
              RandomTableModel.phi_of_table
              n).
Proof.
  intros n binom k Hk Hub.
  apply proposition1_tables_n_from_failure_count_ratio_bound_pow4.
  eapply Rle_trans.
  - rewrite <- failure_ratio_tables_n_pow4.
    rewrite failure_ratio_tables_n_pow4.
    set (d := INR (Nat.pow 4%nat (n * n)%nat)).
    assert (Hdpos : 0 < d).
    {
      unfold d.
      rewrite <- tables_n_length.
      apply lt_0_INR.
      apply tables_n_length_pos.
    }
    assert (HleR : INR (failure_count_n n) <= INR k).
    {
      apply le_INR.
      exact Hk.
    }
    unfold Rdiv.
    apply Rmult_le_compat_r.
    + left.
      apply Rinv_0_lt_compat.
      exact Hdpos.
    + exact HleR.
  - exact Hub.
Qed.

Definition failure_count_bound (B : nat -> nat) : Prop :=
  forall n,
    (failure_count_n n <= B n)%nat.

Theorem proposition1_tables_n_from_symbolic_failure_count_bound :
  forall (B : nat -> nat) n (binom : nat -> nat -> nat),
    failure_count_bound B ->
    (INR (B n) / INR (Nat.pow 4%nat (n * n)%nat))
      <= Proposition1.hall_union_bound binom n (3 / 4) ->
    1 - Proposition1.hall_union_bound binom n (3 / 4)
      <= FiniteProbability.Pr
           RandomTableModel.table
           (tables_n n)
           (Proposition1.E_event
              RandomTableModel.table
              RandomTableModel.phi_of_table
              n).
Proof.
  intros B n binom HB Hub.
  apply proposition1_tables_n_from_failure_count_upper_bound with (k := B n).
  - apply HB.
  - exact Hub.
Qed.

Theorem proposition1_tables_n_family_from_symbolic_failure_count_bound :
  forall (B : nat -> nat) (binom : nat -> nat -> nat),
    failure_count_bound B ->
    (forall n,
      (INR (B n) / INR (Nat.pow 4%nat (n * n)%nat))
        <= Proposition1.hall_union_bound binom n (3 / 4)) ->
    forall n,
      1 - Proposition1.hall_union_bound binom n (3 / 4)
        <= FiniteProbability.Pr
             RandomTableModel.table
             (tables_n n)
             (Proposition1.E_event
                RandomTableModel.table
                RandomTableModel.phi_of_table
                n).
Proof.
  intros B binom HB Hratio n.
  apply proposition1_tables_n_from_symbolic_failure_count_bound with (B := B).
  - exact HB.
  - apply Hratio.
Qed.

Definition failure_count_scaled_bound (C : nat -> R) : Prop :=
  forall n,
    INR (failure_count_n n)
      <= C n * INR (Nat.pow 4%nat (n * n)%nat).

Definition normalized_failure_bound (B : nat -> nat) (n : nat) : R :=
  INR (B n) / INR (Nat.pow 4%nat (n * n)%nat).

Lemma failure_count_scaled_bound_from_symbolic :
  forall (B : nat -> nat),
    failure_count_bound B ->
    failure_count_scaled_bound (normalized_failure_bound B).
Proof.
  intros B HB n.
  unfold normalized_failure_bound.
  set (d := INR (Nat.pow 4%nat (n * n)%nat)).
  assert (Hdpos : 0 < d).
  {
    unfold d.
    rewrite <- tables_n_length.
    apply lt_0_INR.
    apply tables_n_length_pos.
  }
  assert (Hdneq : d <> 0) by lra.
  assert (HleR : INR (failure_count_n n) <= INR (B n)).
  {
    apply le_INR.
    apply HB.
  }
  replace ((INR (B n) / d) * d) with (INR (B n)).
  - exact HleR.
  - field.
    exact Hdneq.
Qed.

Lemma failure_count_scaled_bound_one :
  failure_count_scaled_bound (fun _ => 1).
Proof.
  intro n.
  assert (Hle : (failure_count_n n <= Nat.pow 4%nat (n * n)%nat)%nat).
  {
    apply failure_count_n_le_tables_n_length.
  }
  rewrite Rmult_1_l.
  apply le_INR.
  exact Hle.
Qed.

Lemma failure_count_ratio_le_from_scaled_bound :
  forall n c,
    INR (failure_count_n n)
      <= c * INR (Nat.pow 4%nat (n * n)%nat) ->
    INR (failure_count_n n) / INR (Nat.pow 4%nat (n * n)%nat)
      <= c.
Proof.
  intros n c Hscaled.
  set (d := INR (Nat.pow 4%nat (n * n)%nat)).
  assert (Hdpos : 0 < d).
  {
    unfold d.
    rewrite <- tables_n_length.
    apply lt_0_INR.
    apply tables_n_length_pos.
  }
  assert (Hdneq : d <> 0) by lra.
  apply Rmult_le_reg_r with (r := d).
  - exact Hdpos.
  - unfold Rdiv.
    field_simplify.
    + unfold d.
      rewrite Rmult_comm.
      exact Hscaled.
    + exact Hdneq.
Qed.

Lemma nat_ratio_pow4_le_from_scaled_bound :
  forall n (k : nat) c,
    INR k <= c * INR (Nat.pow 4%nat (n * n)%nat) ->
    INR k / INR (Nat.pow 4%nat (n * n)%nat) <= c.
Proof.
  intros n k c Hscaled.
  set (d := INR (Nat.pow 4%nat (n * n)%nat)).
  assert (Hdpos : 0 < d).
  {
    unfold d.
    rewrite <- tables_n_length.
    apply lt_0_INR.
    apply tables_n_length_pos.
  }
  assert (Hdneq : d <> 0) by lra.
  apply Rmult_le_reg_r with (r := d).
  - exact Hdpos.
  - unfold Rdiv.
    field_simplify.
    + unfold d.
      rewrite Rmult_comm.
      exact Hscaled.
    + exact Hdneq.
Qed.

Theorem proposition1_tables_n_from_scaled_failure_count_bound :
  forall n (binom : nat -> nat -> nat) c,
    INR (failure_count_n n)
      <= c * INR (Nat.pow 4%nat (n * n)%nat) ->
    c <= Proposition1.hall_union_bound binom n (3 / 4) ->
    1 - Proposition1.hall_union_bound binom n (3 / 4)
      <= FiniteProbability.Pr
           RandomTableModel.table
           (tables_n n)
           (Proposition1.E_event
              RandomTableModel.table
              RandomTableModel.phi_of_table
              n).
Proof.
  intros n binom c Hscaled Hc.
  apply proposition1_tables_n_from_failure_count_ratio_bound_pow4.
  eapply Rle_trans.
  - apply failure_count_ratio_le_from_scaled_bound.
    exact Hscaled.
  - exact Hc.
Qed.

Theorem proposition1_tables_n_family_from_scaled_failure_count_bound :
  forall (C : nat -> R) (binom : nat -> nat -> nat),
    failure_count_scaled_bound C ->
    (forall n, C n <= Proposition1.hall_union_bound binom n (3 / 4)) ->
    forall n,
      1 - Proposition1.hall_union_bound binom n (3 / 4)
        <= FiniteProbability.Pr
             RandomTableModel.table
             (tables_n n)
             (Proposition1.E_event
                RandomTableModel.table
                RandomTableModel.phi_of_table
                n).
Proof.
  intros C binom HC Hhub n.
  apply proposition1_tables_n_from_scaled_failure_count_bound with (c := C n).
  - apply HC.
  - apply Hhub.
Qed.

Theorem proposition1_tables_n_family_from_symbolic_bound_via_scaled :
  forall (B : nat -> nat) (binom : nat -> nat -> nat),
    failure_count_bound B ->
    (forall n,
      normalized_failure_bound B n
        <= Proposition1.hall_union_bound binom n (3 / 4)) ->
    forall n,
      1 - Proposition1.hall_union_bound binom n (3 / 4)
        <= FiniteProbability.Pr
             RandomTableModel.table
             (tables_n n)
             (Proposition1.E_event
                RandomTableModel.table
                RandomTableModel.phi_of_table
                n).
Proof.
  intros B binom HB Hhub n.
  apply proposition1_tables_n_family_from_scaled_failure_count_bound
    with (C := normalized_failure_bound B).
  - apply failure_count_scaled_bound_from_symbolic.
    exact HB.
  - exact Hhub.
Qed.

Theorem proposition1_tables_n_family_from_symbolic_scaled_premise :
  forall (B : nat -> nat) (binom : nat -> nat -> nat),
    failure_count_bound B ->
    (forall n,
      INR (B n)
        <= Proposition1.hall_union_bound binom n (3 / 4)
             * INR (Nat.pow 4%nat (n * n)%nat)) ->
    forall n,
      1 - Proposition1.hall_union_bound binom n (3 / 4)
        <= FiniteProbability.Pr
             RandomTableModel.table
             (tables_n n)
             (Proposition1.E_event
                RandomTableModel.table
                RandomTableModel.phi_of_table
                n).
Proof.
  intros B binom HB Hscaled n.
  apply proposition1_tables_n_family_from_symbolic_bound_via_scaled with (B := B).
  - exact HB.
  - intro k.
    unfold normalized_failure_bound.
    apply nat_ratio_pow4_le_from_scaled_bound.
    apply Hscaled.
Qed.

Lemma failure_count_bound_pow4 :
  failure_count_bound (fun n => Nat.pow 4%nat (n * n)%nat).
Proof.
  intro n.
  apply failure_count_n_le_tables_n_length.
Qed.

Theorem proposition1_tables_n_family_from_pow4_scaled_premise :
  forall (binom : nat -> nat -> nat),
    (forall n,
      INR (Nat.pow 4%nat (n * n)%nat)
        <= Proposition1.hall_union_bound binom n (3 / 4)
             * INR (Nat.pow 4%nat (n * n)%nat)) ->
    forall n,
      1 - Proposition1.hall_union_bound binom n (3 / 4)
        <= FiniteProbability.Pr
             RandomTableModel.table
             (tables_n n)
             (Proposition1.E_event
                RandomTableModel.table
                RandomTableModel.phi_of_table
                n).
Proof.
  intros binom Hscaled n.
  apply proposition1_tables_n_family_from_symbolic_scaled_premise
    with (B := fun k => Nat.pow 4%nat (k * k)%nat).
  - apply failure_count_bound_pow4.
  - exact Hscaled.
Qed.

Lemma pow4_scaled_premise_from_hall_bound_ge_1 :
  forall (binom : nat -> nat -> nat),
    (forall n, 1 <= Proposition1.hall_union_bound binom n (3 / 4)) ->
    forall n,
      INR (Nat.pow 4%nat (n * n)%nat)
        <= Proposition1.hall_union_bound binom n (3 / 4)
             * INR (Nat.pow 4%nat (n * n)%nat).
Proof.
  intros binom Hhub n.
  set (d := INR (Nat.pow 4%nat (n * n)%nat)).
  assert (Hdpos : 0 < d).
  {
    unfold d.
    rewrite <- tables_n_length.
    apply lt_0_INR.
    apply tables_n_length_pos.
  }
  pose proof (Hhub n) as Hh.
  assert (Hscaled : 1 * d <= Proposition1.hall_union_bound binom n (3 / 4) * d).
  {
    apply Rmult_le_compat_r.
    + left; exact Hdpos.
    + exact Hh.
  }
  unfold d in Hscaled.
  rewrite Rmult_1_l in Hscaled.
  exact Hscaled.
Qed.

Theorem proposition1_tables_n_family_from_pow4_hall_bound_ge_1 :
  forall (binom : nat -> nat -> nat),
    (forall n, 1 <= Proposition1.hall_union_bound binom n (3 / 4)) ->
    forall n,
      1 - Proposition1.hall_union_bound binom n (3 / 4)
        <= FiniteProbability.Pr
             RandomTableModel.table
             (tables_n n)
             (Proposition1.E_event
                RandomTableModel.table
                RandomTableModel.phi_of_table
                n).
Proof.
  intros binom Hhub n.
  apply proposition1_tables_n_family_from_pow4_scaled_premise.
  apply pow4_scaled_premise_from_hall_bound_ge_1.
  exact Hhub.
Qed.

Theorem proposition1_tables_n_family_from_scaled_bound_one :
  forall (binom : nat -> nat -> nat),
    (forall n, 1 <= Proposition1.hall_union_bound binom n (3 / 4)) ->
    forall n,
      1 - Proposition1.hall_union_bound binom n (3 / 4)
        <= FiniteProbability.Pr
             RandomTableModel.table
             (tables_n n)
             (Proposition1.E_event
                RandomTableModel.table
                RandomTableModel.phi_of_table
                n).
Proof.
  intros binom Hhub n.
  apply proposition1_tables_n_family_from_scaled_failure_count_bound
    with (C := fun _ => 1).
  - apply failure_count_scaled_bound_one.
  - intros k.
    apply Hhub.
Qed.

End RandomTableEnumeration.
