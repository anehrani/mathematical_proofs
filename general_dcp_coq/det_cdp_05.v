From Stdlib Require Import List Arith Lia Permutation.

Require Export deterministic_cdp.

Import ListNotations.

Module DetCDP05.

Section PaperCore.

Context {A B : Type}.

Theorem only_ties_remove_cards :
  forall (phi : A -> B -> Lemma1.outcome) (start : @Lemma1.config A B) os n,
    length (Lemma1.deck_A start) = n ->
    length (Lemma1.deck_B start) = n ->
    @Lemma1.game A B phi start os ->
    Lemma1.tie_count os = n.
Proof.
  exact lemma1_exactly_n_ties.
Qed.

Theorem tie_matching :
  forall (phi : A -> B -> Lemma1.outcome) (start : @Lemma1.config A B) tr,
    NoDup (Lemma1.deck_A start) ->
    NoDup (Lemma1.deck_B start) ->
    @Lemma2.game_trace A B phi start tr ->
    @Lemma2.perfect_matching_on A B phi (Lemma1.deck_A start) (Lemma1.deck_B start)
      (@Lemma2.tie_pairs A B tr).
Proof.
  exact lemma2_tie_matching.
Qed.

Theorem cyclic_invariance :
  forall (phi : A -> B -> Lemma1.outcome) (start : @Lemma1.config A B) tr c,
    @Lemma2.play A B phi start tr c ->
    Forall (@Lemma3.non_tie_duel A B) tr ->
    exists i j,
      Lemma1.deck_A c = Nat.iter i (@Lemma3.move_top_to_bottom A) (Lemma1.deck_A start)
      /\
      Lemma1.deck_B c = Nat.iter j (@Lemma3.move_top_to_bottom B) (Lemma1.deck_B start).
Proof.
  exact lemma3_cyclic_invariance.
Qed.

Theorem phase_transition_rule :
  forall (phi : A -> B -> Lemma1.outcome) initial_A initial_B i j c1 o c2,
    @Lemma4.phase_state A B initial_A initial_B i j c1 ->
    @Lemma1.step A B phi c1 o c2 ->
    match o with
    | Lemma1.WA => @Lemma4.phase_state A B initial_A initial_B i (S j) c2
    | Lemma1.WB => @Lemma4.phase_state A B initial_A initial_B (S i) j c2
    | Lemma1.NN => @Lemma4.phase_state A B initial_A initial_B (S i) (S j) c2
    | Lemma1.TT => True
    end.
Proof.
  exact lemma4_phase_transition_rule.
Qed.

Theorem no_repeated_states_within_phase :
  forall (phi : A -> B -> Lemma1.outcome) (start : @Lemma1.config A B) tr,
    @Lemma2.game_trace A B phi start tr ->
    ~ exists prefix cycle suffix mid,
        tr = prefix ++ cycle ++ suffix /\
        cycle <> [] /\
        @Lemma2.play A B phi start prefix mid /\
        @Lemma2.play A B phi mid cycle mid /\
        @Lemma2.game_trace A B phi mid suffix.
Proof.
  exact lemma5_no_repeated_states.
Qed.

End PaperCore.

Section PhasewiseCounting.

Theorem phasewise_bound :
  forall m visited forbidden,
    NoDup visited ->
    NoDup forbidden ->
    (forall s, In s visited -> ~ In s forbidden) ->
    Forall (TheoremPhasewise.bounded_state m) visited ->
    Forall (TheoremPhasewise.bounded_state m) forbidden ->
    length forbidden = m - 1 ->
    length visited <= m * m - m + 1.
Proof.
  exact theorem_phasewise_bound.
Qed.

Theorem upper_bound :
  forall n,
    CorollaryUpper.sum_upto CorollaryUpper.phase_term n = n * (n * n + 2) / 3.
Proof.
  exact corollary_upper_sum_identity.
Qed.

End PhasewiseCounting.

Section StaircaseLocal.

Theorem table_restriction :
  forall n m u v,
    m <= n ->
    m >= 2 ->
    u < m ->
    v < m ->
    LowerBoundConstructive.constructive_phi_global n u (v + (n - m)) =
    LowerBoundConstructive.phi_local m u v.
Proof.
  exact constructive_phi_global_restricts_to_local.
Qed.

Theorem intermediate_row_dynamics :
  forall m u,
    m > 2 ->
    1 <= u <= m - 2 ->
    (forall v,
      m - u <= v <= m - 1 ->
      local_step m (u, v) = Some (u, (v + 1) mod m)) /\
    (1 <= u <= m - 3 ->
      forall v,
        0 <= v <= m - 3 - u ->
        LowerBoundConstructive.local_step m (u, v) = Some (u, v + 1)) /\
    LowerBoundConstructive.local_step m (u, m - 2 - u) = Some (u + 1, m - 1 - u).
Proof.
  exact local_step_intermediate_row_dynamics_summary.
Qed.

Theorem final_row_dynamics :
  forall m,
    m > 2 ->
    (forall v,
      1 <= v <= m - 1 ->
      LowerBoundConstructive.local_step m (m - 1, v) = Some (m - 1, (v + 1) mod m)) /\
    LowerBoundConstructive.local_step m (m - 1, 0) = None.
Proof.
  exact local_step_last_row_dynamics_summary.
Qed.

Theorem exact_cardinality_of_row_sets :
  forall m u,
    m > 2 ->
    (0 <= u <= m - 2 -> length (LowerBoundConstructive.visited_cols_row m u) = m - 1) /\
    (u = m - 1 -> length (LowerBoundConstructive.visited_cols_row m u) = m).
Proof.
  exact visited_cols_row_cardinality.
Qed.

Theorem small_phase_checks :
  (LowerBoundConstructive.local_step 1 (0, 0) = None /\ 1 = 1 * 1 - 1 + 1) /\
  ((exists s1 s2,
      LowerBoundConstructive.local_step 2 (0, 0) = Some s1 /\
      LowerBoundConstructive.local_step 2 s1 = Some s2 /\
      LowerBoundConstructive.local_step 2 s2 = None /\
      s2 = (1, 0)) /\
   3 = 2 * 2 - 2 + 1).
Proof.
  split.
  - exact local_phase_base_case_m1.
  - exact local_phase_base_case_m2.
Qed.

Theorem local_staircase_budget :
  forall m,
    (m = 1 -> LowerBound.phase_term m = 1) /\
    (m = 2 -> LowerBound.phase_term m = 3) /\
    (m > 2 -> LowerBound.phase_term m = (m - 1) * (m - 1) + m).
Proof.
  exact local_phase_budget_complete_all_m.
Qed.

Theorem staircase_closed_form :
  forall n,
    LowerBound.T n = n * (n * n + 2) / 3.
Proof.
  exact constructive_budget_matches_global_closed_form.
Qed.

End StaircaseLocal.

(*
  The current workspace does not contain unconditional end-to-end Coq proofs for
  the manuscript's remaining global staircase statements, including:

  - monotonic_row_development
  - local_injectivity
  - local_staircase_traversal
  - accumulated_row_offset
  - phase_reset
  - tightness
  - main_theorem

  The repository's existing Coq development verifies the semantic core, the
  abstract phasewise counting argument, and the local staircase budget lemmas;
  the final global staircase induction remains a separate formalization task.
*)

End DetCDP05.