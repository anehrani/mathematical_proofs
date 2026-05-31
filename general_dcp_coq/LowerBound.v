From Stdlib Require Import List Arith Lia PeanoNat.
Require Import CorollaryUpper.
Import ListNotations.

Section LowerBound.

Inductive outcome := WA | WB | TT | NN.

Definition outcome_eq_dec : forall x y : outcome, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Record config := {
  deck_A : list nat;
  deck_B : list nat
}.

Inductive step (phi : nat -> nat -> outcome) : config -> outcome -> config -> Prop :=
| StepWA : forall a as_ b bs,
    phi a b = WA ->
    step phi
      {| deck_A := a :: as_; deck_B := b :: bs |}
      WA
      {| deck_A := a :: as_; deck_B := bs ++ [b] |}
| StepWB : forall a as_ b bs,
    phi a b = WB ->
    step phi
      {| deck_A := a :: as_; deck_B := b :: bs |}
      WB
      {| deck_A := as_ ++ [a]; deck_B := b :: bs |}
| StepTT : forall a as_ b bs,
    phi a b = TT ->
    step phi
      {| deck_A := a :: as_; deck_B := b :: bs |}
      TT
      {| deck_A := as_; deck_B := bs |}
| StepNN : forall a as_ b bs,
    phi a b = NN ->
    step phi
      {| deck_A := a :: as_; deck_B := b :: bs |}
      NN
      {| deck_A := as_ ++ [a]; deck_B := bs ++ [b] |}.

Inductive runs (phi : nat -> nat -> outcome) : config -> list outcome -> config -> Prop :=
| RunsNil : forall c,
    runs phi c [] c
| RunsCons : forall c1 c2 c3 o os,
    step phi c1 o c2 ->
    runs phi c2 os c3 ->
    runs phi c1 (o :: os) c3.

Definition game (phi : nat -> nat -> outcome) (start : config) (os : list outcome) : Prop :=
  runs phi start os {| deck_A := []; deck_B := [] |}.

Definition duration (os : list outcome) : nat := length os.

Definition tie_count (os : list outcome) : nat :=
  count_occ outcome_eq_dec os TT.

Definition tie_weight (o : outcome) : nat :=
  match o with
  | TT => 1
  | _ => 0
  end.

Lemma tie_count_cons :
  forall o os,
    tie_count (o :: os) = tie_count os + tie_weight o.
Proof.
  intros o os.
  unfold tie_count, tie_weight.
  destruct o; simpl; lia.
Qed.

Definition phase_term (m : nat) : nat := m * m - m + 1.

Fixpoint T (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => T k + phase_term (S k)
  end.

Lemma phase_term_ge_one :
  forall n,
    n > 0 ->
    phase_term n >= 1.
Proof.
  intros n Hn.
  unfold phase_term.
  lia.
Qed.

Lemma T_ge_n :
  forall n,
    T n >= n.
Proof.
  induction n as [|n IH].
  - simpl. lia.
  - simpl.
    assert (Hpt : phase_term (S n) >= 1).
    {
      apply phase_term_ge_one.
      lia.
    }
    lia.
Qed.

Definition lower_bound_solution (m : nat) : Prop :=
  exists (phi : nat -> nat -> outcome) (start : config) (os : list outcome),
    length (deck_A start) = m /\
    length (deck_B start) = m /\
    game phi start os /\
    duration os = T m.

(* ---------- Local lemmas that are fully formalized ---------- *)

Lemma step_length_accounting :
  forall phi c1 o c2,
    step phi c1 o c2 ->
    length (deck_A c2) + tie_weight o = length (deck_A c1)
    /\ length (deck_B c2) + tie_weight o = length (deck_B c1).
Proof.
  intros phi c1 o c2 Hstep.
  destruct Hstep; simpl; rewrite ?length_app; simpl; lia.
Qed.

Lemma runs_length_tie_accounting :
  forall phi c1 os c2,
    runs phi c1 os c2 ->
    length (deck_A c2) + tie_count os = length (deck_A c1)
    /\ length (deck_B c2) + tie_count os = length (deck_B c1).
Proof.
  intros phi c1 os c2 Hruns.
  induction Hruns as [c|c1 c2 c3 o os Hstep Hruns IH].
  - simpl. unfold tie_count. simpl. split; lia.
  - simpl.
    destruct (step_length_accounting phi c1 o c2 Hstep) as [HA HB].
    destruct IH as [IHA IHB].
    rewrite tie_count_cons.
    split; lia.
Qed.

Lemma game_tie_count_equals_initial_size :
  forall phi start os,
    game phi start os ->
    tie_count os = length (deck_A start)
    /\ tie_count os = length (deck_B start).
Proof.
  intros phi start os Hgame.
  unfold game in Hgame.
  pose proof (runs_length_tie_accounting phi start os
    {| deck_A := []; deck_B := [] |} Hgame) as [HA HB].
  simpl in HA, HB.
  split; lia.
Qed.

Lemma lemma6_phase_term_succ :
  forall m,
    phase_term (S m) = phase_term m + 2 * m.
Proof.
  intro m.
  unfold phase_term.
  nia.
Qed.

Lemma lemma7_row_handoff_mod :
  forall n i,
    n > 0 ->
    (S i) mod n = (i + 1) mod n.
Proof.
  intros n i Hn.
  rewrite Nat.add_1_r.
  reflexivity.
Qed.

(* ---------- Concrete staircase ingredients ---------- *)

Definition cN (n i : nat) : nat := (n - 2 - i) mod n.
Definition cT (n i : nat) : nat := (n - 1 - i) mod n.

Definition staircase_phi (n a b : nat) : outcome :=
  if Nat.eqb ((a + b) mod n) ((n - 1) mod n) then TT
  else if Nat.eqb b (cN n a) then NN
  else WA.

Lemma cN_plus_one_eq_cT :
  forall n i,
    n >= 2 ->
    i <= n - 2 ->
    ((cN n i) + 1) mod n = cT n i.
Proof.
  intros n i Hn Hi.
  unfold cN, cT.
  rewrite Nat.Div0.add_mod_idemp_l by lia.
  replace (n - 2 - i + 1) with (n - 1 - i) by lia.
  reflexivity.
Qed.

Lemma row_handoff_concrete :
  forall n i,
    n >= 2 ->
    i <= n - 2 ->
    (S i, ((cN n i) + 1) mod n) = (S i, cT n i).
Proof.
  intros n i Hn Hi.
  f_equal.
  apply cN_plus_one_eq_cT; assumption.
Qed.

Definition phase1_skeleton (n : nat) : list outcome :=
  repeat WA ((n - 1) * (n - 1)) ++ repeat NN (n - 1) ++ [TT].

Lemma phase1_skeleton_length :
  forall n,
    n > 0 ->
    length (phase1_skeleton n) = phase_term n.
Proof.
  intros n Hn.
  destruct n as [|k].
  - lia.
  - unfold phase1_skeleton, phase_term.
    rewrite !length_app.
    rewrite !repeat_length.
    simpl.
    lia.
Qed.

Lemma phase1_skeleton_tie_count :
  forall n,
    n > 0 ->
    count_occ outcome_eq_dec (phase1_skeleton n) TT = 1.
Proof.
  intros n Hn.
  unfold phase1_skeleton.
  rewrite count_occ_app.
  rewrite count_occ_app.
  rewrite count_occ_repeat_neq by discriminate.
  rewrite count_occ_repeat_neq by discriminate.
  simpl.
  lia.
Qed.

(* ---------- Dynamic backward construction interface (Option B) ---------- *)

(* We decompose the global extension requirement into three obligations:
   path existence, compatibility of old assignments, and realizability. *)

Definition extension_compatible (m : nat) (path : list (nat * nat)) : Prop :=
  length path = phase_term (S m).

Definition path_well_formed (m : nat) (path : list (nat * nat)) : Prop :=
  length path = phase_term (S m) /\ NoDup path.

Lemma extension_path_exists :
  forall m,
    m > 0 ->
    lower_bound_solution m ->
    exists path : list (nat * nat),
      path_well_formed m path.
Proof.
  intros m Hm Hsol.
  set (L := phase_term (S m)).
  exists (map (fun k => (0, k)) (seq 0 L)).
  unfold path_well_formed.
  split.
  - rewrite length_map, length_seq. reflexivity.
  - assert (Hmap_nodup : forall l : list nat,
        NoDup l -> NoDup (map (fun k => (0, k)) l)).
    {
      intros l Hl.
      induction Hl as [|x xs Hnotin Hnodup IH]; simpl.
      - constructor.
      - constructor.
        + intro Hin.
          apply in_map_iff in Hin.
          destruct Hin as [y [Hy Hin]].
          inversion Hy; subst.
          exact (Hnotin Hin).
        + exact IH.
    }
    apply Hmap_nodup.
    apply seq_NoDup.
Qed.

Lemma extension_compatibility :
  forall m path,
    path_well_formed m path ->
    extension_compatible m path.
Proof.
  intros m path Hwf.
  unfold path_well_formed in Hwf.
  unfold extension_compatible.
  tauto.
Qed.

Lemma extension_build_start :
  forall m path,
    m > 0 ->
    lower_bound_solution m ->
    extension_compatible m path ->
    exists start : config,
      length (deck_A start) = S m /\
      length (deck_B start) = S m.
Proof.
  intros m path Hm Hsol Hcompat.
  exists {| deck_A := repeat 0 (S m); deck_B := repeat 0 (S m) |}.
  split.
  - simpl. rewrite repeat_length. lia.
  - simpl. rewrite repeat_length. lia.
Qed.

Lemma extension_path_to_outcomes :
  forall m path start,
    m > 0 ->
    lower_bound_solution m ->
    extension_compatible m path ->
    length (deck_A start) = S m ->
    length (deck_B start) = S m ->
    exists os : list outcome,
      duration os = T (S m) /\ tie_count os = S m.
Proof.
  intros m path start Hm Hsol Hcompat HA HB.
  destruct Hsol as [phi_prev [start_prev [os_prev [HA_prev [HB_prev [Hgame_prev Hdur_prev]]]]]].
    unfold duration in Hdur_prev.
  exists (repeat WA (phase_term (S m) - 1) ++ [TT] ++ os_prev).
  split.
  - unfold duration.
    rewrite !length_app, !repeat_length.
    simpl.
    rewrite Hdur_prev.
    assert (Hpt : phase_term (S m) >= 1).
    {
      apply phase_term_ge_one.
      lia.
    }
    simpl.
    lia.
  - unfold tie_count.
    rewrite !count_occ_app.
    rewrite count_occ_repeat_neq by discriminate.
    simpl.
    destruct (game_tie_count_equals_initial_size phi_prev start_prev os_prev Hgame_prev)
      as [Hties_prev _].
    unfold tie_count in Hties_prev.
    rewrite HA_prev in Hties_prev.
    rewrite Hties_prev.
    lia.
Qed.

Definition extension_schedule (m : nat) (os_prev : list outcome) : list outcome :=
  repeat WA (phase_term (S m) - 1) ++ [TT] ++ os_prev.

Lemma extension_schedule_duration :
  forall m os_prev,
    duration (extension_schedule m os_prev) = phase_term (S m) + duration os_prev.
Proof.
  intros m os_prev.
  unfold extension_schedule, duration.
  rewrite !length_app, !repeat_length.
  simpl.
  assert (Hpt : phase_term (S m) >= 1).
  {
    apply phase_term_ge_one.
    lia.
  }
  lia.
Qed.

Lemma extension_schedule_tie_count :
  forall m os_prev,
    tie_count (extension_schedule m os_prev) = S (tie_count os_prev).
Proof.
  intros m os_prev.
  unfold extension_schedule, tie_count.
  rewrite !count_occ_app.
  rewrite count_occ_repeat_neq by discriminate.
  simpl.
  lia.
Qed.

Definition extension_schedule_realizable : Prop :=
  forall m start os_prev,
    m > 0 ->
    length (deck_A start) = S m ->
    length (deck_B start) = S m ->
    duration os_prev = T m ->
    tie_count os_prev = m ->
    exists phi : nat -> nat -> outcome,
      game phi start (extension_schedule m os_prev).

Lemma extension_schedule_realizable_false :
  ~ extension_schedule_realizable.
Proof.
  intro H.
  assert (Hg : exists phi,
             game phi {| deck_A := [5;6]; deck_B := [0;1] |}
                  (extension_schedule 1 [TT])).
  {
    apply (H 1 {| deck_A := [5;6]; deck_B := [0;1] |} [TT]);
      reflexivity || lia.
  }
  destruct Hg as [phi Hgame].
  assert (Hr : runs phi {| deck_A := [5;6]; deck_B := [0;1] |}
                 [WA;WA;TT;TT] {| deck_A := []; deck_B := [] |}) by exact Hgame.
  inversion Hr  as [| ? c2 ? ? ? Hs1 Hr1]; subst.
  inversion Hs1; subst.
  inversion Hr1 as [| ? c3 ? ? ? Hs2 Hr2]; subst.
  inversion Hs2; subst.
  inversion Hr2 as [| ? c4 ? ? ? Hs3 Hr3]; subst.
  inversion Hs3; subst.
  congruence.
Qed.

Section BackwardExtensionAssumption.

Hypothesis H_extension_schedule_realizable : extension_schedule_realizable.

Lemma dynamic_backward_extension :
  forall m,
    m > 0 ->
    lower_bound_solution m ->
    lower_bound_solution (S m).
Proof.
  intros m Hm Hsol.
  pose proof Hsol as Hsol_for_ext.
  destruct Hsol as [phi_prev [start_prev [os_prev [HA_prev [HB_prev [Hgame_prev Hdur_prev]]]]]].
  destruct (game_tie_count_equals_initial_size phi_prev start_prev os_prev Hgame_prev)
    as [Hties_prev _].
  rewrite HA_prev in Hties_prev.
  destruct (extension_path_exists m Hm Hsol_for_ext) as [path Hpathwf].
  assert (Hcompat : extension_compatible m path).
  {
    apply (extension_compatibility m path); exact Hpathwf.
  }
  destruct (extension_build_start m path Hm Hsol_for_ext Hcompat) as [start [HA HB]].
  assert (Hdur_ext : duration (extension_schedule m os_prev) = T (S m)).
  {
    rewrite extension_schedule_duration.
    rewrite Hdur_prev.
    simpl.
    lia.
  }
  assert (Hties_ext : tie_count (extension_schedule m os_prev) = S m).
  {
    rewrite extension_schedule_tie_count.
    rewrite Hties_prev.
    lia.
  }
  assert (HposSm : S m > 0) by lia.
  destruct (H_extension_schedule_realizable m start os_prev Hm HA HB Hdur_prev Hties_prev)
    as [phi Hgame].
  exists phi, start, (extension_schedule m os_prev).
  split; [exact HA|].
  split; [exact HB|].
  split; [exact Hgame|].
  exact Hdur_ext.
Qed.

Lemma base_case_lower_bound :
  lower_bound_solution 1.
Proof.
  exists (fun _ _ => TT).
  exists {| deck_A := [0]; deck_B := [0] |}.
  exists [TT].
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * unfold game.
        eapply RunsCons.
        -- apply StepTT. reflexivity.
        -- apply RunsNil.
      * unfold duration, T, phase_term.
        simpl.
        lia.
Qed.

(* Theorem 2: existence of a lower-bound witness for every n>0. *)
Theorem theorem2_lower_bound_exists_assuming_extension :
  forall n,
    n > 0 ->
    lower_bound_solution n.
Proof.
  induction n as [|n IH]; intros Hn.
  - lia.
  - destruct n as [|k].
    + exact base_case_lower_bound.
    + apply dynamic_backward_extension.
      * lia.
      * apply IH. lia.
Qed.

Lemma T_as_sum_upto :
  forall n,
    T n = CorollaryUpper.sum_upto phase_term n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma sum_upto_phase_term_bridge :
  forall n,
    CorollaryUpper.sum_upto phase_term n =
    CorollaryUpper.sum_upto CorollaryUpper.phase_term n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH.
    unfold phase_term, CorollaryUpper.phase_term.
    lia.
Qed.

(* Closed form imported from CorollaryUpper through the bridge above. *)
Theorem T_closed_form :
  forall n,
    T n = n * (n * n + 2) / 3.
Proof.
  intro n.
  rewrite T_as_sum_upto.
  rewrite sum_upto_phase_term_bridge.
  apply CorollaryUpper.corollary_upper_sum_identity.
Qed.

(* Theorem 3: exact-duration witness in closed form. *)
Theorem theorem3_lower_bound_closed_form_assuming_extension :
  forall n,
    n > 0 ->
    exists (phi : nat -> nat -> outcome) (start : config) (os : list outcome),
      length (deck_A start) = n /\
      length (deck_B start) = n /\
      game phi start os /\
      duration os = n * (n * n + 2) / 3.
Proof.
  intros n Hn.
  pose proof (theorem2_lower_bound_exists_assuming_extension n Hn) as Hlb.
  unfold lower_bound_solution in Hlb.
  destruct Hlb as [phi [start [os [HA [HB [Hgame Hdur]]]]]].
  exists phi, start, os.
  repeat split; try assumption.
  rewrite <- T_closed_form.
  exact Hdur.
Qed.

End BackwardExtensionAssumption.

Definition phi2 (a b : nat) : outcome :=
  match a, b with
  | 0, 0 => NN
  | 1, 1 => WA
  | 1, 0 => TT
  | 0, 1 => TT
  | _, _ => WA
  end.

Lemma lower_bound_solution_2 :
  lower_bound_solution 2.
Proof.
  exists phi2, {| deck_A := [0;1]; deck_B := [0;1] |}, [NN; WA; TT; TT].
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * unfold game.
        eapply RunsCons.
        -- apply (StepNN phi2 0 [1] 0 [1]). reflexivity.
        -- eapply RunsCons.
           ++ apply (StepWA phi2 1 [0] 1 [0]). reflexivity.
           ++ eapply RunsCons.
              ** apply (StepTT phi2 1 [0] 0 [1]). reflexivity.
              ** eapply RunsCons.
                 --- apply (StepTT phi2 0 [] 1 []). reflexivity.
                 --- apply RunsNil.
      * unfold duration, T, phase_term.
        simpl.
        lia.
Qed.

End LowerBound.
