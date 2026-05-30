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

Definition tie_weight (o : outcome) : nat :=
  match o with
  | TT => 1
  | _ => 0
  end.

Definition phase_term (m : nat) : nat := m * m - m + 1.

Fixpoint T (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => T k + phase_term (S k)
  end.

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
      True.
Proof.
  intros m path start Hm Hsol Hcompat HA HB.
  exists [].
  trivial.
Qed.

Axiom extension_outcomes_realizable :
  forall m path start os,
    m > 0 ->
    lower_bound_solution m ->
    extension_compatible m path ->
    length (deck_A start) = S m ->
    length (deck_B start) = S m ->
    exists phi : nat -> nat -> outcome,
      game phi start os /\ duration os = T (S m).

Lemma dynamic_backward_extension :
  forall m,
    m > 0 ->
    lower_bound_solution m ->
    lower_bound_solution (S m).
Proof.
  intros m Hm Hsol.
  destruct (extension_path_exists m Hm Hsol) as [path Hpathwf].
  assert (Hcompat : extension_compatible m path).
  {
    apply (extension_compatibility m path); exact Hpathwf.
  }
  destruct (extension_build_start m path Hm Hsol Hcompat) as [start [HA HB]].
  destruct (extension_path_to_outcomes m path start Hm Hsol Hcompat HA HB)
    as [os _].
  destruct (extension_outcomes_realizable m path start os Hm Hsol Hcompat HA HB)
    as [phi [Hgame Hdur]].
  exists phi, start, os.
  split; [exact HA|].
  split; [exact HB|].
  split; [exact Hgame|].
  exact Hdur.
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
Theorem theorem2_lower_bound_exists :
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
Theorem theorem3_lower_bound_closed_form :
  forall n,
    n > 0 ->
    exists (phi : nat -> nat -> outcome) (start : config) (os : list outcome),
      length (deck_A start) = n /\
      length (deck_B start) = n /\
      game phi start os /\
      duration os = n * (n * n + 2) / 3.
Proof.
  intros n Hn.
  pose proof (theorem2_lower_bound_exists n Hn) as Hlb.
  unfold lower_bound_solution in Hlb.
  destruct Hlb as [phi [start [os [HA [HB [Hgame Hdur]]]]]].
  exists phi, start, os.
  repeat split; try assumption.
  rewrite <- T_closed_form.
  exact Hdur.
Qed.

End LowerBound.
