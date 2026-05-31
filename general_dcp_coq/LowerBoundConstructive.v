From Stdlib Require Import List Arith Lia.
Require Import LowerBound TheoremPhasewise.
Import ListNotations.

Section ConstructiveScaffold.

Definition move_top_to_bottom {X : Type} (xs : list X) : list X :=
  match xs with
  | [] => []
  | x :: xs' => xs' ++ [x]
  end.

Lemma move_top_to_bottom_length :
  forall X (xs : list X),
    length (move_top_to_bottom xs) = length xs.
Proof.
  intros X xs.
  destruct xs as [|x xs]; simpl; [reflexivity|].
  rewrite length_app.
  simpl.
  lia.
Qed.

Lemma iter_move_top_to_bottom_comm :
  forall X (xs : list X) n,
    Nat.iter n move_top_to_bottom (move_top_to_bottom xs) =
    move_top_to_bottom (Nat.iter n move_top_to_bottom xs).
Proof.
  intros X xs n.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma iter_move_top_to_bottom_length :
  forall X (xs : list X) n,
    length (Nat.iter n move_top_to_bottom xs) = length xs.
Proof.
  intros X xs n.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite move_top_to_bottom_length.
    exact IH.
Qed.

Lemma runs_cons_inv :
  forall phi c o os c',
    LowerBound.runs phi c (o :: os) c' ->
    exists c2,
      LowerBound.step phi c o c2 /\
      LowerBound.runs phi c2 os c'.
Proof.
  intros phi c o os c' Hr.
  inversion Hr; subst.
  eauto.
Qed.

Lemma step_WA_from_heads :
  forall phi a as_ b bs c2,
    LowerBound.step phi
      {| LowerBound.deck_A := a :: as_; LowerBound.deck_B := b :: bs |}
      LowerBound.WA c2 ->
    c2 =
      {| LowerBound.deck_A := a :: as_; LowerBound.deck_B := bs ++ [b] |}.
Proof.
  intros phi a as_ b bs c2 Hs.
  inversion Hs; subst; reflexivity.
Qed.

Lemma step_NN_from_heads :
  forall phi a as_ b bs c2,
    LowerBound.step phi
      {| LowerBound.deck_A := a :: as_; LowerBound.deck_B := b :: bs |}
      LowerBound.NN c2 ->
    c2 =
      {| LowerBound.deck_A := as_ ++ [a]; LowerBound.deck_B := bs ++ [b] |}.
Proof.
  intros phi a as_ b bs c2 Hs.
  inversion Hs; subst; reflexivity.
Qed.

Lemma step_NN_head_value :
  forall phi a as_ b bs c2,
    LowerBound.step phi
      {| LowerBound.deck_A := a :: as_; LowerBound.deck_B := b :: bs |}
      LowerBound.NN c2 ->
    phi a b = LowerBound.NN.
Proof.
  intros phi a as_ b bs c2 Hs.
  inversion Hs; subst; assumption.
Qed.

Lemma step_WA_head_value :
  forall phi a as_ b bs c2,
    LowerBound.step phi
      {| LowerBound.deck_A := a :: as_; LowerBound.deck_B := b :: bs |}
      LowerBound.WA c2 ->
    phi a b = LowerBound.WA.
Proof.
  intros phi a as_ b bs c2 Hs.
  inversion Hs; subst; assumption.
Qed.

Lemma step_WA_heads_advance_B_when_nonempty_tail :
  forall phi a as_ b b2 bs2 c2,
    LowerBound.step phi
      {| LowerBound.deck_A := a :: as_; LowerBound.deck_B := b :: b2 :: bs2 |}
      LowerBound.WA c2 ->
    LowerBound.deck_A c2 = a :: as_ /\
    LowerBound.deck_B c2 = b2 :: (bs2 ++ [b]).
Proof.
  intros phi a as_ b b2 bs2 c2 Hs.
  inversion Hs; subst.
  simpl.
  split; reflexivity.
Qed.

Lemma step_NN_heads_advance_both_when_nonempty_tails :
  forall phi a a2 as2 b b2 bs2 c2,
    LowerBound.step phi
      {| LowerBound.deck_A := a :: a2 :: as2;
         LowerBound.deck_B := b :: b2 :: bs2 |}
      LowerBound.NN c2 ->
    LowerBound.deck_A c2 = a2 :: (as2 ++ [a]) /\
    LowerBound.deck_B c2 = b2 :: (bs2 ++ [b]).
Proof.
  intros phi a a2 as2 b b2 bs2 c2 Hs.
  inversion Hs; subst.
  simpl.
  split; reflexivity.
Qed.

Lemma runs_repeat_WA_shape :
  forall phi k c c',
    LowerBound.runs phi c (repeat LowerBound.WA k) c' ->
    LowerBound.deck_A c' = LowerBound.deck_A c /\
    LowerBound.deck_B c' = Nat.iter k move_top_to_bottom (LowerBound.deck_B c).
Proof.
  intros phi k.
  induction k as [|k IH]; intros c c' Hr.
  - simpl in Hr.
    inversion Hr; subst.
    split; reflexivity.
  - simpl in Hr.
    destruct (runs_cons_inv phi c LowerBound.WA (repeat LowerBound.WA k) c' Hr)
      as [c2 [Hs Hr2]].
    specialize (IH c2 c' Hr2).
    destruct IH as [HA HB].
    assert (Hshape :
      LowerBound.deck_A c2 = LowerBound.deck_A c /\
      LowerBound.deck_B c2 = move_top_to_bottom (LowerBound.deck_B c)).
    {
      inversion Hs; subst.
      simpl.
      split; reflexivity.
    }
    destruct Hshape as [HAc HBc].
    split.
    + rewrite HA.
      exact HAc.
    + simpl.
      rewrite HB.
      rewrite HBc.
      rewrite iter_move_top_to_bottom_comm.
      reflexivity.
Qed.

Lemma runs_repeat_NN_shape :
  forall phi k c c',
    LowerBound.runs phi c (repeat LowerBound.NN k) c' ->
    LowerBound.deck_A c' = Nat.iter k move_top_to_bottom (LowerBound.deck_A c) /\
    LowerBound.deck_B c' = Nat.iter k move_top_to_bottom (LowerBound.deck_B c).
Proof.
  intros phi k.
  induction k as [|k IH]; intros c c' Hr.
  - simpl in Hr.
    inversion Hr; subst.
    split; reflexivity.
  - simpl in Hr.
    destruct (runs_cons_inv phi c LowerBound.NN (repeat LowerBound.NN k) c' Hr)
      as [c2 [Hs Hr2]].
    specialize (IH c2 c' Hr2).
    destruct IH as [HA HB].
    assert (Hshape :
      LowerBound.deck_A c2 = move_top_to_bottom (LowerBound.deck_A c) /\
      LowerBound.deck_B c2 = move_top_to_bottom (LowerBound.deck_B c)).
    {
      inversion Hs; subst.
      simpl.
      split; reflexivity.
    }
    destruct Hshape as [HAc HBc].
    split.
    + simpl.
      rewrite HA.
      rewrite HAc.
      rewrite iter_move_top_to_bottom_comm.
      reflexivity.
    + simpl.
      rewrite HB.
      rewrite HBc.
      rewrite iter_move_top_to_bottom_comm.
      reflexivity.
Qed.

Lemma runs_app_inv :
  forall phi c os1 os2 c',
    LowerBound.runs phi c (os1 ++ os2) c' ->
    exists cm,
      LowerBound.runs phi c os1 cm /\
      LowerBound.runs phi cm os2 c'.
Proof.
  intros phi c os1.
  revert c.
  induction os1 as [|o os1 IH]; intros c os2 c' Hr.
  - simpl in Hr.
    exists c.
    split.
    + apply LowerBound.RunsNil.
    + exact Hr.
  - simpl in Hr.
    destruct (runs_cons_inv phi c o (os1 ++ os2) c' Hr) as [c2 [Hs Hr2]].
    destruct (IH c2 os2 c' Hr2) as [cm [Hleft Hright]].
    exists cm.
    split.
    + eapply LowerBound.RunsCons.
      * exact Hs.
      * exact Hleft.
    + exact Hright.
Qed.

Lemma runs_app :
  forall phi c os1 cm os2 c',
    LowerBound.runs phi c os1 cm ->
    LowerBound.runs phi cm os2 c' ->
    LowerBound.runs phi c (os1 ++ os2) c'.
Proof.
  intros phi c os1.
  revert c.
  induction os1 as [|o os1 IH]; intros c cm os2 c' H1 H2.
  - inversion H1; subst.
    simpl.
    exact H2.
  - destruct (runs_cons_inv phi c o os1 cm H1) as [c2 [Hs Hr_tail]].
    simpl.
    eapply LowerBound.RunsCons.
    + exact Hs.
    + eapply IH.
      * exact Hr_tail.
      * exact H2.
Qed.

Lemma runs_repeat_WA_then_NN_shape :
  forall phi p q c c',
    LowerBound.runs phi c (repeat LowerBound.WA p ++ repeat LowerBound.NN q) c' ->
    LowerBound.deck_A c' = Nat.iter q move_top_to_bottom (LowerBound.deck_A c) /\
    LowerBound.deck_B c' = Nat.iter q move_top_to_bottom
                          (Nat.iter p move_top_to_bottom (LowerBound.deck_B c)).
Proof.
  intros phi p q c c' Hr.
  destruct (runs_app_inv phi c (repeat LowerBound.WA p) (repeat LowerBound.NN q) c' Hr)
    as [cm [Hwa Hnn]].
  destruct (runs_repeat_WA_shape phi p c cm Hwa) as [HAwa HBwa].
  destruct (runs_repeat_NN_shape phi q cm c' Hnn) as [HAnn HBnn].
  split.
  - rewrite HAnn.
    rewrite HAwa.
    reflexivity.
  - rewrite HBnn.
    rewrite HBwa.
    reflexivity.
Qed.

Lemma runs_nil_inv :
  forall phi c c',
    LowerBound.runs phi c [] c' ->
    c' = c.
Proof.
  intros phi c c' Hr.
  inversion Hr; subst; reflexivity.
Qed.

Lemma step_TT_from_heads :
  forall phi a as_ b bs c2,
    LowerBound.step phi
      {| LowerBound.deck_A := a :: as_; LowerBound.deck_B := b :: bs |}
      LowerBound.TT c2 ->
    c2 =
      {| LowerBound.deck_A := as_; LowerBound.deck_B := bs |}.
Proof.
  intros phi a as_ b bs c2 Hs.
  inversion Hs; subst; reflexivity.
Qed.

Lemma runs_repeat_WA_then_NN_then_TT_structure :
  forall phi p q c c',
    LowerBound.runs phi c
      (repeat LowerBound.WA p ++ repeat LowerBound.NN q ++ [LowerBound.TT]) c' ->
    exists cm a as_ b bs,
      LowerBound.runs phi c (repeat LowerBound.WA p ++ repeat LowerBound.NN q) cm /\
      LowerBound.deck_A cm = a :: as_ /\
      LowerBound.deck_B cm = b :: bs /\
      LowerBound.deck_A c' = as_ /\
      LowerBound.deck_B c' = bs.
Proof.
  intros phi p q c c' Hr.
  rewrite app_assoc in Hr.
  destruct (runs_app_inv phi c
              (repeat LowerBound.WA p ++ repeat LowerBound.NN q)
              [LowerBound.TT] c' Hr)
    as [cm [Hprefix Htt]].
  destruct (runs_cons_inv phi cm LowerBound.TT [] c' Htt) as [c2 [Hs Hnil]].
  assert (Hc2 : c2 = c').
  {
    symmetry.
    apply runs_nil_inv with (phi := phi).
    exact Hnil.
  }
  rewrite Hc2 in Hs.
  clear Hc2 Hnil Htt.
  inversion Hs; subst.
  exists {| LowerBound.deck_A := a :: as_; LowerBound.deck_B := b :: bs |}.
  exists a, as_, b, bs.
  repeat split; try reflexivity.
  exact Hprefix.
Qed.

Definition non_tie_count (os : list LowerBound.outcome) : nat :=
  length os - LowerBound.tie_count os.

Definition phase_block_trace (p q : nat) : list LowerBound.outcome :=
  repeat LowerBound.WA p ++ repeat LowerBound.NN q ++ [LowerBound.TT].

Lemma phase_block_trace_tie_count :
  forall p q,
    LowerBound.tie_count (phase_block_trace p q) = 1.
Proof.
  intros p q.
  unfold phase_block_trace, LowerBound.tie_count.
  rewrite !count_occ_app.
  rewrite count_occ_repeat_neq by discriminate.
  rewrite count_occ_repeat_neq by discriminate.
  simpl.
  lia.
Qed.

Lemma phase_block_trace_non_tie_count :
  forall p q,
    non_tie_count (phase_block_trace p q) = p + q.
Proof.
  intros p q.
  unfold non_tie_count.
  rewrite phase_block_trace_tie_count.
  unfold phase_block_trace.
  rewrite !length_app.
  rewrite !repeat_length.
  simpl.
  lia.
Qed.

Theorem phase_block_realizes_budget :
  forall phi p q c c',
    LowerBound.runs phi c (phase_block_trace p q) c' ->
    non_tie_count (phase_block_trace p q) = p + q /\
    LowerBound.tie_count (phase_block_trace p q) = 1 /\
    exists cm a as_ b bs,
      LowerBound.runs phi c (repeat LowerBound.WA p ++ repeat LowerBound.NN q) cm /\
      LowerBound.deck_A cm = a :: as_ /\
      LowerBound.deck_B cm = b :: bs /\
      LowerBound.deck_A c' = as_ /\
      LowerBound.deck_B c' = bs.
Proof.
  intros phi p q c c' Hr.
  split.
  - apply phase_block_trace_non_tie_count.
  - split.
    + apply phase_block_trace_tie_count.
    + unfold phase_block_trace in Hr.
      exact (runs_repeat_WA_then_NN_then_TT_structure phi p q c c' Hr).
Qed.

Corollary phase_block_decks_drop_by_one :
  forall phi p q c c',
    LowerBound.runs phi c (phase_block_trace p q) c' ->
    length (LowerBound.deck_A c') = length (LowerBound.deck_A c) - 1 /\
    length (LowerBound.deck_B c') = length (LowerBound.deck_B c) - 1.
Proof.
  intros phi p q c c' Hr.
  pose proof (LowerBound.runs_length_tie_accounting
                phi c (phase_block_trace p q) c' Hr) as [HA HB].
  rewrite phase_block_trace_tie_count in HA.
  rewrite phase_block_trace_tie_count in HB.
  split.
  - lia.
  - lia.
Qed.

Corollary phase_block_post_decks_explicit :
  forall phi p q c c',
    LowerBound.runs phi c (phase_block_trace p q) c' ->
    exists a as_ b bs,
      Nat.iter q move_top_to_bottom (LowerBound.deck_A c) = a :: as_ /\
      Nat.iter q move_top_to_bottom
        (Nat.iter p move_top_to_bottom (LowerBound.deck_B c)) = b :: bs /\
      LowerBound.deck_A c' = as_ /\
      LowerBound.deck_B c' = bs.
Proof.
  intros phi p q c c' Hr.
  destruct (phase_block_realizes_budget phi p q c c' Hr)
    as [_ [_ [cm [a [as_ [b [bs [Hprefix [HAcm [HBcm [HAc' HBc']]]]]]]]]]].
  destruct (runs_repeat_WA_then_NN_shape phi p q c cm Hprefix) as [HAshape HBshape].
  exists a, as_, b, bs.
  repeat split; try assumption.
  - rewrite <- HAshape.
    exact HAcm.
  - rewrite <- HBshape.
    exact HBcm.
Qed.

Theorem phase_block_permutation_handoff :
  forall phi p q c c' m,
    length (LowerBound.deck_A c) = m ->
    length (LowerBound.deck_B c) = m ->
    LowerBound.runs phi c (phase_block_trace p q) c' ->
    exists a as_ b bs,
      Nat.iter q move_top_to_bottom (LowerBound.deck_A c) = a :: as_ /\
      Nat.iter q move_top_to_bottom
        (Nat.iter p move_top_to_bottom (LowerBound.deck_B c)) = b :: bs /\
      LowerBound.deck_A c' = as_ /\
      LowerBound.deck_B c' = bs /\
      length as_ = m - 1 /\
      length bs = m - 1.
Proof.
  intros phi p q c c' m HAm HBm Hr.
  destruct (phase_block_post_decks_explicit phi p q c c' Hr)
    as [a [as_ [b [bs [HAiter [HBiter [HAc' HBc']]]]]]].
  exists a, as_, b, bs.
  repeat split; try assumption.
  - assert (HlenA : length (a :: as_) = m).
    {
      rewrite <- HAiter.
      rewrite iter_move_top_to_bottom_length.
      exact HAm.
    }
    simpl in HlenA.
    lia.
  - assert (HlenB : length (b :: bs) = m).
    {
      rewrite <- HBiter.
      rewrite iter_move_top_to_bottom_length.
      rewrite iter_move_top_to_bottom_length.
      exact HBm.
    }
    simpl in HlenB.
    lia.
Qed.

Theorem phase_block_handoff_from_canonical_rotations :
  forall phi p q c c' a_top a_tail b_top b_tail,
    LowerBound.runs phi c (phase_block_trace p q) c' ->
    Nat.iter q move_top_to_bottom (LowerBound.deck_A c) = a_top :: a_tail ->
    Nat.iter q move_top_to_bottom
      (Nat.iter p move_top_to_bottom (LowerBound.deck_B c)) = b_top :: b_tail ->
    LowerBound.deck_A c' = a_tail /\
    LowerBound.deck_B c' = b_tail.
Proof.
  intros phi p q c c' a_top a_tail b_top b_tail Hr HAcanon HBcanon.
  destruct (phase_block_post_decks_explicit phi p q c c' Hr)
    as [a [as_ [b [bs [HAiter [HBiter [HAc' HBc']]]]]]].
  rewrite HAcanon in HAiter.
  injection HAiter as _ Has.
  rewrite HBcanon in HBiter.
  injection HBiter as _ Hbs.
  split.
  - rewrite HAc'.
    symmetry.
    exact Has.
  - rewrite HBc'.
    symmetry.
    exact Hbs.
Qed.

Theorem phase_endpoint_canonical_handoff_and_budget :
  forall phi p q c c' m a_top a_tail b_top b_tail n,
    m > 2 ->
    LowerBound.runs phi c (phase_block_trace p q) c' ->
    length (LowerBound.deck_A c) = m ->
    length (LowerBound.deck_B c) = m ->
    Nat.iter q move_top_to_bottom (LowerBound.deck_A c) = a_top :: a_tail ->
    Nat.iter q move_top_to_bottom
      (Nat.iter p move_top_to_bottom (LowerBound.deck_B c)) = b_top :: b_tail ->
    LowerBound.deck_A c' = a_tail /\
    LowerBound.deck_B c' = b_tail /\
    length a_tail = m - 1 /\
    length b_tail = m - 1 /\
    LowerBound.phase_term m = (m - 1) * (m - 1) + m /\
    LowerBound.T n = n * (n * n + 2) / 3.
Proof.
  intros phi p q c c' m a_top a_tail b_top b_tail n Hm Hr HAm HBm HAcanon HBcanon.
  destruct (phase_block_permutation_handoff phi p q c c' m HAm HBm Hr)
    as [a [as_ [b [bs [HAiter [HBiter [HAcp [HBcp [HlenA HlenB]]]]]]]]].
  destruct (phase_block_handoff_from_canonical_rotations
              phi p q c c' a_top a_tail b_top b_tail Hr HAcanon HBcanon)
    as [HAc HBc].
  assert (Ha_tail : a_tail = as_) by congruence.
  assert (Hb_tail : b_tail = bs) by congruence.
  assert (Hmcase : LowerBound.phase_term m = (m - 1) * (m - 1) + m).
  {
    unfold LowerBound.phase_term.
    nia.
  }
  pose proof (LowerBound.T_closed_form n) as HT.
  repeat split.
  - exact HAc.
  - exact HBc.
  - rewrite Ha_tail.
    exact HlenA.
  - rewrite Hb_tail.
    exact HlenB.
  - exact Hmcase.
  - exact HT.
Qed.

Lemma two_phase_run_accounting :
  forall phi c1 c2 c3 os1 os2,
    LowerBound.runs phi c1 os1 c2 ->
    LowerBound.runs phi c2 os2 c3 ->
    LowerBound.runs phi c1 (os1 ++ os2) c3 /\
    LowerBound.duration (os1 ++ os2) = LowerBound.duration os1 + LowerBound.duration os2 /\
    LowerBound.tie_count (os1 ++ os2) = LowerBound.tie_count os1 + LowerBound.tie_count os2.
Proof.
  intros phi c1 c2 c3 os1 os2 H1 H2.
  split.
  - apply (runs_app phi c1 os1 c2 os2 c3 H1 H2).
  - split.
    + unfold LowerBound.duration.
      rewrite length_app.
      reflexivity.
    + unfold LowerBound.tie_count.
      rewrite count_occ_app.
      reflexivity.
Qed.

Lemma phase_block_trace_duration :
  forall p q,
    LowerBound.duration (phase_block_trace p q) = p + q + 1.
Proof.
  intros p q.
  unfold LowerBound.duration, phase_block_trace.
  rewrite !length_app.
  rewrite !repeat_length.
  simpl.
  lia.
Qed.

Corollary two_phase_blocks_duration_ties :
  forall phi p1 q1 p2 q2 c1 c2 c3,
    LowerBound.runs phi c1 (phase_block_trace p1 q1) c2 ->
    LowerBound.runs phi c2 (phase_block_trace p2 q2) c3 ->
    LowerBound.duration (phase_block_trace p1 q1 ++ phase_block_trace p2 q2)
      = (p1 + q1 + 1) + (p2 + q2 + 1) /\
    LowerBound.tie_count (phase_block_trace p1 q1 ++ phase_block_trace p2 q2)
      = 2.
Proof.
  intros phi p1 q1 p2 q2 c1 c2 c3 Hr1 Hr2.
  destruct (two_phase_run_accounting phi c1 c2 c3
              (phase_block_trace p1 q1) (phase_block_trace p2 q2) Hr1 Hr2)
    as [_ [Hdur Htie]].
  split.
  - rewrite phase_block_trace_duration in Hdur.
    rewrite phase_block_trace_duration in Hdur.
    exact Hdur.
  - rewrite phase_block_trace_tie_count in Htie.
    rewrite phase_block_trace_tie_count in Htie.
    exact Htie.
Qed.

Corollary two_phase_blocks_decks_drop_by_two :
  forall phi p1 q1 p2 q2 c1 c2 c3,
    LowerBound.runs phi c1 (phase_block_trace p1 q1) c2 ->
    LowerBound.runs phi c2 (phase_block_trace p2 q2) c3 ->
    length (LowerBound.deck_A c3) = length (LowerBound.deck_A c1) - 2 /\
    length (LowerBound.deck_B c3) = length (LowerBound.deck_B c1) - 2.
Proof.
  intros phi p1 q1 p2 q2 c1 c2 c3 Hr1 Hr2.
  destruct (two_phase_run_accounting phi c1 c2 c3
              (phase_block_trace p1 q1) (phase_block_trace p2 q2) Hr1 Hr2)
    as [Hr12 [_ Htie12]].
  pose proof (LowerBound.runs_length_tie_accounting
                phi c1
                (phase_block_trace p1 q1 ++ phase_block_trace p2 q2)
                c3 Hr12) as [HA HB].
  assert (Ht1 : LowerBound.tie_count (phase_block_trace p1 q1) = 1)
    by apply phase_block_trace_tie_count.
  assert (Ht2 : LowerBound.tie_count (phase_block_trace p2 q2) = 1)
    by apply phase_block_trace_tie_count.
  rewrite Htie12 in HA.
  rewrite Htie12 in HB.
  rewrite Ht1 in HA.
  rewrite Ht2 in HA.
  rewrite Ht1 in HB.
  rewrite Ht2 in HB.
  split.
  - assert (HA' : length (LowerBound.deck_A c1) = length (LowerBound.deck_A c3) + 2).
    {
      symmetry.
      exact HA.
    }
    lia.
  - assert (HB' : length (LowerBound.deck_B c1) = length (LowerBound.deck_B c3) + 2).
    {
      symmetry.
      exact HB.
    }
    lia.
Qed.

Definition block := (nat * nat)%type.

Definition trace_of_block (b : block) : list LowerBound.outcome :=
  phase_block_trace (fst b) (snd b).

Fixpoint blocks_trace (bs : list block) : list LowerBound.outcome :=
  match bs with
  | [] => []
  | b :: bs' => trace_of_block b ++ blocks_trace bs'
  end.

Fixpoint blocks_duration (bs : list block) : nat :=
  match bs with
  | [] => 0
  | (p, q) :: bs' => (p + q + 1) + blocks_duration bs'
  end.

Inductive runs_blocks (phi : nat -> nat -> LowerBound.outcome)
  : LowerBound.config -> list block -> LowerBound.config -> Prop :=
| RunsBlocksNil : forall c,
    runs_blocks phi c [] c
| RunsBlocksCons : forall c1 c2 c3 p q bs,
    LowerBound.runs phi c1 (phase_block_trace p q) c2 ->
    runs_blocks phi c2 bs c3 ->
    runs_blocks phi c1 ((p, q) :: bs) c3.

Lemma blocks_trace_duration :
  forall bs,
    LowerBound.duration (blocks_trace bs) = blocks_duration bs.
Proof.
  induction bs as [|(p, q) bs IH].
  - reflexivity.
  - simpl.
    unfold trace_of_block.
    unfold LowerBound.duration in *.
    rewrite length_app.
    rewrite phase_block_trace_duration.
    simpl.
    rewrite IH.
    lia.
Qed.

Lemma blocks_trace_tie_count :
  forall bs,
    LowerBound.tie_count (blocks_trace bs) = length bs.
Proof.
  induction bs as [|(p, q) bs IH].
  - reflexivity.
  - simpl.
    unfold LowerBound.tie_count in *.
    rewrite count_occ_app.
    replace (count_occ LowerBound.outcome_eq_dec (trace_of_block (p, q)) LowerBound.TT) with 1.
    2:{
      unfold trace_of_block.
      simpl.
      unfold LowerBound.tie_count.
      symmetry.
      apply phase_block_trace_tie_count.
    }
    rewrite IH.
    simpl.
    reflexivity.
Qed.

Lemma runs_blocks_to_runs :
  forall phi c1 bs c2,
    runs_blocks phi c1 bs c2 ->
    LowerBound.runs phi c1 (blocks_trace bs) c2.
Proof.
  intros phi c1 bs c2 Hrb.
  induction Hrb as [c|c1 c2 c3 p q bs Hr_block Hrbs IH].
  - simpl.
    apply LowerBound.RunsNil.
  - simpl.
    apply (runs_app phi c1 (phase_block_trace p q) c2 (blocks_trace bs) c3);
      assumption.
Qed.

Theorem runs_blocks_accounting :
  forall phi c1 bs c2,
    runs_blocks phi c1 bs c2 ->
    LowerBound.duration (blocks_trace bs) = blocks_duration bs /\
    LowerBound.tie_count (blocks_trace bs) = length bs /\
    length (LowerBound.deck_A c2) = length (LowerBound.deck_A c1) - length bs /\
    length (LowerBound.deck_B c2) = length (LowerBound.deck_B c1) - length bs.
Proof.
  intros phi c1 bs c2 Hrb.
  split.
  - apply blocks_trace_duration.
  - split.
    + apply blocks_trace_tie_count.
    + pose proof (runs_blocks_to_runs phi c1 bs c2 Hrb) as Hr.
      pose proof (LowerBound.runs_length_tie_accounting phi c1 (blocks_trace bs) c2 Hr)
        as [HA HB].
      rewrite blocks_trace_tie_count in HA.
      rewrite blocks_trace_tie_count in HB.
      split; lia.
Qed.

Fixpoint blocks_of_n (n : nat) : list block :=
  match n with
  | 0 => []
  | S k => (LowerBound.phase_term (S k) - 1, 0) :: blocks_of_n k
  end.

Lemma blocks_of_n_length :
  forall n,
    length (blocks_of_n n) = n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma blocks_of_n_duration :
  forall n,
    blocks_duration (blocks_of_n n) = LowerBound.T n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    assert (Hpt : LowerBound.phase_term (S n) >= 1).
    {
      apply LowerBound.phase_term_ge_one.
      lia.
    }
    lia.
Qed.

Lemma blocks_of_n_trace_duration :
  forall n,
    LowerBound.duration (blocks_trace (blocks_of_n n)) = LowerBound.T n.
Proof.
  intro n.
  rewrite blocks_trace_duration.
  apply blocks_of_n_duration.
Qed.

Definition lower_bound_blocks_obligation (n : nat) : Prop :=
  exists (phi : nat -> nat -> LowerBound.outcome)
         (start final : LowerBound.config),
    length (LowerBound.deck_A start) = n /\
    length (LowerBound.deck_B start) = n /\
    runs_blocks phi start (blocks_of_n n) final /\
    LowerBound.deck_A final = [] /\
    LowerBound.deck_B final = [].

Theorem lower_bound_solution_from_blocks_obligation :
  forall n,
    lower_bound_blocks_obligation n ->
    LowerBound.lower_bound_solution n.
Proof.
  intros n Hob.
  destruct Hob as [phi [start [final [HA [HB [Hrb [HfA HfB]]]]]]].
  destruct final as [fa fb].
  simpl in HfA, HfB.
  subst fa fb.
  exists phi, start, (blocks_trace (blocks_of_n n)).
  repeat split.
  - exact HA.
  - exact HB.
  - unfold LowerBound.game.
    exact (runs_blocks_to_runs phi start (blocks_of_n n)
             {| LowerBound.deck_A := []; LowerBound.deck_B := [] |} Hrb).
  - apply blocks_of_n_trace_duration.
Qed.

Lemma blocks_of_n_2_trace :
  blocks_trace (blocks_of_n 2) =
  [LowerBound.WA; LowerBound.WA; LowerBound.TT; LowerBound.TT].
Proof.
  reflexivity.
Qed.

Lemma lower_bound_blocks_obligation_2_false :
  ~ lower_bound_blocks_obligation 2.
Proof.
  intro Hob.
  destruct Hob as [phi [start [final [HA [HB [Hrb _]]]]]].
  destruct start as [da db].
  simpl in HA, HB.
  destruct da as [|a0 da']; simpl in HA; try lia.
  destruct da' as [|a1 da'']; simpl in HA; try lia.
  destruct da''; simpl in HA; try lia.
  destruct db as [|b0 db']; simpl in HB; try lia.
  destruct db' as [|b1 db'']; simpl in HB; try lia.
  destruct db''; simpl in HB; try lia.
  pose proof (runs_blocks_to_runs phi
                {| LowerBound.deck_A := [a0; a1]; LowerBound.deck_B := [b0; b1] |}
                (blocks_of_n 2) final Hrb) as Hr.
  rewrite blocks_of_n_2_trace in Hr.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [a0; a1]; LowerBound.deck_B := [b0; b1] |}
              LowerBound.WA [LowerBound.WA; LowerBound.TT; LowerBound.TT] final Hr)
    as [c1 [Hs1 Hr1]].
  inversion Hs1; subst.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [a0; a1]; LowerBound.deck_B := [b1; b0] |}
              LowerBound.WA [LowerBound.TT; LowerBound.TT] final Hr1)
    as [c2 [Hs2 Hr2]].
  inversion Hs2; subst.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [a0; a1]; LowerBound.deck_B := [b0; b1] |}
              LowerBound.TT [LowerBound.TT] final Hr2)
    as [c3 [Hs3 _]].
  inversion Hs3; subst.
  congruence.
Qed.

Inductive block_mode := ModeWA_NN | ModeNN_WA.

Definition block_flex := (block_mode * nat * nat)%type.

Definition trace_of_flex_block (b : block_flex) : list LowerBound.outcome :=
  match b with
  | (ModeWA_NN, p, q) => repeat LowerBound.WA p ++ repeat LowerBound.NN q ++ [LowerBound.TT]
  | (ModeNN_WA, p, q) => repeat LowerBound.NN q ++ repeat LowerBound.WA p ++ [LowerBound.TT]
  end.

Fixpoint flex_blocks_trace (bs : list block_flex) : list LowerBound.outcome :=
  match bs with
  | [] => []
  | b :: bs' => trace_of_flex_block b ++ flex_blocks_trace bs'
  end.

Inductive runs_flex_blocks (phi : nat -> nat -> LowerBound.outcome)
  : LowerBound.config -> list block_flex -> LowerBound.config -> Prop :=
| RunsFlexBlocksNil : forall c,
    runs_flex_blocks phi c [] c
| RunsFlexBlocksCons : forall c1 c2 c3 b bs,
    LowerBound.runs phi c1 (trace_of_flex_block b) c2 ->
    runs_flex_blocks phi c2 bs c3 ->
    runs_flex_blocks phi c1 (b :: bs) c3.

Lemma runs_flex_blocks_to_runs :
  forall phi c1 bs c2,
    runs_flex_blocks phi c1 bs c2 ->
    LowerBound.runs phi c1 (flex_blocks_trace bs) c2.
Proof.
  intros phi c1 bs c2 Hrb.
  induction Hrb as [c|c1 c2 c3 b bs Hr_block Hrbs IH].
  - simpl. apply LowerBound.RunsNil.
  - simpl.
    apply (runs_app phi c1 (trace_of_flex_block b) c2 (flex_blocks_trace bs) c3);
      assumption.
Qed.

Definition flex_blocks_of_2 : list block_flex :=
  [(ModeNN_WA, 1, 1); (ModeWA_NN, 0, 0)].

Lemma flex_blocks_of_2_trace :
  flex_blocks_trace flex_blocks_of_2 =
  [LowerBound.NN; LowerBound.WA; LowerBound.TT; LowerBound.TT].
Proof.
  reflexivity.
Qed.

Lemma runs_flex_blocks_2_witness :
  exists start final,
    length (LowerBound.deck_A start) = 2 /\
    length (LowerBound.deck_B start) = 2 /\
    runs_flex_blocks LowerBound.phi2 start flex_blocks_of_2 final /\
    LowerBound.deck_A final = [] /\
    LowerBound.deck_B final = [].
Proof.
  exists {| LowerBound.deck_A := [0;1]; LowerBound.deck_B := [0;1] |}.
  exists {| LowerBound.deck_A := []; LowerBound.deck_B := [] |}.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * eapply RunsFlexBlocksCons.
        -- unfold trace_of_flex_block.
           simpl.
           eapply LowerBound.RunsCons.
           ++ apply (LowerBound.StepNN LowerBound.phi2 0 [1] 0 [1]). reflexivity.
           ++ eapply LowerBound.RunsCons.
              ** apply (LowerBound.StepWA LowerBound.phi2 1 [0] 1 [0]). reflexivity.
              ** eapply LowerBound.RunsCons.
                 --- apply (LowerBound.StepTT LowerBound.phi2 1 [0] 0 [1]). reflexivity.
                 --- apply LowerBound.RunsNil.
        -- eapply RunsFlexBlocksCons.
           ++ unfold trace_of_flex_block.
              simpl.
              eapply LowerBound.RunsCons.
              ** apply (LowerBound.StepTT LowerBound.phi2 0 [] 1 []). reflexivity.
              ** apply LowerBound.RunsNil.
           ++ apply RunsFlexBlocksNil.
      * split; reflexivity.
Qed.

Fixpoint flex_blocks_duration (bs : list block_flex) : nat :=
  match bs with
  | [] => 0
  | (_, p, q) :: bs' => (p + q + 1) + flex_blocks_duration bs'
  end.

Lemma trace_of_flex_block_duration :
  forall m p q,
    LowerBound.duration (trace_of_flex_block (m, p, q)) = p + q + 1.
Proof.
  intros m p q.
  destruct m.
  - unfold trace_of_flex_block, LowerBound.duration.
    simpl.
    rewrite !length_app, !repeat_length.
    simpl.
    lia.
  - unfold trace_of_flex_block, LowerBound.duration.
    simpl.
    rewrite !length_app, !repeat_length.
    simpl.
    lia.
Qed.

Lemma trace_of_flex_block_tie_count :
  forall m p q,
    LowerBound.tie_count (trace_of_flex_block (m, p, q)) = 1.
Proof.
  intros m p q.
  destruct m.
  - unfold trace_of_flex_block, LowerBound.tie_count.
    simpl.
    rewrite !count_occ_app.
    rewrite count_occ_repeat_neq by discriminate.
    rewrite count_occ_repeat_neq by discriminate.
    simpl.
    lia.
  - unfold trace_of_flex_block, LowerBound.tie_count.
    simpl.
    rewrite !count_occ_app.
    rewrite count_occ_repeat_neq by discriminate.
    rewrite count_occ_repeat_neq by discriminate.
    simpl.
    lia.
Qed.

Lemma flex_blocks_trace_duration :
  forall bs,
    LowerBound.duration (flex_blocks_trace bs) = flex_blocks_duration bs.
Proof.
  induction bs as [|((m, p), q) bs IH].
  - reflexivity.
  - simpl.
    unfold LowerBound.duration in *.
    rewrite length_app.
    destruct m.
    + simpl.
      rewrite !length_app, !repeat_length.
      simpl.
      rewrite IH.
      lia.
    + simpl.
      rewrite !length_app, !repeat_length.
      simpl.
      rewrite IH.
      lia.
Qed.

Lemma flex_blocks_trace_tie_count :
  forall bs,
    LowerBound.tie_count (flex_blocks_trace bs) = length bs.
Proof.
  induction bs as [|((m, p), q) bs IH].
  - reflexivity.
  - simpl.
    unfold LowerBound.tie_count in *.
    rewrite count_occ_app.
    destruct m.
    + simpl.
      rewrite !count_occ_app.
      rewrite count_occ_repeat_neq by discriminate.
      rewrite count_occ_repeat_neq by discriminate.
      simpl.
      rewrite IH.
      lia.
    + simpl.
      rewrite !count_occ_app.
      rewrite count_occ_repeat_neq by discriminate.
      rewrite count_occ_repeat_neq by discriminate.
      simpl.
      rewrite IH.
      lia.
Qed.

Theorem runs_flex_blocks_accounting :
  forall phi c1 bs c2,
    runs_flex_blocks phi c1 bs c2 ->
    LowerBound.duration (flex_blocks_trace bs) = flex_blocks_duration bs /\
    LowerBound.tie_count (flex_blocks_trace bs) = length bs /\
    length (LowerBound.deck_A c2) = length (LowerBound.deck_A c1) - length bs /\
    length (LowerBound.deck_B c2) = length (LowerBound.deck_B c1) - length bs.
Proof.
  intros phi c1 bs c2 Hrb.
  split.
  - apply flex_blocks_trace_duration.
  - split.
    + apply flex_blocks_trace_tie_count.
    + pose proof (runs_flex_blocks_to_runs phi c1 bs c2 Hrb) as Hr.
      pose proof (LowerBound.runs_length_tie_accounting phi c1 (flex_blocks_trace bs) c2 Hr)
        as [HA HB].
      rewrite flex_blocks_trace_tie_count in HA.
      rewrite flex_blocks_trace_tie_count in HB.
      split; lia.
Qed.

Definition lower_bound_flex_blocks_obligation (n : nat) : Prop :=
  exists (phi : nat -> nat -> LowerBound.outcome)
         (start final : LowerBound.config)
         (bs : list block_flex),
    length (LowerBound.deck_A start) = n /\
    length (LowerBound.deck_B start) = n /\
    length bs = n /\
    flex_blocks_duration bs = LowerBound.T n /\
    runs_flex_blocks phi start bs final /\
    LowerBound.deck_A final = [] /\
    LowerBound.deck_B final = [].

Theorem lower_bound_solution_from_flex_blocks_obligation :
  forall n,
    lower_bound_flex_blocks_obligation n ->
    LowerBound.lower_bound_solution n.
Proof.
  intros n Hob.
  destruct Hob as [phi [start [final [bs [HA [HB [_ [Hdur [Hrb [HfA HfB]]]]]]]]]].
  destruct final as [fa fb].
  simpl in HfA, HfB.
  subst fa fb.
  exists phi, start, (flex_blocks_trace bs).
  repeat split.
  - exact HA.
  - exact HB.
  - unfold LowerBound.game.
    exact (runs_flex_blocks_to_runs phi start bs
             {| LowerBound.deck_A := []; LowerBound.deck_B := [] |} Hrb).
  - rewrite flex_blocks_trace_duration.
    exact Hdur.
Qed.

Definition flex_block_of_size (m : nat) : block_flex :=
  match m with
  | 0 => (ModeWA_NN, 0, 0)
  | 1 => (ModeWA_NN, 0, 0)
  | S (S _) => (ModeNN_WA, 1, LowerBound.phase_term m - 2)
  end.

Fixpoint flex_blocks_of_n (n : nat) : list block_flex :=
  match n with
  | 0 => []
  | S k => flex_block_of_size (S k) :: flex_blocks_of_n k
  end.

Lemma flex_block_of_size_duration :
  forall m,
    LowerBound.duration (trace_of_flex_block (flex_block_of_size m)) = LowerBound.phase_term m.
Proof.
  intro m.
  destruct m as [|[|k]].
  - unfold flex_block_of_size, LowerBound.phase_term.
    simpl.
    reflexivity.
  - unfold flex_block_of_size, LowerBound.phase_term.
    simpl.
    reflexivity.
  - unfold flex_block_of_size.
    rewrite trace_of_flex_block_duration.
    unfold LowerBound.phase_term.
    simpl.
    lia.
Qed.

Lemma flex_blocks_duration_cons_size :
  forall m bs,
    flex_blocks_duration (flex_block_of_size m :: bs) =
    LowerBound.phase_term m + flex_blocks_duration bs.
Proof.
  intros m bs.
  destruct m as [|[|k]].
  - unfold flex_block_of_size, flex_blocks_duration, LowerBound.phase_term.
    simpl.
    lia.
  - unfold flex_block_of_size, flex_blocks_duration, LowerBound.phase_term.
    simpl.
    lia.
  - unfold flex_block_of_size, flex_blocks_duration.
    simpl.
    unfold LowerBound.phase_term.
    simpl.
    lia.
Qed.

Lemma flex_blocks_of_n_length :
  forall n,
    length (flex_blocks_of_n n) = n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma flex_blocks_of_n_duration :
  forall n,
    flex_blocks_duration (flex_blocks_of_n n) = LowerBound.T n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - change (flex_blocks_duration (flex_block_of_size (S n) :: flex_blocks_of_n n) = LowerBound.T (S n)).
    rewrite flex_blocks_duration_cons_size.
    simpl.
    rewrite IH.
    lia.
Qed.

Lemma flex_blocks_of_n_2_eq :
  flex_blocks_of_n 2 = flex_blocks_of_2.
Proof.
  reflexivity.
Qed.

Lemma lower_bound_flex_blocks_obligation_2 :
  lower_bound_flex_blocks_obligation 2.
Proof.
  destruct runs_flex_blocks_2_witness as [start [final [HA [HB [Hrb [HfA HfB]]]]]].
  exists LowerBound.phi2, start, final, flex_blocks_of_2.
  split.
  - exact HA.
  - split.
    + exact HB.
    + split.
      * reflexivity.
      * split.
        -- rewrite <- flex_blocks_of_n_2_eq.
           rewrite flex_blocks_of_n_duration.
           reflexivity.
        -- split.
           ++ exact Hrb.
           ++ split; assumption.
Qed.

Lemma lower_bound_solution_2_via_flex_blocks :
  LowerBound.lower_bound_solution 2.
Proof.
  apply lower_bound_solution_from_flex_blocks_obligation.
  exact lower_bound_flex_blocks_obligation_2.
Qed.

Definition phi_tt (_ _ : nat) : LowerBound.outcome := LowerBound.TT.

Definition candidate_flex_blocks_obligation (n : nat) : Prop :=
  exists (phi : nat -> nat -> LowerBound.outcome)
         (start final : LowerBound.config),
    length (LowerBound.deck_A start) = n /\
    length (LowerBound.deck_B start) = n /\
    runs_flex_blocks phi start (flex_blocks_of_n n) final /\
    LowerBound.deck_A final = [] /\
    LowerBound.deck_B final = [].

Lemma lower_bound_flex_obligation_from_candidate :
  forall n,
    candidate_flex_blocks_obligation n ->
    lower_bound_flex_blocks_obligation n.
Proof.
  intros n Hcand.
  destruct Hcand as [phi [start [final [HA [HB [Hrb [HfA HfB]]]]]]].
  exists phi, start, final, (flex_blocks_of_n n).
  split.
  - exact HA.
  - split.
    + exact HB.
    + split.
      * apply flex_blocks_of_n_length.
      * split.
        -- apply flex_blocks_of_n_duration.
        -- split.
           ++ exact Hrb.
           ++ split; assumption.
Qed.

Lemma candidate_flex_blocks_obligation_0 :
  candidate_flex_blocks_obligation 0.
Proof.
  exists phi_tt,
    {| LowerBound.deck_A := []; LowerBound.deck_B := [] |},
    {| LowerBound.deck_A := []; LowerBound.deck_B := [] |}.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * simpl.
        apply RunsFlexBlocksNil.
      * split; reflexivity.
Qed.

Lemma candidate_flex_blocks_obligation_1 :
  candidate_flex_blocks_obligation 1.
Proof.
  exists phi_tt,
    {| LowerBound.deck_A := [0]; LowerBound.deck_B := [0] |},
    {| LowerBound.deck_A := []; LowerBound.deck_B := [] |}.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * change (runs_flex_blocks phi_tt
                 {| LowerBound.deck_A := [0]; LowerBound.deck_B := [0] |}
                 [flex_block_of_size 1]
                 {| LowerBound.deck_A := []; LowerBound.deck_B := [] |}).
        eapply RunsFlexBlocksCons.
        -- unfold trace_of_flex_block, flex_block_of_size.
           simpl.
           eapply LowerBound.RunsCons.
           ++ apply (LowerBound.StepTT phi_tt 0 [] 0 []). reflexivity.
           ++ apply LowerBound.RunsNil.
        -- apply RunsFlexBlocksNil.
      * split; reflexivity.
Qed.

Lemma candidate_flex_blocks_obligation_2 :
  candidate_flex_blocks_obligation 2.
Proof.
  destruct runs_flex_blocks_2_witness as [start [final [HA [HB [Hrb [HfA HfB]]]]]].
  exists LowerBound.phi2, start, final.
  split.
  - exact HA.
  - split.
    + exact HB.
    + split.
      * rewrite flex_blocks_of_n_2_eq.
        exact Hrb.
      * split; assumption.
Qed.

Theorem lower_bound_solution_upto_2_via_candidate :
  forall n,
    n > 0 ->
    n <= 2 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros n Hpos Hle2.
  destruct n as [|n']; [lia|].
  destruct n' as [|n''].
  - apply lower_bound_solution_from_flex_blocks_obligation.
    apply lower_bound_flex_obligation_from_candidate.
    exact candidate_flex_blocks_obligation_1.
  - assert (n'' = 0) by lia.
    subst n''.
    apply lower_bound_solution_from_flex_blocks_obligation.
    apply lower_bound_flex_obligation_from_candidate.
    exact candidate_flex_blocks_obligation_2.
Qed.

Definition phase_extension_adaptive_step_ge2 : Prop :=
  forall n phi mid final bs,
    n >= 2 ->
    length (LowerBound.deck_A mid) = n ->
    length (LowerBound.deck_B mid) = n ->
    length bs = n ->
    flex_blocks_duration bs = LowerBound.T n ->
    runs_flex_blocks phi mid bs final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    exists b start,
      flex_blocks_duration [b] = LowerBound.phase_term (S n) /\
      length (LowerBound.deck_A start) = S n /\
      length (LowerBound.deck_B start) = S n /\
      LowerBound.runs phi start (trace_of_flex_block b) mid.

Definition adaptive_tail_reachable
  (n : nat) (phi : nat -> nat -> LowerBound.outcome) (mid : LowerBound.config) : Prop :=
  exists final bs,
    length bs = n /\
    flex_blocks_duration bs = LowerBound.T n /\
    runs_flex_blocks phi mid bs final /\
    LowerBound.deck_A final = [] /\
    LowerBound.deck_B final = [].

Definition phase_extension_adaptive_step_ge2_on_tail_reachable : Prop :=
  forall n phi mid,
    n >= 2 ->
    length (LowerBound.deck_A mid) = n ->
    length (LowerBound.deck_B mid) = n ->
    adaptive_tail_reachable n phi mid ->
    exists b start,
      flex_blocks_duration [b] = LowerBound.phase_term (S n) /\
      length (LowerBound.deck_A start) = S n /\
      length (LowerBound.deck_B start) = S n /\
      LowerBound.runs phi start (trace_of_flex_block b) mid.

Definition adaptive_step_at_tail_reachable (n : nat) : Prop :=
  forall phi mid,
    length (LowerBound.deck_A mid) = n ->
    length (LowerBound.deck_B mid) = n ->
    adaptive_tail_reachable n phi mid ->
    exists b start,
      flex_blocks_duration [b] = LowerBound.phase_term (S n) /\
      length (LowerBound.deck_A start) = S n /\
      length (LowerBound.deck_B start) = S n /\
      LowerBound.runs phi start (trace_of_flex_block b) mid.

Definition adaptive_step_ge2_tail_reachable_step : Prop :=
  forall n,
    n >= 2 ->
    adaptive_step_at_tail_reachable n ->
    adaptive_step_at_tail_reachable (S n).

Theorem phase_extension_adaptive_step_ge2_on_tail_reachable_from_base_step :
  adaptive_step_at_tail_reachable 2 ->
  adaptive_step_ge2_tail_reachable_step ->
  phase_extension_adaptive_step_ge2_on_tail_reachable.
Proof.
  intros Hbase2 Hstep n phi mid Hn HAm HBm Hreach.
  assert (Hall : forall m, m >= 2 -> adaptive_step_at_tail_reachable m).
  {
    intros m Hm.
    assert (Hex : exists k, m = 2 + k) by (exists (m - 2); lia).
    destruct Hex as [k Hk].
    subst m.
    induction k as [|k IH].
    - replace (2 + 0) with 2 by lia.
      exact Hbase2.
    - replace (2 + S k) with (S (2 + k)) by lia.
      apply Hstep.
      + lia.
      + apply IH.
        lia.
  }
  exact (Hall n Hn phi mid HAm HBm Hreach).
Qed.

Lemma phase_extension_adaptive_step_ge2_from_tail_reachable :
  phase_extension_adaptive_step_ge2_on_tail_reachable ->
  phase_extension_adaptive_step_ge2.
Proof.
  intros Htail n phi mid final bs Hn HAm HBm Hlen Hdur Hr HfA HfB.
  apply (Htail n phi mid Hn HAm HBm).
  exists final, bs.
  repeat split; assumption.
Qed.

Lemma phase_extension_adaptive_step_ge2_to_tail_reachable :
  phase_extension_adaptive_step_ge2 ->
  phase_extension_adaptive_step_ge2_on_tail_reachable.
Proof.
  intros Hstep n phi mid Hn HAm HBm Hreach.
  destruct Hreach as [final [bs [Hlen [Hdur [Hr [HfA HfB]]]]]].
  exact (Hstep n phi mid final bs Hn HAm HBm Hlen Hdur Hr HfA HfB).
Qed.

Lemma lower_bound_flex_blocks_step_ge2_from_adaptive :
  phase_extension_adaptive_step_ge2 ->
  forall n,
    n >= 2 ->
    lower_bound_flex_blocks_obligation n ->
    lower_bound_flex_blocks_obligation (S n).
Proof.
  intros Hstep n Hn Hob.
  destruct Hob as [phi [mid [final [bs [HAm [HBm [Hlen [Hdur [Hr [HfA HfB]]]]]]]]]].
  destruct (Hstep n phi mid final bs Hn HAm HBm Hlen Hdur Hr HfA HfB)
    as [b [start [Hbdur [HAs [HBs Hr_head]]]]].
  exists phi, start, final, (b :: bs).
  split.
  - exact HAs.
  - split.
    + exact HBs.
    + split.
      * simpl.
        rewrite Hlen.
        reflexivity.
      * split.
        -- destruct b as [[m p] q].
          simpl in Hbdur.
          simpl.
          rewrite Hdur.
          lia.
        -- split.
           ++ eapply RunsFlexBlocksCons.
              ** exact Hr_head.
              ** exact Hr.
           ++ split; assumption.
Qed.

Section AdaptiveGe2Reduction.

Hypothesis Hstep_adaptive_ge2 : phase_extension_adaptive_step_ge2.

Lemma lower_bound_flex_blocks_obligation_from_2_onward_adaptive :
  forall k,
    lower_bound_flex_blocks_obligation (k + 2).
Proof.
  intro k.
  induction k as [|k IH].
  - simpl.
    apply lower_bound_flex_obligation_from_candidate.
    exact candidate_flex_blocks_obligation_2.
  - replace (S k + 2) with (S (k + 2)) by lia.
    eapply lower_bound_flex_blocks_step_ge2_from_adaptive.
    + exact Hstep_adaptive_ge2.
    + lia.
    + exact IH.
Qed.

Theorem lower_bound_flex_blocks_obligation_all_adaptive :
  forall n,
    lower_bound_flex_blocks_obligation n.
Proof.
  intro n.
  destruct n as [|n'].
  - apply lower_bound_flex_obligation_from_candidate.
    exact candidate_flex_blocks_obligation_0.
  - destruct n' as [|n''].
    + apply lower_bound_flex_obligation_from_candidate.
      exact candidate_flex_blocks_obligation_1.
    + replace (S (S n'')) with (n'' + 2) by lia.
      apply lower_bound_flex_blocks_obligation_from_2_onward_adaptive.
Qed.

Theorem lower_bound_solution_all_via_adaptive_ge2_step :
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros n Hn.
  apply lower_bound_solution_from_flex_blocks_obligation.
  apply lower_bound_flex_blocks_obligation_all_adaptive.
Qed.

End AdaptiveGe2Reduction.

Theorem lower_bound_solution_all_via_adaptive_ge2_tail_reachable_step :
  phase_extension_adaptive_step_ge2_on_tail_reachable ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Htail n Hn.
  apply (lower_bound_solution_all_via_adaptive_ge2_step
           (phase_extension_adaptive_step_ge2_from_tail_reachable Htail)
           n Hn).
Qed.

Theorem lower_bound_solution_all_via_adaptive_ge2_base_step :
  adaptive_step_at_tail_reachable 2 ->
  adaptive_step_ge2_tail_reachable_step ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Hbase2 Hstep n Hn.
  apply lower_bound_solution_all_via_adaptive_ge2_tail_reachable_step.
  apply phase_extension_adaptive_step_ge2_on_tail_reachable_from_base_step.
  - exact Hbase2.
  - exact Hstep.
  - exact Hn.
Qed.

Lemma config_deck_A_nil_of_length_zero :
  forall c,
    length (LowerBound.deck_A c) = 0 ->
    LowerBound.deck_A c = [].
Proof.
  intros c Hlen.
  destruct c as [da db].
  simpl in Hlen.
  destruct da; simpl in Hlen; [reflexivity|lia].
Qed.

Lemma config_deck_B_nil_of_length_zero :
  forall c,
    length (LowerBound.deck_B c) = 0 ->
    LowerBound.deck_B c = [].
Proof.
  intros c Hlen.
  destruct c as [da db].
  simpl in Hlen.
  destruct db; simpl in Hlen; [reflexivity|lia].
Qed.

Lemma one_phase_run_size1 :
  forall phi a b,
    phi a b = LowerBound.TT ->
    LowerBound.runs phi
      {| LowerBound.deck_A := [a]; LowerBound.deck_B := [b] |}
      (trace_of_flex_block (flex_block_of_size 1))
      {| LowerBound.deck_A := []; LowerBound.deck_B := [] |}.
Proof.
  intros phi a b Htt.
  unfold trace_of_flex_block, flex_block_of_size.
  simpl.
  eapply LowerBound.RunsCons.
  - apply (LowerBound.StepTT phi a [] b []). exact Htt.
  - apply LowerBound.RunsNil.
Qed.

Lemma one_phase_run_size2_pattern :
  forall phi u x v y,
    phi u v = LowerBound.NN ->
    phi x y = LowerBound.WA ->
    phi x v = LowerBound.TT ->
    LowerBound.runs phi
      {| LowerBound.deck_A := [u; x]; LowerBound.deck_B := [v; y] |}
      (trace_of_flex_block (flex_block_of_size 2))
      {| LowerBound.deck_A := [u]; LowerBound.deck_B := [y] |}.
Proof.
  intros phi u x v y Hnn Hwa Htt.
  unfold trace_of_flex_block, flex_block_of_size.
  simpl.
  eapply LowerBound.RunsCons.
  - apply (LowerBound.StepNN phi u [x] v [y]). exact Hnn.
  - eapply LowerBound.RunsCons.
    + apply (LowerBound.StepWA phi x [u] y [v]). exact Hwa.
    + eapply LowerBound.RunsCons.
      * apply (LowerBound.StepTT phi x [u] v [y]). exact Htt.
      * apply LowerBound.RunsNil.
Qed.

Lemma phase_extension_base_n0_if_tt :
  forall phi mid a b,
    length (LowerBound.deck_A mid) = 0 ->
    length (LowerBound.deck_B mid) = 0 ->
    phi a b = LowerBound.TT ->
    exists start,
      length (LowerBound.deck_A start) = 1 /\
      length (LowerBound.deck_B start) = 1 /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size 1)) mid.
Proof.
  intros phi mid a b HAm HBm Htt.
  assert (HmidA : LowerBound.deck_A mid = []).
  {
    apply config_deck_A_nil_of_length_zero.
    exact HAm.
  }
  assert (HmidB : LowerBound.deck_B mid = []).
  {
    apply config_deck_B_nil_of_length_zero.
    exact HBm.
  }
  destruct mid as [ma mb].
  simpl in HmidA, HmidB.
  subst ma mb.
  exists {| LowerBound.deck_A := [a]; LowerBound.deck_B := [b] |}.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + apply one_phase_run_size1.
      exact Htt.
Qed.

Lemma config_deck_A_singleton_of_length_one :
  forall c,
    length (LowerBound.deck_A c) = 1 ->
    exists a,
      LowerBound.deck_A c = [a].
Proof.
  intros c Hlen.
  destruct c as [da db].
  simpl in Hlen.
  destruct da as [|a da']; simpl in Hlen; [lia|].
  destruct da' as [|a2 da'']; simpl in Hlen; [|lia].
  exists a.
  reflexivity.
Qed.

Lemma config_deck_B_singleton_of_length_one :
  forall c,
    length (LowerBound.deck_B c) = 1 ->
    exists b,
      LowerBound.deck_B c = [b].
Proof.
  intros c Hlen.
  destruct c as [da db].
  simpl in Hlen.
  destruct db as [|b db']; simpl in Hlen; [lia|].
  destruct db' as [|b2 db'']; simpl in Hlen; [|lia].
  exists b.
  reflexivity.
Qed.

Lemma phase_extension_base_n1_if_pattern :
  forall phi mid u y x v,
    length (LowerBound.deck_A mid) = 1 ->
    length (LowerBound.deck_B mid) = 1 ->
    phi u v = LowerBound.NN ->
    phi x y = LowerBound.WA ->
    phi x v = LowerBound.TT ->
    LowerBound.deck_A mid = [u] ->
    LowerBound.deck_B mid = [y] ->
    exists start,
      length (LowerBound.deck_A start) = 2 /\
      length (LowerBound.deck_B start) = 2 /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size 2)) mid.
Proof.
  intros phi mid u y x v HAm HBm Hnn Hwa Htt HmidA HmidB.
  destruct mid as [ma mb].
  simpl in HAm, HBm, HmidA, HmidB.
  subst ma mb.
  exists {| LowerBound.deck_A := [u; x]; LowerBound.deck_B := [v; y] |}.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + apply one_phase_run_size2_pattern; assumption.
Qed.

Lemma phase_extension_base_n1_exists_if_pattern :
  forall phi mid x v,
    length (LowerBound.deck_A mid) = 1 ->
    length (LowerBound.deck_B mid) = 1 ->
    (forall u y,
       LowerBound.deck_A mid = [u] ->
       LowerBound.deck_B mid = [y] ->
       phi u v = LowerBound.NN /\
       phi x y = LowerBound.WA /\
       phi x v = LowerBound.TT) ->
    exists start,
      length (LowerBound.deck_A start) = 2 /\
      length (LowerBound.deck_B start) = 2 /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size 2)) mid.
Proof.
  intros phi mid x v HAm HBm Hpat.
  destruct (config_deck_A_singleton_of_length_one mid HAm) as [u Hu].
  destruct (config_deck_B_singleton_of_length_one mid HBm) as [y Hy].
  destruct (Hpat u y Hu Hy) as [Hnn [Hwa Htt]].
  eapply phase_extension_base_n1_if_pattern; eauto.
Qed.

Lemma candidate_obligation_from_head_tail :
  forall n phi start mid final,
    length (LowerBound.deck_A start) = S n ->
    length (LowerBound.deck_B start) = S n ->
    LowerBound.runs phi start
      (trace_of_flex_block (flex_block_of_size (S n))) mid ->
    runs_flex_blocks phi mid (flex_blocks_of_n n) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    candidate_flex_blocks_obligation (S n).
Proof.
  intros n phi start mid final HAs HBs Hr_head Hr_tail HfA HfB.
  exists phi, start, final.
  split.
  - exact HAs.
  - split.
    + exact HBs.
    + split.
      * change (runs_flex_blocks phi start
                  (flex_block_of_size (S n) :: flex_blocks_of_n n)
                  final).
        eapply RunsFlexBlocksCons.
        -- exact Hr_head.
        -- exact Hr_tail.
      * split; assumption.
Qed.

Lemma candidate_step_n0_if_tt :
  forall phi mid final a b,
    length (LowerBound.deck_A mid) = 0 ->
    length (LowerBound.deck_B mid) = 0 ->
    runs_flex_blocks phi mid (flex_blocks_of_n 0) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    phi a b = LowerBound.TT ->
    candidate_flex_blocks_obligation 1.
Proof.
  intros phi mid final a b HAm HBm Hr_tail HfA HfB Htt.
  destruct (phase_extension_base_n0_if_tt phi mid a b HAm HBm Htt)
    as [start [HAs [HBs Hr_head]]].
  eapply candidate_obligation_from_head_tail.
  - exact HAs.
  - exact HBs.
  - exact Hr_head.
  - exact Hr_tail.
  - exact HfA.
  - exact HfB.
Qed.

Lemma candidate_step_n1_if_pattern :
  forall phi mid final x v,
    length (LowerBound.deck_A mid) = 1 ->
    length (LowerBound.deck_B mid) = 1 ->
    runs_flex_blocks phi mid (flex_blocks_of_n 1) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    (forall u y,
       LowerBound.deck_A mid = [u] ->
       LowerBound.deck_B mid = [y] ->
       phi u v = LowerBound.NN /\
       phi x y = LowerBound.WA /\
       phi x v = LowerBound.TT) ->
    candidate_flex_blocks_obligation 2.
Proof.
  intros phi mid final x v HAm HBm Hr_tail HfA HfB Hpat.
  destruct (phase_extension_base_n1_exists_if_pattern phi mid x v HAm HBm Hpat)
    as [start [HAs [HBs Hr_head]]].
  eapply candidate_obligation_from_head_tail.
  - exact HAs.
  - exact HBs.
  - exact Hr_head.
  - exact Hr_tail.
  - exact HfA.
  - exact HfB.
Qed.

Definition phase_extension_obligation_split : Prop :=
  (forall phi mid final,
     length (LowerBound.deck_A mid) = 0 ->
     length (LowerBound.deck_B mid) = 0 ->
     runs_flex_blocks phi mid (flex_blocks_of_n 0) final ->
     LowerBound.deck_A final = [] ->
     LowerBound.deck_B final = [] ->
     exists a b,
       phi a b = LowerBound.TT)
  /\
  (forall n phi mid final,
     n > 0 ->
     length (LowerBound.deck_A mid) = n ->
     length (LowerBound.deck_B mid) = n ->
     runs_flex_blocks phi mid (flex_blocks_of_n n) final ->
     LowerBound.deck_A final = [] ->
     LowerBound.deck_B final = [] ->
     exists start,
       length (LowerBound.deck_A start) = S n /\
       length (LowerBound.deck_B start) = S n /\
       LowerBound.runs phi start
         (trace_of_flex_block (flex_block_of_size (S n))) mid).

Lemma phase_extension_obligation_from_split :
  phase_extension_obligation_split ->
  (forall n phi mid final,
     length (LowerBound.deck_A mid) = n ->
     length (LowerBound.deck_B mid) = n ->
     runs_flex_blocks phi mid (flex_blocks_of_n n) final ->
     LowerBound.deck_A final = [] ->
     LowerBound.deck_B final = [] ->
     exists start,
       length (LowerBound.deck_A start) = S n /\
       length (LowerBound.deck_B start) = S n /\
       LowerBound.runs phi start
         (trace_of_flex_block (flex_block_of_size (S n))) mid).
Proof.
  intros [Hzero Hpos] n phi mid final HAm HBm Hr_tail HfA HfB.
  destruct n as [|n'].
  - destruct (Hzero phi mid final HAm HBm Hr_tail HfA HfB) as [a [b Htt]].
    exact (phase_extension_base_n0_if_tt phi mid a b HAm HBm Htt).
  - apply (Hpos (S n') phi mid final).
    + lia.
    + exact HAm.
    + exact HBm.
    + exact Hr_tail.
    + exact HfA.
    + exact HfB.
Qed.

Section CandidateInduction.

Hypothesis candidate_flex_blocks_step :
  forall n,
    candidate_flex_blocks_obligation n ->
    candidate_flex_blocks_obligation (S n).

Theorem candidate_flex_blocks_obligation_all :
  forall n,
    candidate_flex_blocks_obligation n.
Proof.
  intro n.
  induction n as [|n IH].
  - exact candidate_flex_blocks_obligation_0.
  - apply candidate_flex_blocks_step.
    exact IH.
Qed.

Theorem lower_bound_solution_all_via_candidate_step :
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros n Hn.
  apply lower_bound_solution_from_flex_blocks_obligation.
  apply lower_bound_flex_obligation_from_candidate.
  apply candidate_flex_blocks_obligation_all.
Qed.

End CandidateInduction.

Section CandidateInductionFromGe2.

Hypothesis candidate_flex_blocks_step_ge2 :
  forall n,
    n >= 2 ->
    candidate_flex_blocks_obligation n ->
    candidate_flex_blocks_obligation (S n).

Lemma candidate_flex_blocks_obligation_from_2_onward :
  forall k,
    candidate_flex_blocks_obligation (k + 2).
Proof.
  intro k.
  induction k as [|k IH].
  - simpl.
    exact candidate_flex_blocks_obligation_2.
  - replace (S k + 2) with (S (k + 2)) by lia.
    apply candidate_flex_blocks_step_ge2.
    + lia.
    + exact IH.
Qed.

Theorem candidate_flex_blocks_obligation_all_from_ge2_step :
  forall n,
    candidate_flex_blocks_obligation n.
Proof.
  intro n.
  destruct n as [|n'].
  - exact candidate_flex_blocks_obligation_0.
  - destruct n' as [|n''].
    + exact candidate_flex_blocks_obligation_1.
    + replace (S (S n'')) with (n'' + 2) by lia.
      apply candidate_flex_blocks_obligation_from_2_onward.
Qed.

Theorem lower_bound_solution_all_via_candidate_step_ge2 :
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros n Hn.
  apply lower_bound_solution_from_flex_blocks_obligation.
  apply lower_bound_flex_obligation_from_candidate.
  apply candidate_flex_blocks_obligation_all_from_ge2_step.
Qed.

End CandidateInductionFromGe2.

Definition phase_extension_obligation : Prop :=
  forall n phi mid final,
    length (LowerBound.deck_A mid) = n ->
    length (LowerBound.deck_B mid) = n ->
    runs_flex_blocks phi mid (flex_blocks_of_n n) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    exists start,
      length (LowerBound.deck_A start) = S n /\
      length (LowerBound.deck_B start) = S n /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size (S n))) mid.

Lemma candidate_step_from_phase_extension :
  phase_extension_obligation ->
  forall n,
    candidate_flex_blocks_obligation n ->
    candidate_flex_blocks_obligation (S n).
Proof.
  intros Hext n Hcand.
  destruct Hcand as [phi [mid [final [HA [HB [Hrb [HfA HfB]]]]]]].
  destruct (Hext n phi mid final HA HB Hrb HfA HfB)
    as [start [HAs [HBs Hr_first]]].
  exists phi, start, final.
  split.
  - exact HAs.
  - split.
    + exact HBs.
    + split.
      * change (runs_flex_blocks phi start
                  (flex_block_of_size (S n) :: flex_blocks_of_n n)
                  final).
        eapply RunsFlexBlocksCons.
        -- exact Hr_first.
        -- exact Hrb.
      * split; assumption.
Qed.

Section PhaseExtensionReduction.

Hypothesis H_phase_extension : phase_extension_obligation.

Theorem lower_bound_solution_all_via_phase_extension :
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros n Hn.
  exact (lower_bound_solution_all_via_candidate_step
           (candidate_step_from_phase_extension H_phase_extension)
           n Hn).
Qed.

End PhaseExtensionReduction.

Section PhaseExtensionSplitReduction.

Hypothesis H_phase_extension_split : phase_extension_obligation_split.

Theorem lower_bound_solution_all_via_phase_extension_split :
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros n Hn.
  exact (lower_bound_solution_all_via_phase_extension
           (phase_extension_obligation_from_split H_phase_extension_split)
           n Hn).
Qed.

End PhaseExtensionSplitReduction.

Definition phase_extension_zero_case_witness : Prop :=
  forall phi mid final,
    length (LowerBound.deck_A mid) = 0 ->
    length (LowerBound.deck_B mid) = 0 ->
    runs_flex_blocks phi mid (flex_blocks_of_n 0) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    exists a b,
      phi a b = LowerBound.TT.

Definition phase_extension_pos_case_constructor : Prop :=
  forall n phi mid final,
    n > 0 ->
    length (LowerBound.deck_A mid) = n ->
    length (LowerBound.deck_B mid) = n ->
    runs_flex_blocks phi mid (flex_blocks_of_n n) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    exists start,
      length (LowerBound.deck_A start) = S n /\
      length (LowerBound.deck_B start) = S n /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size (S n))) mid.

Lemma phase_extension_zero_case_witness_if_exists_tt :
  forall phi,
    (exists a b, phi a b = LowerBound.TT) ->
    forall mid final,
      length (LowerBound.deck_A mid) = 0 ->
      length (LowerBound.deck_B mid) = 0 ->
      runs_flex_blocks phi mid (flex_blocks_of_n 0) final ->
      LowerBound.deck_A final = [] ->
      LowerBound.deck_B final = [] ->
      exists a b,
        phi a b = LowerBound.TT.
Proof.
  intros phi Htt mid final _ _ _ _ _.
  exact Htt.
Qed.

Lemma phase_extension_pos_case_n1_if_pattern :
  forall phi mid final x v,
    length (LowerBound.deck_A mid) = 1 ->
    length (LowerBound.deck_B mid) = 1 ->
    runs_flex_blocks phi mid (flex_blocks_of_n 1) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    (forall u y,
       LowerBound.deck_A mid = [u] ->
       LowerBound.deck_B mid = [y] ->
       phi u v = LowerBound.NN /\
       phi x y = LowerBound.WA /\
       phi x v = LowerBound.TT) ->
    exists start,
      length (LowerBound.deck_A start) = 2 /\
      length (LowerBound.deck_B start) = 2 /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size 2)) mid.
Proof.
  intros phi mid final x v HAm HBm _ _ _ Hpat.
  apply (phase_extension_base_n1_exists_if_pattern phi mid x v HAm HBm Hpat).
Qed.

Lemma phase_extension_split_from_explicit_assumptions :
  (forall (phi : nat -> nat -> LowerBound.outcome), exists a b, phi a b = LowerBound.TT) ->
  (forall n phi mid final,
     n > 0 ->
     length (LowerBound.deck_A mid) = n ->
     length (LowerBound.deck_B mid) = n ->
     runs_flex_blocks phi mid (flex_blocks_of_n n) final ->
     LowerBound.deck_A final = [] ->
     LowerBound.deck_B final = [] ->
     exists start,
       length (LowerBound.deck_A start) = S n /\
       length (LowerBound.deck_B start) = S n /\
       LowerBound.runs phi start
         (trace_of_flex_block (flex_block_of_size (S n))) mid) ->
  phase_extension_obligation_split.
Proof.
  intros Htt_all Hpos_all.
  split.
  - intros phi mid final HAm HBm Hr HfA HfB.
    exact (phase_extension_zero_case_witness_if_exists_tt
             phi (Htt_all phi) mid final HAm HBm Hr HfA HfB).
  - exact Hpos_all.
Qed.

Definition phase_extension_pos_case_n1_constructor : Prop :=
  forall phi mid final,
    length (LowerBound.deck_A mid) = 1 ->
    length (LowerBound.deck_B mid) = 1 ->
    runs_flex_blocks phi mid (flex_blocks_of_n 1) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    exists start,
      length (LowerBound.deck_A start) = 2 /\
      length (LowerBound.deck_B start) = 2 /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size 2)) mid.

Definition phase_extension_pos_case_ge2_constructor : Prop :=
  forall n phi mid final,
    n >= 2 ->
    length (LowerBound.deck_A mid) = n ->
    length (LowerBound.deck_B mid) = n ->
    runs_flex_blocks phi mid (flex_blocks_of_n n) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    exists start,
      length (LowerBound.deck_A start) = S n /\
      length (LowerBound.deck_B start) = S n /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size (S n))) mid.

Definition phase_block_head_constructor_ge2 : Prop :=
  forall n phi mid,
    n >= 2 ->
    length (LowerBound.deck_A mid) = n ->
    length (LowerBound.deck_B mid) = n ->
    exists start,
      length (LowerBound.deck_A start) = S n /\
      length (LowerBound.deck_B start) = S n /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size (S n))) mid.

Lemma phase_extension_pos_case_ge2_from_head_constructor :
  phase_block_head_constructor_ge2 ->
  phase_extension_pos_case_ge2_constructor.
Proof.
  intros Hhead n phi mid final Hn HAm HBm _ _ _.
  exact (Hhead n phi mid Hn HAm HBm).
Qed.

Theorem lower_bound_solution_all_via_phase_block_head_ge2 :
  phase_block_head_constructor_ge2 ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Hhead n Hn.
  eapply lower_bound_solution_all_via_candidate_step_ge2.
  - intros k Hk Hcand.
    destruct Hcand as [phi [mid [final [HAm [HBm [Hr [HfA HfB]]]]]]].
    destruct (Hhead k phi mid Hk HAm HBm)
      as [start [HAs [HBs Hr_head]]].
    eapply candidate_obligation_from_head_tail.
    + exact HAs.
    + exact HBs.
    + exact Hr_head.
    + exact Hr.
    + exact HfA.
    + exact HfB.
  - exact Hn.
Qed.

Lemma step_NN_impossible_for_phi_tt :
  forall c c',
    ~ LowerBound.step phi_tt c LowerBound.NN c'.
Proof.
  intros c c' Hs.
  inversion Hs; subst.
  unfold phi_tt in H.
  discriminate.
Qed.

Lemma runs_starting_with_NN_impossible_for_phi_tt :
  forall c os c',
    ~ LowerBound.runs phi_tt c (LowerBound.NN :: os) c'.
Proof.
  intros c os c' Hr.
  destruct (runs_cons_inv phi_tt c LowerBound.NN os c' Hr) as [cm [Hs _]].
  exact (step_NN_impossible_for_phi_tt c cm Hs).
Qed.

Lemma phase_block_head_constructor_ge2_false :
  ~ phase_block_head_constructor_ge2.
Proof.
  intro Hhead.
  set (mid := {| LowerBound.deck_A := [0; 1]; LowerBound.deck_B := [0; 1] |}).
  destruct (Hhead 2 phi_tt mid ltac:(lia) eq_refl eq_refl)
    as [start [_ [_ Hr]]].
  simpl in Hr.
  eapply runs_starting_with_NN_impossible_for_phi_tt.
  exact Hr.
Qed.

Definition phase_block_head_constructor_ge2_restricted : Prop :=
  forall n phi mid final,
    n >= 2 ->
    length (LowerBound.deck_A mid) = n ->
    length (LowerBound.deck_B mid) = n ->
    runs_flex_blocks phi mid (flex_blocks_of_n n) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    exists start,
      length (LowerBound.deck_A start) = S n /\
      length (LowerBound.deck_B start) = S n /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size (S n))) mid.

Definition ge2_tail_reachable
  (n : nat) (phi : nat -> nat -> LowerBound.outcome) (mid : LowerBound.config) : Prop :=
  exists final,
    runs_flex_blocks phi mid (flex_blocks_of_n n) final /\
    LowerBound.deck_A final = [] /\
    LowerBound.deck_B final = [].

Definition phase_block_head_constructor_ge2_on_tail_reachable : Prop :=
  forall n phi mid,
    n >= 2 ->
    length (LowerBound.deck_A mid) = n ->
    length (LowerBound.deck_B mid) = n ->
    ge2_tail_reachable n phi mid ->
    exists start,
      length (LowerBound.deck_A start) = S n /\
      length (LowerBound.deck_B start) = S n /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size (S n))) mid.

Lemma ge2_tail_reachable_2_implies_mid_pattern :
  forall phi mid,
    length (LowerBound.deck_A mid) = 2 ->
    length (LowerBound.deck_B mid) = 2 ->
    ge2_tail_reachable 2 phi mid ->
    exists u x v y,
      LowerBound.deck_A mid = [u; x] /\
      LowerBound.deck_B mid = [v; y] /\
      phi u v = LowerBound.NN /\
      phi x y = LowerBound.WA /\
      phi x v = LowerBound.TT.
Proof.
  intros phi mid HAm HBm Hreach.
  destruct Hreach as [final [Hrb _]].
  pose proof (runs_flex_blocks_to_runs phi mid (flex_blocks_of_n 2) final Hrb) as Hr.
  rewrite flex_blocks_of_n_2_eq in Hr.
  rewrite flex_blocks_of_2_trace in Hr.
  destruct mid as [da db].
  simpl in HAm, HBm, Hr.
  destruct da as [|u da']; [discriminate HAm|].
  destruct da' as [|x da'']; [discriminate HAm|].
  destruct da'' as [|a3 da''']; [|discriminate HAm].
  destruct db as [|v db']; [discriminate HBm|].
  destruct db' as [|y db'']; [discriminate HBm|].
  destruct db'' as [|b3 db''']; [|discriminate HBm].
  simpl in Hr.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [u; x]; LowerBound.deck_B := [v; y] |}
              LowerBound.NN
              [LowerBound.WA; LowerBound.TT; LowerBound.TT]
              final Hr)
    as [c1 [Hs1 Hr1]].
  inversion Hs1; subst c1.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [x; u]; LowerBound.deck_B := [y; v] |}
              LowerBound.WA
              [LowerBound.TT; LowerBound.TT]
              final Hr1)
    as [c2 [Hs2 Hr2]].
  inversion Hs2; subst c2.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [x; u]; LowerBound.deck_B := [v; y] |}
              LowerBound.TT
              [LowerBound.TT]
              final Hr2)
    as [c3 [Hs3 _]].
  inversion Hs3; subst c3.
  exists u, x, v, y.
  repeat split; reflexivity || assumption.
Qed.

Definition adaptive_step_2_pattern_constructor : Prop :=
  forall phi mid final bs,
    length (LowerBound.deck_A mid) = 2 ->
    length (LowerBound.deck_B mid) = 2 ->
    length bs = 2 ->
    flex_blocks_duration bs = LowerBound.T 2 ->
    runs_flex_blocks phi mid bs final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    exists b start,
      flex_blocks_duration [b] = LowerBound.phase_term 3 /\
      length (LowerBound.deck_A start) = 3 /\
      length (LowerBound.deck_B start) = 3 /\
      LowerBound.runs phi start (trace_of_flex_block b) mid.

Definition adaptive_tail_reachable_2_canonicalizable : Prop :=
  forall phi mid,
    length (LowerBound.deck_A mid) = 2 ->
    length (LowerBound.deck_B mid) = 2 ->
    adaptive_tail_reachable 2 phi mid ->
    ge2_tail_reachable 2 phi mid.

Definition adaptive_step_2_from_ge2_pattern : Prop :=
  forall phi mid u x v y,
    LowerBound.deck_A mid = [u; x] ->
    LowerBound.deck_B mid = [v; y] ->
    phi u v = LowerBound.NN ->
    phi x y = LowerBound.WA ->
    phi x v = LowerBound.TT ->
    exists b start,
      flex_blocks_duration [b] = LowerBound.phase_term 3 /\
      length (LowerBound.deck_A start) = 3 /\
      length (LowerBound.deck_B start) = 3 /\
      LowerBound.runs phi start (trace_of_flex_block b) mid.

Definition adaptive_step_2_from_ge2_pattern_fixed_head3 : Prop :=
  forall phi mid u x v y,
    LowerBound.deck_A mid = [u; x] ->
    LowerBound.deck_B mid = [v; y] ->
    phi u v = LowerBound.NN ->
    phi x y = LowerBound.WA ->
    phi x v = LowerBound.TT ->
    exists start,
      length (LowerBound.deck_A start) = 3 /\
      length (LowerBound.deck_B start) = 3 /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size 3)) mid.

Lemma adaptive_step_2_pattern_constructor_from_canonical_ge2_pattern :
  adaptive_tail_reachable_2_canonicalizable ->
  adaptive_step_2_from_ge2_pattern ->
  adaptive_step_2_pattern_constructor.
Proof.
  intros Hcanon Hpat phi mid final bs HAm HBm Hlen Hdur Hr HfA HfB.
  assert (Hadapt : adaptive_tail_reachable 2 phi mid).
  {
    exists final, bs.
    repeat split; assumption.
  }
  pose proof (Hcanon phi mid HAm HBm Hadapt) as Hge2.
  destruct (ge2_tail_reachable_2_implies_mid_pattern phi mid HAm HBm Hge2)
    as [u [x [v [y [HA [HB [Hnn [Hwa Htt]]]]]]]].
  exact (Hpat phi mid u x v y HA HB Hnn Hwa Htt).
Qed.

Lemma adaptive_step_at_tail_reachable_2_if_pattern_constructor :
  adaptive_step_2_pattern_constructor ->
  adaptive_step_at_tail_reachable 2.
Proof.
  intros Hpat2 phi mid HAm HBm Hreach.
  destruct Hreach as [final [bs [Hlen [Hdur [Hr [HfA HfB]]]]]].
  exact (Hpat2 phi mid final bs HAm HBm Hlen Hdur Hr HfA HfB).
Qed.

Theorem lower_bound_solution_all_via_adaptive_pattern_base_step :
  adaptive_step_2_pattern_constructor ->
  adaptive_step_ge2_tail_reachable_step ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Hpat2 Hstep n Hn.
  apply lower_bound_solution_all_via_adaptive_ge2_base_step.
  - apply adaptive_step_at_tail_reachable_2_if_pattern_constructor.
    exact Hpat2.
  - exact Hstep.
  - exact Hn.
Qed.

Theorem lower_bound_solution_all_via_adaptive_canonical_ge2_pattern_base_step :
  adaptive_tail_reachable_2_canonicalizable ->
  adaptive_step_2_from_ge2_pattern ->
  adaptive_step_ge2_tail_reachable_step ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Hcanon Hpat Hstep n Hn.
  apply lower_bound_solution_all_via_adaptive_pattern_base_step.
  - apply adaptive_step_2_pattern_constructor_from_canonical_ge2_pattern.
    + exact Hcanon.
    + exact Hpat.
  - exact Hstep.
  - exact Hn.
Qed.

Definition phase_block_head_constructor_2_pattern_constructor : Prop :=
  forall phi mid u x v y,
    LowerBound.deck_A mid = [u; x] ->
    LowerBound.deck_B mid = [v; y] ->
    phi u v = LowerBound.NN ->
    phi x y = LowerBound.WA ->
    phi x v = LowerBound.TT ->
    exists start,
      length (LowerBound.deck_A start) = 3 /\
      length (LowerBound.deck_B start) = 3 /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size 3)) mid.

Definition phase_block_head_constructor_at_tail_reachable (n : nat) : Prop :=
  forall phi mid,
    length (LowerBound.deck_A mid) = n ->
    length (LowerBound.deck_B mid) = n ->
    ge2_tail_reachable n phi mid ->
    exists start,
      length (LowerBound.deck_A start) = S n /\
      length (LowerBound.deck_B start) = S n /\
      LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size (S n))) mid.

Lemma phase_block_head_constructor_at_tail_reachable_2_if_pattern_constructor :
  phase_block_head_constructor_2_pattern_constructor ->
  phase_block_head_constructor_at_tail_reachable 2.
Proof.
  intros Hpat2 phi mid HAm HBm Hreach.
  destruct (ge2_tail_reachable_2_implies_mid_pattern phi mid HAm HBm Hreach)
    as [u [x [v [y [HA [HB [Hnn [Hwa Htt]]]]]]]].
  exact (Hpat2 phi mid u x v y HA HB Hnn Hwa Htt).
Qed.

Definition phase_block_head_constructor_ge2_step_tail_reachable : Prop :=
  forall n,
    n >= 2 ->
    phase_block_head_constructor_at_tail_reachable n ->
    phase_block_head_constructor_at_tail_reachable (S n).

Theorem phase_block_head_constructor_ge2_on_tail_reachable_from_base_step :
  phase_block_head_constructor_at_tail_reachable 2 ->
  phase_block_head_constructor_ge2_step_tail_reachable ->
  phase_block_head_constructor_ge2_on_tail_reachable.
Proof.
  intros Hbase2 Hstep n phi mid Hn HAm HBm Hreach.
  assert (Hall : forall m, m >= 2 -> phase_block_head_constructor_at_tail_reachable m).
  {
    intros m Hm.
    assert (Hex : exists k, m = 2 + k) by (exists (m - 2); lia).
    destruct Hex as [k Hk].
    subst m.
    induction k as [|k IH].
    - replace (2 + 0) with 2 by lia.
      exact Hbase2.
    - replace (2 + S k) with (S (2 + k)) by lia.
      apply Hstep.
      + lia.
      + apply IH.
        lia.
  }
  exact (Hall n Hn phi mid HAm HBm Hreach).
Qed.

Lemma restricted_head_constructor_from_on_tail_reachable :
  phase_block_head_constructor_ge2_on_tail_reachable ->
  phase_block_head_constructor_ge2_restricted.
Proof.
  intros Hon n phi mid final Hn HAm HBm Hr HfA HfB.
  apply (Hon n phi mid Hn HAm HBm).
  exists final.
  repeat split; assumption.
Qed.

Lemma on_tail_reachable_from_restricted_head_constructor :
  phase_block_head_constructor_ge2_restricted ->
  phase_block_head_constructor_ge2_on_tail_reachable.
Proof.
  intros Hrestricted n phi mid Hn HAm HBm Hreach.
  destruct Hreach as [final [Hr [HfA HfB]]].
  exact (Hrestricted n phi mid final Hn HAm HBm Hr HfA HfB).
Qed.

Lemma phase_extension_pos_case_ge2_from_restricted_head_constructor :
  phase_block_head_constructor_ge2_restricted ->
  phase_extension_pos_case_ge2_constructor.
Proof.
  intros Hrestricted n phi mid final Hn HAm HBm Hr HfA HfB.
  exact (Hrestricted n phi mid final Hn HAm HBm Hr HfA HfB).
Qed.

Lemma restricted_head_constructor_from_phase_extension_pos_case_ge2 :
  phase_extension_pos_case_ge2_constructor ->
  phase_block_head_constructor_ge2_restricted.
Proof.
  intros Hge2 n phi mid final Hn HAm HBm Hr HfA HfB.
  exact (Hge2 n phi mid final Hn HAm HBm Hr HfA HfB).
Qed.

Theorem lower_bound_solution_all_via_phase_block_head_ge2_restricted :
  phase_block_head_constructor_ge2_restricted ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Hrestricted n Hn.
  eapply lower_bound_solution_all_via_candidate_step_ge2.
  - intros k Hk Hcand.
    destruct Hcand as [phi [mid [final [HAm [HBm [Hr [HfA HfB]]]]]]].
    destruct (Hrestricted k phi mid final Hk HAm HBm Hr HfA HfB)
      as [start [HAs [HBs Hr_head]]].
    eapply candidate_obligation_from_head_tail.
    + exact HAs.
    + exact HBs.
    + exact Hr_head.
    + exact Hr.
    + exact HfA.
    + exact HfB.
  - exact Hn.
Qed.

Theorem lower_bound_solution_all_via_phase_block_head_ge2_tail_reachable :
  phase_block_head_constructor_ge2_on_tail_reachable ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Hon n Hn.
  apply lower_bound_solution_all_via_phase_block_head_ge2_restricted.
  apply restricted_head_constructor_from_on_tail_reachable.
  exact Hon.
  exact Hn.
Qed.

Theorem lower_bound_solution_all_via_phase_block_head_ge2_base_step :
  phase_block_head_constructor_at_tail_reachable 2 ->
  phase_block_head_constructor_ge2_step_tail_reachable ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Hbase2 Hstep n Hn.
  apply lower_bound_solution_all_via_phase_block_head_ge2_tail_reachable.
  apply phase_block_head_constructor_ge2_on_tail_reachable_from_base_step.
  - exact Hbase2.
  - exact Hstep.
  - exact Hn.
Qed.

Theorem lower_bound_solution_all_via_ge2_pattern_base_step :
  phase_block_head_constructor_2_pattern_constructor ->
  phase_block_head_constructor_ge2_step_tail_reachable ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Hpat2 Hstep n Hn.
  apply lower_bound_solution_all_via_phase_block_head_ge2_base_step.
  - apply phase_block_head_constructor_at_tail_reachable_2_if_pattern_constructor.
    exact Hpat2.
  - exact Hstep.
  - exact Hn.
Qed.

Lemma flex_block_of_size_S_ge2_shape :
  forall n,
    n >= 2 ->
    flex_block_of_size (S n) = (ModeNN_WA, 1, LowerBound.phase_term (S n) - 2).
Proof.
  intros n Hn.
  destruct n as [|n']; [lia|].
  destruct n' as [|n'']; [lia|].
  reflexivity.
Qed.

Lemma trace_of_flex_block_size_S_ge2_shape :
  forall n,
    n >= 2 ->
    trace_of_flex_block (flex_block_of_size (S n)) =
      repeat LowerBound.NN (LowerBound.phase_term (S n) - 2) ++
      [LowerBound.WA; LowerBound.TT].
Proof.
  intros n Hn.
  rewrite flex_block_of_size_S_ge2_shape by exact Hn.
  unfold trace_of_flex_block.
  simpl.
  reflexivity.
Qed.

Lemma runs_flex_block_size3_impossible :
  forall phi start mid,
    length (LowerBound.deck_A start) = 3 ->
    length (LowerBound.deck_B start) = 3 ->
    ~ LowerBound.runs phi start
        (trace_of_flex_block (flex_block_of_size 3)) mid.
Proof.
  intros phi start mid HAs HBs Hr.
  destruct start as [da db].
  simpl in HAs, HBs, Hr.
  destruct da as [|a0 da']; [discriminate HAs|].
  destruct da' as [|a1 da'']; [discriminate HAs|].
  destruct da'' as [|a2 da''']; [discriminate HAs|].
  destruct da''' as [|a3 da'''']; [|discriminate HAs].
  destruct db as [|b0 db']; [discriminate HBs|].
  destruct db' as [|b1 db'']; [discriminate HBs|].
  destruct db'' as [|b2 db''']; [discriminate HBs|].
  destruct db''' as [|b3 db'''']; [|discriminate HBs].
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [a0; a1; a2]; LowerBound.deck_B := [b0; b1; b2] |}
              LowerBound.NN
              [LowerBound.NN; LowerBound.NN; LowerBound.NN; LowerBound.NN; LowerBound.WA; LowerBound.TT]
              mid Hr)
    as [c1 [Hs1 Hr1]].
  inversion Hs1; subst c1.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [a1; a2; a0]; LowerBound.deck_B := [b1; b2; b0] |}
              LowerBound.NN
              [LowerBound.NN; LowerBound.NN; LowerBound.NN; LowerBound.WA; LowerBound.TT]
              mid Hr1)
    as [c2 [Hs2 Hr2]].
  inversion Hs2; subst c2.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [a2; a0; a1]; LowerBound.deck_B := [b2; b0; b1] |}
              LowerBound.NN
              [LowerBound.NN; LowerBound.NN; LowerBound.WA; LowerBound.TT]
              mid Hr2)
    as [c3 [Hs3 Hr3]].
  inversion Hs3; subst c3.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [a0; a1; a2]; LowerBound.deck_B := [b0; b1; b2] |}
              LowerBound.NN
              [LowerBound.NN; LowerBound.WA; LowerBound.TT]
              mid Hr3)
    as [c4 [Hs4 Hr4]].
  inversion Hs4; subst c4.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [a1; a2; a0]; LowerBound.deck_B := [b1; b2; b0] |}
              LowerBound.NN
              [LowerBound.WA; LowerBound.TT]
              mid Hr4)
    as [c5 [Hs5 Hr5]].
  inversion Hs5; subst c5.
  destruct (runs_cons_inv phi
              {| LowerBound.deck_A := [a2; a0; a1]; LowerBound.deck_B := [b2; b0; b1] |}
              LowerBound.WA
              [LowerBound.TT]
              mid Hr5)
    as [c6 [Hs6 _]].
  pose proof (step_NN_head_value phi a2 [a0; a1] b2 [b0; b1]
                {| LowerBound.deck_A := [a0; a1; a2]; LowerBound.deck_B := [b0; b1; b2] |}
                Hs3) as Hnn.
  pose proof (step_WA_head_value phi a2 [a0; a1] b2 [b0; b1] c6 Hs6) as Hwa.
  rewrite Hnn in Hwa.
  discriminate.
Qed.

Lemma ge2_tail_reachable_2_exists_for_phi2 :
  exists mid,
    length (LowerBound.deck_A mid) = 2 /\
    length (LowerBound.deck_B mid) = 2 /\
    ge2_tail_reachable 2 LowerBound.phi2 mid.
Proof.
  destruct runs_flex_blocks_2_witness as [mid [final [HAm [HBm [Hrb [HfA HfB]]]]]].
  exists mid.
  repeat split; try assumption.
  exists final.
  repeat split; assumption.
Qed.

Lemma phase_block_head_constructor_at_tail_reachable_2_false :
  ~ phase_block_head_constructor_at_tail_reachable 2.
Proof.
  intro Hbase2.
  destruct ge2_tail_reachable_2_exists_for_phi2 as [mid [HAm [HBm Hreach]]].
  destruct (Hbase2 LowerBound.phi2 mid HAm HBm Hreach)
    as [start [HAs [HBs Hr]]].
  exact (runs_flex_block_size3_impossible LowerBound.phi2 start mid HAs HBs Hr).
Qed.

Lemma phase_block_head_constructor_2_pattern_constructor_false :
  ~ phase_block_head_constructor_2_pattern_constructor.
Proof.
  intro Hpat2.
  apply phase_block_head_constructor_at_tail_reachable_2_false.
  apply phase_block_head_constructor_at_tail_reachable_2_if_pattern_constructor.
  exact Hpat2.
Qed.

Lemma adaptive_step_2_from_ge2_pattern_fixed_head3_false :
  ~ adaptive_step_2_from_ge2_pattern_fixed_head3.
Proof.
  intro Hfixed.
  apply phase_block_head_constructor_2_pattern_constructor_false.
  intros phi mid u x v y HA HB Hnn Hwa Htt.
  destruct (Hfixed phi mid u x v y HA HB Hnn Hwa Htt)
    as [start [HAs [HBs Hr]]].
  exists start.
  repeat split; assumption.
Qed.

Lemma phase_block_head_constructor_ge2_restricted_false :
  ~ phase_block_head_constructor_ge2_restricted.
Proof.
  intro Hrestricted.
  assert (Hon : phase_block_head_constructor_ge2_on_tail_reachable).
  {
    apply on_tail_reachable_from_restricted_head_constructor.
    exact Hrestricted.
  }
  assert (Hbase2 : phase_block_head_constructor_at_tail_reachable 2).
  {
    intros phi mid HAm HBm Hreach.
    apply (Hon 2 phi mid).
    - lia.
    - exact HAm.
    - exact HBm.
    - exact Hreach.
  }
  exact (phase_block_head_constructor_at_tail_reachable_2_false Hbase2).
Qed.

Lemma phase_extension_pos_case_ge2_constructor_false :
  ~ phase_extension_pos_case_ge2_constructor.
Proof.
  intro Hge2.
  apply phase_block_head_constructor_ge2_restricted_false.
  apply restricted_head_constructor_from_phase_extension_pos_case_ge2.
  exact Hge2.
Qed.

Lemma candidate_step_ge2_from_phase_extension_pos_case_ge2 :
  phase_extension_pos_case_ge2_constructor ->
  forall n,
    n >= 2 ->
    candidate_flex_blocks_obligation n ->
    candidate_flex_blocks_obligation (S n).
Proof.
  intros Hge2 n Hn Hcand.
  destruct Hcand as [phi [mid [final [HAm [HBm [Hr [HfA HfB]]]]]]].
  destruct (Hge2 n phi mid final Hn HAm HBm Hr HfA HfB)
    as [start [HAs [HBs Hr_head]]].
  eapply candidate_obligation_from_head_tail.
  - exact HAs.
  - exact HBs.
  - exact Hr_head.
  - exact Hr.
  - exact HfA.
  - exact HfB.
Qed.

Theorem lower_bound_solution_all_via_ge2_phase_constructor :
  phase_extension_pos_case_ge2_constructor ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Hge2 n Hn.
  exact (lower_bound_solution_all_via_candidate_step_ge2
           (candidate_step_ge2_from_phase_extension_pos_case_ge2 Hge2)
           n Hn).
Qed.

Definition phase_extension_pos_case_n1_pattern_witness : Prop :=
  forall phi mid final,
    length (LowerBound.deck_A mid) = 1 ->
    length (LowerBound.deck_B mid) = 1 ->
    runs_flex_blocks phi mid (flex_blocks_of_n 1) final ->
    LowerBound.deck_A final = [] ->
    LowerBound.deck_B final = [] ->
    exists x v,
      forall u y,
        LowerBound.deck_A mid = [u] ->
        LowerBound.deck_B mid = [y] ->
        phi u v = LowerBound.NN /\
        phi x y = LowerBound.WA /\
        phi x v = LowerBound.TT.

Lemma phase_extension_pos_case_n1_constructor_if_pattern_witness :
  phase_extension_pos_case_n1_pattern_witness ->
  phase_extension_pos_case_n1_constructor.
Proof.
  intros Hpat_all phi mid final HAm HBm Hr HfA HfB.
  destruct (Hpat_all phi mid final HAm HBm Hr HfA HfB) as [x [v Hpat]].
  exact (phase_extension_pos_case_n1_if_pattern
           phi mid final x v HAm HBm Hr HfA HfB Hpat).
Qed.

Lemma phase_extension_pos_case_constructor_from_n1_ge2 :
  phase_extension_pos_case_n1_constructor ->
  phase_extension_pos_case_ge2_constructor ->
  phase_extension_pos_case_constructor.
Proof.
  intros Hn1 Hge2 n phi mid final Hn HAm HBm Hr HfA HfB.
  destruct n as [|n'].
  - lia.
  - destruct n' as [|n''].
    + exact (Hn1 phi mid final HAm HBm Hr HfA HfB).
    + apply (Hge2 (S (S n'')) phi mid final).
      * lia.
      * exact HAm.
      * exact HBm.
      * exact Hr.
      * exact HfA.
      * exact HfB.
Qed.

Theorem lower_bound_solution_all_via_n1_ge2_phase_assumptions :
  (forall (phi : nat -> nat -> LowerBound.outcome), exists a b, phi a b = LowerBound.TT) ->
  phase_extension_pos_case_n1_constructor ->
  phase_extension_pos_case_ge2_constructor ->
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros Htt_all Hn1 Hge2 n Hn.
  exact (lower_bound_solution_all_via_phase_extension_split
           (phase_extension_split_from_explicit_assumptions
              Htt_all
              (phase_extension_pos_case_constructor_from_n1_ge2 Hn1 Hge2))
           n Hn).
Qed.

    Theorem lower_bound_solution_all_via_tt_n1_pattern_ge2_assumptions :
      (forall (phi : nat -> nat -> LowerBound.outcome), exists a b, phi a b = LowerBound.TT) ->
      phase_extension_pos_case_n1_pattern_witness ->
      phase_extension_pos_case_ge2_constructor ->
      forall n,
        n > 0 ->
        LowerBound.lower_bound_solution n.
    Proof.
      intros Htt_all Hn1pat Hge2.
      apply lower_bound_solution_all_via_n1_ge2_phase_assumptions.
      - exact Htt_all.
      - apply phase_extension_pos_case_n1_constructor_if_pattern_witness.
        exact Hn1pat.
      - exact Hge2.
    Qed.

Lemma phase_extension_split_from_local_premises :
  phase_extension_zero_case_witness ->
  phase_extension_pos_case_constructor ->
  phase_extension_obligation_split.
Proof.
  intros Hzero Hpos.
  split.
  - exact Hzero.
  - exact Hpos.
Qed.

Section PhaseExtensionLocalPremiseReduction.

Hypothesis Hzero_local : phase_extension_zero_case_witness.
Hypothesis Hpos_local : phase_extension_pos_case_constructor.

Theorem lower_bound_solution_all_via_local_phase_premises :
  forall n,
    n > 0 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros n Hn.
  exact (lower_bound_solution_all_via_phase_extension_split
           (phase_extension_split_from_local_premises Hzero_local Hpos_local)
           n Hn).
Qed.

End PhaseExtensionLocalPremiseReduction.

Lemma lower_bound_flex_blocks_obligation_0 :
  lower_bound_flex_blocks_obligation 0.
Proof.
  exists phi_tt,
    {| LowerBound.deck_A := []; LowerBound.deck_B := [] |},
    {| LowerBound.deck_A := []; LowerBound.deck_B := [] |},
    ([] : list block_flex).
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ apply RunsFlexBlocksNil.
           ++ split; reflexivity.
Qed.

Lemma lower_bound_flex_blocks_obligation_1 :
  lower_bound_flex_blocks_obligation 1.
Proof.
  exists phi_tt,
    {| LowerBound.deck_A := [0]; LowerBound.deck_B := [0] |},
    {| LowerBound.deck_A := []; LowerBound.deck_B := [] |},
    [flex_block_of_size 1].
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * split.
         -- unfold flex_blocks_duration, flex_block_of_size, LowerBound.T.
           simpl.
           reflexivity.
        -- split.
           ++ eapply RunsFlexBlocksCons.
              ** unfold trace_of_flex_block, flex_block_of_size.
                 simpl.
                 eapply LowerBound.RunsCons.
                 --- apply (LowerBound.StepTT phi_tt 0 [] 0 []). reflexivity.
                 --- apply LowerBound.RunsNil.
              ** apply RunsFlexBlocksNil.
           ++ split; reflexivity.
Qed.

Lemma lower_bound_solution_1_via_flex_blocks :
  LowerBound.lower_bound_solution 1.
Proof.
  apply lower_bound_solution_from_flex_blocks_obligation.
  exact lower_bound_flex_blocks_obligation_1.
Qed.

Theorem lower_bound_solution_upto_2_via_flex_blocks :
  forall n,
    n > 0 ->
    n <= 2 ->
    LowerBound.lower_bound_solution n.
Proof.
  intros n Hpos Hle2.
  destruct n as [|n']; [lia|].
  destruct n' as [|n''].
  - exact lower_bound_solution_1_via_flex_blocks.
  - assert (n'' = 0) by lia.
    subst n''.
    exact lower_bound_solution_2_via_flex_blocks.
Qed.

Definition canonical_phase_trace (m : nat) : list LowerBound.outcome :=
  repeat LowerBound.WA (m * m - m) ++ [LowerBound.TT].

Lemma canonical_phase_trace_length :
  forall m,
    length (canonical_phase_trace m) = LowerBound.phase_term m.
Proof.
  intro m.
  unfold canonical_phase_trace, LowerBound.phase_term.
  rewrite length_app, repeat_length.
  simpl.
  lia.
Qed.

Lemma canonical_phase_trace_tie_count :
  forall m,
    LowerBound.tie_count (canonical_phase_trace m) = 1.
Proof.
  intro m.
  unfold canonical_phase_trace, LowerBound.tie_count.
  rewrite count_occ_app.
  rewrite count_occ_repeat_neq by discriminate.
  simpl.
  lia.
Qed.

Lemma canonical_phase_trace_non_tie_count :
  forall m,
    non_tie_count (canonical_phase_trace m) = m * m - m.
Proof.
  intro m.
  unfold non_tie_count.
  rewrite canonical_phase_trace_length.
  rewrite canonical_phase_trace_tie_count.
  unfold LowerBound.phase_term.
  lia.
Qed.

Lemma phase_term_as_budget_plus_tie :
  forall m,
    LowerBound.phase_term m = (m * m - m) + 1.
Proof.
  intro m.
  unfold LowerBound.phase_term.
  lia.
Qed.

Lemma visited_bound_via_reserved_cells :
  forall m visited forbidden,
    NoDup visited ->
    NoDup forbidden ->
    (forall s, In s visited -> ~ In s forbidden) ->
    Forall (TheoremPhasewise.bounded_state m) visited ->
    Forall (TheoremPhasewise.bounded_state m) forbidden ->
    length forbidden = m - 1 ->
    length visited <= LowerBound.phase_term m.
Proof.
  intros m visited forbidden HnodupV HnodupF Hdisj HboundedV HboundedF HlenF.
  pose proof
    (TheoremPhasewise.theorem_phasewise_bound
      m visited forbidden HnodupV HnodupF Hdisj HboundedV HboundedF HlenF)
    as Hbound.
  unfold LowerBound.phase_term.
  lia.
Qed.

Definition phi_direct (n i j : nat) : LowerBound.outcome :=
  if Nat.eqb (i + j) (n - 1) then LowerBound.TT
  else if Nat.eqb (i + j) (n - 2) then LowerBound.NN
  else LowerBound.WA.

Definition phi_local (m u v : nat) : LowerBound.outcome :=
  if Nat.eqb (u + v) (m - 1) then LowerBound.TT
  else if Nat.eqb (u + v) (m - 2) then LowerBound.NN
  else LowerBound.WA.

Lemma phi_direct_restricts_to_local :
  forall n m u v,
    m <= n ->
    m >= 2 ->
    u < m ->
    v < m ->
    phi_direct n u (v + (n - m)) = phi_local m u v.
Proof.
  intros n m u v Hmn Hm Hu Hv.
  unfold phi_direct, phi_local.
  assert (Hs1 : u + (v + (n - m)) = (u + v) + (n - m)) by lia.
  rewrite Hs1.
  set (x := u + v).
  assert (Ht : (x + (n - m) =? n - 1) = (x =? m - 1)).
  {
    destruct (x + (n - m) =? n - 1) eqn:Hl;
    destruct (x =? m - 1) eqn:Hr; try reflexivity.
    - apply Nat.eqb_eq in Hl.
      apply Nat.eqb_neq in Hr.
      exfalso.
      apply Hr.
      lia.
    - apply Nat.eqb_neq in Hl.
      apply Nat.eqb_eq in Hr.
      exfalso.
      apply Hl.
      lia.
  }
  rewrite Ht.
  destruct (x =? m - 1) eqn:HeqT; [reflexivity|].
  assert (Hn : (x + (n - m) =? n - 2) = (x =? m - 2)).
  {
    destruct (x + (n - m) =? n - 2) eqn:Hl;
    destruct (x =? m - 2) eqn:Hr; try reflexivity.
    - apply Nat.eqb_eq in Hl.
      apply Nat.eqb_neq in Hr.
      exfalso.
      apply Hr.
      lia.
    - apply Nat.eqb_neq in Hl.
      apply Nat.eqb_eq in Hr.
      exfalso.
      apply Hl.
      lia.
  }
  rewrite Hn.
  reflexivity.
Qed.

Definition local_step (m : nat) (s : nat * nat) : option (nat * nat) :=
  let '(u, v) := s in
  match phi_local m u v with
  | LowerBound.WA => Some (u, (S v) mod m)
  | LowerBound.NN => Some ((S u) mod m, (S v) mod m)
  | LowerBound.TT => None
  | LowerBound.WB => None
  end.

Lemma local_step_m1_terminates_immediately :
  local_step 1 (0, 0) = None.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma local_step_m2_first :
  local_step 2 (0, 0) = Some (1, 1).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma local_step_m2_second :
  local_step 2 (1, 1) = Some (1, 0).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma local_step_m2_third_tie :
  local_step 2 (1, 0) = None.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem local_m2_exact_three_step_trace :
  exists s1 s2,
    local_step 2 (0, 0) = Some s1 /\
    local_step 2 s1 = Some s2 /\
    local_step 2 s2 = None /\
    s2 = (1, 0).
Proof.
  exists (1, 1), (1, 0).
  repeat split;
    try apply local_step_m2_first;
    try apply local_step_m2_second;
    try apply local_step_m2_third_tie;
    reflexivity.
Qed.

Lemma phi_local_row0_before_boundary_is_WA :
  forall m v,
    m > 2 ->
    v <= m - 3 ->
    phi_local m 0 v = LowerBound.WA.
Proof.
  intros m v Hm Hv.
  unfold phi_local.
  simpl.
  assert (Hv1 : v <> m - 1) by lia.
  assert (Hv2 : v <> m - 2) by lia.
  destruct (Nat.eqb_spec v (m - 1)) as [Heq1|Hneq1].
  - lia.
  - destruct (Nat.eqb_spec v (m - 2)) as [Heq2|Hneq2].
    + lia.
    + reflexivity.
Qed.

Lemma phi_local_row0_at_boundary_is_NN :
  forall m,
    m > 2 ->
    phi_local m 0 (m - 2) = LowerBound.NN.
Proof.
  intros m Hm.
  unfold phi_local.
  simpl.
  destruct (Nat.eqb_spec (m - 2) (m - 1)) as [Heq1|Hneq1].
  - lia.
  - destruct (Nat.eqb_spec (m - 2) (m - 2)) as [Heq2|Hneq2].
    + reflexivity.
    + contradiction.
Qed.

Lemma local_step_row0_before_boundary :
  forall m v,
    m > 2 ->
    v <= m - 3 ->
    local_step m (0, v) = Some (0, S v).
Proof.
  intros m v Hm Hv.
  unfold local_step.
  rewrite phi_local_row0_before_boundary_is_WA by assumption.
  rewrite Nat.mod_small by lia.
  reflexivity.
Qed.

Lemma local_step_row0_boundary_to_row1 :
  forall m,
    m > 2 ->
    local_step m (0, m - 2) = Some (1, m - 1).
Proof.
  intros m Hm.
  unfold local_step.
  rewrite phi_local_row0_at_boundary_is_NN by assumption.
  rewrite Nat.mod_small by lia.
  rewrite Nat.mod_small by lia.
  replace (S (m - 2)) with (m - 1) by lia.
  reflexivity.
Qed.

Lemma phi_local_intermediate_high_segment_WA :
  forall m u v,
    m > 2 ->
    1 <= u <= m - 2 ->
    m - u <= v <= m - 1 ->
    phi_local m u v = LowerBound.WA.
Proof.
  intros m u v Hm Hu Hv.
  unfold phi_local.
  simpl.
  destruct (Nat.eqb_spec (u + v) (m - 1)) as [Heq1|Hneq1].
  - lia.
  - destruct (Nat.eqb_spec (u + v) (m - 2)) as [Heq2|Hneq2].
    + lia.
    + reflexivity.
Qed.

Lemma phi_local_intermediate_low_segment_WA :
  forall m u v,
    m > 2 ->
    1 <= u <= m - 3 ->
    0 <= v <= m - 3 - u ->
    phi_local m u v = LowerBound.WA.
Proof.
  intros m u v Hm Hu Hv.
  unfold phi_local.
  simpl.
  destruct (Nat.eqb_spec (u + v) (m - 1)) as [Heq1|Hneq1].
  - lia.
  - destruct (Nat.eqb_spec (u + v) (m - 2)) as [Heq2|Hneq2].
    + lia.
    + reflexivity.
Qed.

Lemma phi_local_intermediate_exit_is_NN :
  forall m u,
    m > 2 ->
    1 <= u <= m - 2 ->
    phi_local m u (m - 2 - u) = LowerBound.NN.
Proof.
  intros m u Hm Hu.
  unfold phi_local.
  simpl.
  destruct (Nat.eqb_spec (u + (m - 2 - u)) (m - 1)) as [Heq1|Hneq1].
  - lia.
  - destruct (Nat.eqb_spec (u + (m - 2 - u)) (m - 2)) as [Heq2|Hneq2].
    + reflexivity.
    + exfalso. apply Hneq2. lia.
Qed.

Lemma local_step_intermediate_high_segment :
  forall m u v,
    m > 2 ->
    1 <= u <= m - 2 ->
    m - u <= v <= m - 1 ->
    local_step m (u, v) = Some (u, (S v) mod m).
Proof.
  intros m u v Hm Hu Hv.
  unfold local_step.
  rewrite phi_local_intermediate_high_segment_WA by assumption.
  reflexivity.
Qed.

Lemma local_step_intermediate_low_segment :
  forall m u v,
    m > 2 ->
    1 <= u <= m - 3 ->
    0 <= v <= m - 3 - u ->
    local_step m (u, v) = Some (u, S v).
Proof.
  intros m u v Hm Hu Hv.
  unfold local_step.
  rewrite phi_local_intermediate_low_segment_WA by assumption.
  rewrite Nat.mod_small by lia.
  reflexivity.
Qed.

Lemma local_step_intermediate_exit_to_next_row :
  forall m u,
    m > 2 ->
    1 <= u <= m - 2 ->
    local_step m (u, m - 2 - u) = Some (u + 1, m - 1 - u).
Proof.
  intros m u Hm Hu.
  unfold local_step.
  rewrite phi_local_intermediate_exit_is_NN by assumption.
  rewrite Nat.mod_small by lia.
  rewrite Nat.mod_small by lia.
  replace (S u) with (u + 1) by lia.
  replace (S (m - 2 - u)) with (m - 1 - u) by lia.
  reflexivity.
Qed.

Definition visited_cols_row (m u : nat) : list nat :=
  match u with
  | 0 => seq 0 (m - 1)
  | S u' =>
      if Nat.eqb u (m - 1)
      then seq 1 (m - 1) ++ [0]
      else seq (m - S u') (S u') ++ seq 0 (m - 1 - S u')
  end.

Lemma visited_cols_row_length_0 :
  forall m,
    m > 2 ->
    length (visited_cols_row m 0) = m - 1.
Proof.
  intros m Hm.
  unfold visited_cols_row.
  rewrite length_seq.
  lia.
Qed.

Lemma visited_cols_row_length_mid :
  forall m u,
    m > 2 ->
    1 <= u <= m - 2 ->
    length (visited_cols_row m u) = m - 1.
Proof.
  intros m u Hm Hu.
  destruct u as [|u']; [lia|].
  unfold visited_cols_row.
  assert (Hneq : S u' <> m - 1) by lia.
  assert (Heqb : (S u' =? m - 1) = false).
  { apply Nat.eqb_neq. exact Hneq. }
  rewrite Heqb.
  rewrite length_app, !length_seq.
  simpl.
  lia.
Qed.

Lemma visited_cols_row_length_last :
  forall m,
    m > 2 ->
    length (visited_cols_row m (m - 1)) = m.
Proof.
  intros m Hm.
  destruct (m - 1) eqn:Em1.
  - lia.
  - unfold visited_cols_row.
    assert (HmS : m = S (S n)) by lia.
    subst m.
    rewrite Nat.eqb_refl.
    rewrite length_app, length_seq.
    simpl.
    lia.
Qed.

Lemma visited_cols_row_cardinality :
  forall m u,
    m > 2 ->
    (0 <= u <= m - 2 -> length (visited_cols_row m u) = m - 1) /\
    (u = m - 1 -> length (visited_cols_row m u) = m).
Proof.
  intros m u Hm.
  split.
  - intros Hu.
    destruct u as [|u'].
    + apply visited_cols_row_length_0; assumption.
    + apply visited_cols_row_length_mid; lia.
  - intros Hu_last.
    subst u.
    apply visited_cols_row_length_last; assumption.
Qed.

  Lemma visited_cols_row_nonlast_excludes_forbidden_col :
    forall m u,
      m > 2 ->
      0 <= u <= m - 2 ->
      ~ In (m - 1 - u) (visited_cols_row m u).
  Proof.
    intros m u Hm Hu.
    destruct u as [|u'].
    - unfold visited_cols_row.
      intro Hin.
      apply in_seq in Hin.
      lia.
    - unfold visited_cols_row.
      assert (Hneq : S u' <> m - 1) by lia.
      assert (Heqb : (S u' =? m - 1) = false).
      { apply Nat.eqb_neq. exact Hneq. }
      rewrite Heqb.
      intro Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + apply in_seq in Hin.
        lia.
      + apply in_seq in Hin.
        lia.
  Qed.

  Lemma visited_cols_row_last_covers_all_cols :
    forall m c,
      m > 2 ->
      c < m ->
      In c (visited_cols_row m (m - 1)).
  Proof.
    intros m c Hm Hc.
    unfold visited_cols_row.
    destruct (m - 1) eqn:Em1.
    - lia.
    - rewrite Nat.eqb_refl.
      destruct c as [|c'].
      + apply in_or_app.
        right.
        simpl.
        left.
        reflexivity.
      + apply in_or_app.
        left.
        apply in_seq.
        lia.
  Qed.

  Theorem visited_cols_row_phase_coverage :
    forall m u,
      m > 2 ->
      (0 <= u <= m - 2 ->
        length (visited_cols_row m u) = m - 1 /\
        ~ In (m - 1 - u) (visited_cols_row m u)) /\
      (u = m - 1 ->
        length (visited_cols_row m u) = m /\
        forall c, c < m -> In c (visited_cols_row m u)).
  Proof.
    intros m u Hm.
    split.
    - intros Hu.
      split.
      + apply (proj1 (visited_cols_row_cardinality m u Hm)).
        exact Hu.
      + apply visited_cols_row_nonlast_excludes_forbidden_col; assumption.
    - intros Hu.
      subst u.
      split.
      + apply visited_cols_row_length_last; assumption.
      + intros c Hc.
        apply visited_cols_row_last_covers_all_cols; assumption.
  Qed.

  Theorem local_step_row0_dynamics_summary :
    forall m,
      m > 2 ->
      (forall v,
        0 <= v <= m - 3 ->
        local_step m (0, v) = Some (0, v + 1)) /\
      local_step m (0, m - 2) = Some (1, m - 1).
  Proof.
    intros m Hm.
    split.
    - intros v Hv.
      rewrite local_step_row0_before_boundary by lia.
      replace (S v) with (v + 1) by lia.
      reflexivity.
    - apply local_step_row0_boundary_to_row1.
      exact Hm.
  Qed.

  Theorem local_step_intermediate_row_dynamics_summary :
    forall m u,
      m > 2 ->
      1 <= u <= m - 2 ->
      (forall v,
        m - u <= v <= m - 1 ->
        local_step m (u, v) = Some (u, (v + 1) mod m)) /\
      (1 <= u <= m - 3 ->
        forall v,
          0 <= v <= m - 3 - u ->
          local_step m (u, v) = Some (u, v + 1)) /\
      local_step m (u, m - 2 - u) = Some (u + 1, m - 1 - u).
  Proof.
    intros m u Hm Hu.
    split.
    - intros v Hv.
      rewrite local_step_intermediate_high_segment by assumption.
      replace (S v) with (v + 1) by lia.
      reflexivity.
    - split.
      + intros Hu_low v Hv.
        rewrite local_step_intermediate_low_segment by assumption.
        replace (S v) with (v + 1) by lia.
        reflexivity.
      + apply local_step_intermediate_exit_to_next_row; assumption.
  Qed.

  Theorem local_step_row_phase_interface :
    forall m u,
      m > 2 ->
      (u = 0 ->
        (forall v,
          0 <= v <= m - 3 ->
          local_step m (u, v) = Some (u, v + 1)) /\
        local_step m (u, m - 2) = Some (1, m - 1)) /\
      (1 <= u <= m - 2 ->
        (forall v,
          m - u <= v <= m - 1 ->
          local_step m (u, v) = Some (u, (v + 1) mod m)) /\
        (1 <= u <= m - 3 ->
          forall v,
            0 <= v <= m - 3 - u ->
            local_step m (u, v) = Some (u, v + 1)) /\
        local_step m (u, m - 2 - u) = Some (u + 1, m - 1 - u)).
  Proof.
    intros m u Hm.
    split.
    - intro Hu0.
      subst u.
      apply local_step_row0_dynamics_summary.
      exact Hm.
    - intro Hu.
      apply local_step_intermediate_row_dynamics_summary; assumption.
  Qed.

  Lemma phi_local_last_row_nonzero_is_WA :
    forall m v,
      m > 2 ->
      1 <= v <= m - 1 ->
      phi_local m (m - 1) v = LowerBound.WA.
  Proof.
    intros m v Hm Hv.
    unfold phi_local.
    destruct (Nat.eqb_spec ((m - 1) + v) (m - 1)) as [Heq1|Hneq1].
    - lia.
    - destruct (Nat.eqb_spec ((m - 1) + v) (m - 2)) as [Heq2|Hneq2].
      + lia.
      + reflexivity.
  Qed.

  Lemma phi_local_last_row_zero_is_TT :
    forall m,
      m > 2 ->
      phi_local m (m - 1) 0 = LowerBound.TT.
  Proof.
    intros m Hm.
    unfold phi_local.
    replace ((m - 1) + 0) with (m - 1) by lia.
    rewrite Nat.eqb_refl.
    reflexivity.
  Qed.

  Lemma local_step_last_row_nonzero :
    forall m v,
      m > 2 ->
      1 <= v <= m - 1 ->
      local_step m (m - 1, v) = Some (m - 1, (v + 1) mod m).
  Proof.
    intros m v Hm Hv.
    unfold local_step.
    rewrite phi_local_last_row_nonzero_is_WA by assumption.
    replace (S v) with (v + 1) by lia.
    reflexivity.
  Qed.

  Lemma local_step_last_row_zero_terminates :
    forall m,
      m > 2 ->
      local_step m (m - 1, 0) = None.
  Proof.
    intros m Hm.
    unfold local_step.
    rewrite phi_local_last_row_zero_is_TT by assumption.
    reflexivity.
  Qed.

  Theorem local_step_last_row_dynamics_summary :
    forall m,
      m > 2 ->
      (forall v,
        1 <= v <= m - 1 ->
        local_step m (m - 1, v) = Some (m - 1, (v + 1) mod m)) /\
      local_step m (m - 1, 0) = None.
  Proof.
    intros m Hm.
    split.
    - intros v Hv.
      apply local_step_last_row_nonzero; assumption.
    - apply local_step_last_row_zero_terminates; assumption.
  Qed.

  Lemma local_phase_base_case_m1 :
    local_step 1 (0, 0) = None /\ 1 = 1 * 1 - 1 + 1.
  Proof.
    split.
    - apply local_step_m1_terminates_immediately.
    - lia.
  Qed.

  Lemma local_phase_base_case_m2 :
    (exists s1 s2,
        local_step 2 (0, 0) = Some s1 /\
        local_step 2 s1 = Some s2 /\
        local_step 2 s2 = None /\
        s2 = (1, 0)) /\
    3 = 2 * 2 - 2 + 1.
  Proof.
    split.
    - apply local_m2_exact_three_step_trace.
    - lia.
  Qed.

  Lemma row_model_total_states_count :
    forall m,
      m > 2 ->
      (m - 1) * (m - 1) + m = m * m - m + 1.
  Proof.
    intros m Hm.
    nia.
  Qed.

  Lemma row_model_non_tie_states_count :
    forall m,
      m > 2 ->
      (m - 1) * (m - 1) + (m - 1) = m * m - m.
  Proof.
    intros m Hm.
    nia.
  Qed.

  Theorem local_row_model_phase_budget_exact :
    forall m,
      m > 2 ->
      ((m - 1) * (m - 1) + (m - 1) = m * m - m) /\
      (S ((m - 1) * (m - 1) + (m - 1)) = LowerBound.phase_term m) /\
      ((m - 1) * (m - 1) + m = LowerBound.phase_term m).
  Proof.
    intros m Hm.
    split.
    - apply row_model_non_tie_states_count; assumption.
    - split.
      + unfold LowerBound.phase_term.
        nia.
      + unfold LowerBound.phase_term.
        apply row_model_total_states_count; assumption.
  Qed.

Theorem local_phase_budget_complete_all_m :
  forall m,
    (m = 1 -> LowerBound.phase_term m = 1) /\
    (m = 2 -> LowerBound.phase_term m = 3) /\
    (m > 2 -> LowerBound.phase_term m = (m - 1) * (m - 1) + m).
Proof.
  intro m.
  split.
  - intro Hm1.
    subst m.
    unfold LowerBound.phase_term.
    lia.
  - split.
    + intro Hm2.
      subst m.
      unfold LowerBound.phase_term.
      lia.
    + intro Hm.
      destruct (local_row_model_phase_budget_exact m Hm) as [_ [_ Hlast]].
      symmetry.
      exact Hlast.
Qed.

Theorem constructive_budget_matches_global_closed_form :
  forall n,
    LowerBound.T n = n * (n * n + 2) / 3.
Proof.
  intro n.
  apply LowerBound.T_closed_form.
Qed.

Definition constructive_phi_global (n : nat) : nat -> nat -> LowerBound.outcome :=
  phi_direct n.

Definition constructive_start (n : nat) : LowerBound.config :=
  {| LowerBound.deck_A := seq 0 n;
     LowerBound.deck_B := seq 0 n |}.

Lemma constructive_start_lengths :
  forall n,
    length (LowerBound.deck_A (constructive_start n)) = n /\
    length (LowerBound.deck_B (constructive_start n)) = n.
Proof.
  intro n.
  unfold constructive_start.
  simpl.
  rewrite !length_seq.
  split; reflexivity.
Qed.

Lemma constructive_phi_global_restricts_to_local :
  forall n m u v,
    m <= n ->
    m >= 2 ->
    u < m ->
    v < m ->
    constructive_phi_global n u (v + (n - m)) = phi_local m u v.
Proof.
  intros n m u v Hmn Hm Hu Hv.
  unfold constructive_phi_global.
  apply phi_direct_restricts_to_local; assumption.
Qed.

Lemma in_constructive_start_deck_A_iff :
  forall n x,
    In x (LowerBound.deck_A (constructive_start n)) <-> x < n.
Proof.
  intros n x.
  unfold constructive_start.
  simpl.
  rewrite in_seq.
  lia.
Qed.

Lemma in_constructive_start_deck_B_iff :
  forall n x,
    In x (LowerBound.deck_B (constructive_start n)) <-> x < n.
Proof.
  intros n x.
  unfold constructive_start.
  simpl.
  rewrite in_seq.
  lia.
Qed.

Theorem local_phase_invariant_package :
  forall m,
    m > 2 ->
    (forall u,
      (u = 0 ->
        (forall v,
          0 <= v <= m - 3 ->
          local_step m (u, v) = Some (u, v + 1)) /\
        local_step m (u, m - 2) = Some (1, m - 1)) /\
      (1 <= u <= m - 2 ->
        (forall v,
          m - u <= v <= m - 1 ->
          local_step m (u, v) = Some (u, (v + 1) mod m)) /\
        (1 <= u <= m - 3 ->
          forall v,
            0 <= v <= m - 3 - u ->
            local_step m (u, v) = Some (u, v + 1)) /\
        local_step m (u, m - 2 - u) = Some (u + 1, m - 1 - u))) /\
    ((forall v,
       1 <= v <= m - 1 ->
       local_step m (m - 1, v) = Some (m - 1, (v + 1) mod m)) /\
      local_step m (m - 1, 0) = None) /\
    (LowerBound.phase_term m = (m - 1) * (m - 1) + m) /\
    ((m - 1) * (m - 1) + (m - 1) = m * m - m).
Proof.
  intros m Hm.
  split.
  - intro u.
    apply local_step_row_phase_interface.
    exact Hm.
  - split.
    + apply local_step_last_row_dynamics_summary.
      exact Hm.
    + destruct (local_row_model_phase_budget_exact m Hm) as [Hnon_tie [_ Hphase]].
      split.
      * symmetry.
        exact Hphase.
      * exact Hnon_tie.
Qed.

(*
  Forward-proof roadmap (axiom-free):
  1) Define one global value-keyed phi and explicit initial decks as functions of n.
  2) Prove a phase invariant: each size-m phase realizes exactly m^2-m non-tie moves,
     then one tie, while preserving a misalignment needed for size-(m-1).
  3) Sum phase lengths with LowerBound.T_closed_form.
*)

End ConstructiveScaffold.
