From Stdlib Require Import List Arith Lia PeanoNat Permutation Program.Equality.

Import ListNotations.

Module DetCDP05.

Inductive outcome := WA | WB | TT | NN.

Definition outcome_eq_dec : forall x y : outcome, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Record config (A B : Type) := {
  deck_A : list A;
  deck_B : list B
}.

Arguments deck_A {A B} _.
Arguments deck_B {A B} _.

Definition tie_weight (o : outcome) : nat :=
  match o with
  | TT => 1
  | _ => 0
  end.

Definition tie_count (os : list outcome) : nat := count_occ outcome_eq_dec os TT.

Definition phase_term (m : nat) : nat := m * m - m + 1.

Fixpoint sum_upto (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => sum_upto f k + f (S k)
  end.

Fixpoint T (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => T k + phase_term (S k)
  end.

Definition move_top_to_bottom {X : Type} (xs : list X) : list X :=
  match xs with
  | [] => []
  | x :: xs' => xs' ++ [x]
  end.

Section PaperCore.

Context {A B : Type}.

Inductive step (phi : A -> B -> outcome) : config A B -> outcome -> config A B -> Prop :=
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

Inductive runs (phi : A -> B -> outcome) : config A B -> list outcome -> config A B -> Prop :=
| RunsNil : forall c,
    runs phi c [] c
| RunsCons : forall c1 c2 c3 o os,
    step phi c1 o c2 ->
    runs phi c2 os c3 ->
    runs phi c1 (o :: os) c3.

Definition game (phi : A -> B -> outcome) (start : config A B) (os : list outcome) : Prop :=
  runs phi start os {| deck_A := []; deck_B := [] |}.

Lemma step_length_accounting :
  forall phi c1 o c2,
    step phi c1 o c2 ->
    length (deck_A c2) + tie_weight o = length (deck_A c1)
    /\ length (deck_B c2) + tie_weight o = length (deck_B c1).
Proof.
  intros phi c1 o c2 Hstep.
  destruct Hstep; simpl; rewrite ?length_app; simpl; split; lia.
Qed.

Lemma tie_count_cons :
  forall o os,
    tie_count (o :: os) = tie_weight o + tie_count os.
Proof.
  intros o os.
  destruct o; reflexivity.
Qed.

Lemma run_length_accounting :
  forall phi c1 os c2,
    runs phi c1 os c2 ->
    length (deck_A c2) + tie_count os = length (deck_A c1)
    /\ length (deck_B c2) + tie_count os = length (deck_B c1).
Proof.
  intros phi c1 os c2 Hrun.
  induction Hrun as [c | c1 c2 c3 o os Hstep Hrun IH].
  - unfold tie_count. simpl. split; apply Nat.add_0_r.
  - destruct (step_length_accounting _ _ _ _ Hstep) as [HA HB].
    destruct IH as [IHA IHB].
    rewrite tie_count_cons.
    simpl in *.
    split; lia.
Qed.

Theorem only_ties_remove_cards :
  forall (phi : A -> B -> outcome) (start : config A B) os n,
    length (deck_A start) = n ->
    length (deck_B start) = n ->
    game phi start os ->
    tie_count os = n.
Proof.
  intros phi start os n HA HB Hgame.
  unfold game in Hgame.
  destruct (run_length_accounting _ _ _ _ Hgame) as [HlenA HlenB].
  simpl in HlenA, HlenB.
  rewrite HA in HlenA.
  rewrite HB in HlenB.
  lia.
Qed.

Definition duel := (A * B * outcome)%type.

Inductive play (phi : A -> B -> outcome) : config A B -> list duel -> config A B -> Prop :=
| PlayNil : forall c,
    play phi c [] c
| PlayWA : forall a as_ b bs tr c,
    phi a b = WA ->
    play phi {| deck_A := a :: as_; deck_B := bs ++ [b] |} tr c ->
    play phi {| deck_A := a :: as_; deck_B := b :: bs |} ((a, b, WA) :: tr) c
| PlayWB : forall a as_ b bs tr c,
    phi a b = WB ->
    play phi {| deck_A := as_ ++ [a]; deck_B := b :: bs |} tr c ->
    play phi {| deck_A := a :: as_; deck_B := b :: bs |} ((a, b, WB) :: tr) c
| PlayTT : forall a as_ b bs tr c,
    phi a b = TT ->
    play phi {| deck_A := as_; deck_B := bs |} tr c ->
    play phi {| deck_A := a :: as_; deck_B := b :: bs |} ((a, b, TT) :: tr) c
| PlayNN : forall a as_ b bs tr c,
    phi a b = NN ->
    play phi {| deck_A := as_ ++ [a]; deck_B := bs ++ [b] |} tr c ->
    play phi {| deck_A := a :: as_; deck_B := b :: bs |} ((a, b, NN) :: tr) c.

Fixpoint tie_pairs (tr : list duel) : list (A * B) :=
  match tr with
  | [] => []
  | (a, b, TT) :: tr' => (a, b) :: tie_pairs tr'
  | _ :: tr' => tie_pairs tr'
  end.

Definition game_trace (phi : A -> B -> outcome) (start : config A B) (tr : list duel) : Prop :=
  play phi start tr {| deck_A := []; deck_B := [] |}.

Definition perfect_matching_on
    (phi : A -> B -> outcome)
    (as_ : list A)
    (bs : list B)
    (ps : list (A * B)) : Prop :=
  Forall (fun p => phi (fst p) (snd p) = TT) ps /\
  Permutation as_ (map fst ps) /\
  Permutation bs (map snd ps) /\
  NoDup (map fst ps) /\
  NoDup (map snd ps).

Lemma perm_move_head_to_tail :
  forall X (x : X) xs,
    Permutation (x :: xs) (xs ++ [x]).
Proof.
  intros X x xs.
  replace (xs ++ [x]) with (xs ++ x :: []) by reflexivity.
  replace (x :: xs) with (x :: xs ++ []) by (rewrite app_nil_r; reflexivity).
  apply Permutation_middle.
Qed.

Lemma play_tie_permutation :
  forall phi c1 tr c2,
    play phi c1 tr c2 ->
    Permutation (deck_A c1) (deck_A c2 ++ map fst (tie_pairs tr)) /\
    Permutation (deck_B c1) (deck_B c2 ++ map snd (tie_pairs tr)).
Proof.
  intros phi c1 tr c2 Hplay.
  induction Hplay as [c | a as_ b bs tr c Hphi Hplay IH | a as_ b bs tr c Hphi Hplay IH
                    | a as_ b bs tr c Hphi Hplay IH | a as_ b bs tr c Hphi Hplay IH].
  - simpl. rewrite !app_nil_r. split; apply Permutation_refl.
  - simpl.
    destruct IH as [IHA IHB].
    split.
    + exact IHA.
    + eapply Permutation_trans.
      * apply perm_move_head_to_tail.
      * exact IHB.
  - simpl.
    destruct IH as [IHA IHB].
    split.
    + eapply Permutation_trans.
      * apply perm_move_head_to_tail.
      * exact IHA.
    + exact IHB.
  - simpl.
    destruct IH as [IHA IHB].
    split.
    + eapply Permutation_trans.
      * apply perm_skip. exact IHA.
      * apply Permutation_middle.
    + eapply Permutation_trans.
      * apply perm_skip. exact IHB.
      * apply Permutation_middle.
  - simpl.
    destruct IH as [IHA IHB].
    split.
    + eapply Permutation_trans.
      * apply perm_move_head_to_tail.
      * exact IHA.
    + eapply Permutation_trans.
      * apply perm_move_head_to_tail.
      * exact IHB.
Qed.

Lemma tie_pairs_are_ties :
  forall phi c1 tr c2,
    play phi c1 tr c2 ->
    Forall (fun p => phi (fst p) (snd p) = TT) (tie_pairs tr).
Proof.
  intros phi c1 tr c2 Hplay.
  induction Hplay as [c | a as_ b bs tr c Hphi Hplay IH | a as_ b bs tr c Hphi Hplay IH
                    | a as_ b bs tr c Hphi Hplay IH | a as_ b bs tr c Hphi Hplay IH].
  - constructor.
  - simpl. exact IH.
  - simpl. exact IH.
  - simpl. constructor; [exact Hphi | exact IH].
  - simpl. exact IH.
Qed.

Lemma nodup_tie_left_unique :
  forall (ps : list (A * B)) (a : A) (b1 b2 : B),
    NoDup (map fst ps) ->
    In (a, b1) ps ->
    In (a, b2) ps ->
    b1 = b2.
Proof.
  intros ps a b1 b2 Hnodup.
  induction ps as [| [a0 b0] ps IH]; intros Hin1 Hin2.
  - inversion Hin1.
  - simpl in Hnodup.
    inversion Hnodup as [| x xs Hnotin Hnodup']; subst x xs.
    simpl in Hin1, Hin2.
    destruct Hin1 as [Heq1 | Hin1].
    + inversion Heq1; subst a0 b0.
      destruct Hin2 as [Heq2 | Hin2].
      * inversion Heq2. reflexivity.
      * exfalso.
        apply Hnotin.
        exact (in_map fst ps (a, b2) Hin2).
    + destruct Hin2 as [Heq2 | Hin2].
      * inversion Heq2; subst a0 b0.
        exfalso.
        apply Hnotin.
        exact (in_map fst ps (a, b1) Hin1).
      * apply IH; assumption.
Qed.

Theorem tie_matching :
  forall (phi : A -> B -> outcome) (start : config A B) tr,
    NoDup (deck_A start) ->
    NoDup (deck_B start) ->
    game_trace phi start tr ->
    perfect_matching_on phi (deck_A start) (deck_B start) (tie_pairs tr).
Proof.
  intros phi start tr HnodupA HnodupB Hgame.
  unfold game_trace in Hgame.
  unfold perfect_matching_on.
  destruct (play_tie_permutation _ _ _ _ Hgame) as [HpermA HpermB].
  split.
  - exact (tie_pairs_are_ties _ _ _ _ Hgame).
  - simpl in HpermA, HpermB.
    split; [exact HpermA |].
    split; [exact HpermB |].
    split.
    + eapply Permutation_NoDup.
      * exact HpermA.
      * exact HnodupA.
    + eapply Permutation_NoDup.
      * exact HpermB.
      * exact HnodupB.
Qed.

Definition duel_outcome (d : duel) : outcome :=
  let '(_, _, o) := d in o.

Definition non_tie_duel (d : duel) : Prop :=
  match duel_outcome d with
  | TT => False
  | _ => True
  end.

Fixpoint rotation_count_A (tr : list duel) : nat :=
  match tr with
  | [] => 0
  | (_, _, WB) :: tr' => S (rotation_count_A tr')
  | (_, _, NN) :: tr' => S (rotation_count_A tr')
  | _ :: tr' => rotation_count_A tr'
  end.

Fixpoint rotation_count_B (tr : list duel) : nat :=
  match tr with
  | [] => 0
  | (_, _, WA) :: tr' => S (rotation_count_B tr')
  | (_, _, NN) :: tr' => S (rotation_count_B tr')
  | _ :: tr' => rotation_count_B tr'
  end.

Lemma iter_move_top_to_bottom_comm :
  forall X (xs : list X) n,
    Nat.iter n move_top_to_bottom (move_top_to_bottom xs) =
    move_top_to_bottom (Nat.iter n move_top_to_bottom xs).
Proof.
  intros X xs n.
  induction n as [| n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma play_non_tie_rotation_counts :
  forall phi c1 tr c2,
    play phi c1 tr c2 ->
    Forall non_tie_duel tr ->
    deck_A c2 = Nat.iter (rotation_count_A tr) move_top_to_bottom (deck_A c1)
    /\
    deck_B c2 = Nat.iter (rotation_count_B tr) move_top_to_bottom (deck_B c1).
Proof.
  intros phi c1 tr c2 Hplay.
  induction Hplay as [c | a as_ b bs tr c Hphi Hplay IH | a as_ b bs tr c Hphi Hplay IH
                    | a as_ b bs tr c Hphi Hplay IH | a as_ b bs tr c Hphi Hplay IH];
    intros Hnon.
  - simpl. split; reflexivity.
  - inversion Hnon as [| ? ? Hhd Htl]; subst.
    destruct (IH Htl) as [IHA IHB].
    simpl in *.
    split.
    + exact IHA.
    + rewrite <- iter_move_top_to_bottom_comm. exact IHB.
  - inversion Hnon as [| ? ? Hhd Htl]; subst.
    destruct (IH Htl) as [IHA IHB].
    simpl in *.
    split.
    + rewrite <- iter_move_top_to_bottom_comm. exact IHA.
    + exact IHB.
  - inversion Hnon as [| ? ? Hhd Htl]; subst.
    simpl in Hhd.
    contradiction.
  - inversion Hnon as [| ? ? Hhd Htl]; subst.
    destruct (IH Htl) as [IHA IHB].
    simpl in *.
    split.
    + rewrite <- iter_move_top_to_bottom_comm. exact IHA.
    + rewrite <- iter_move_top_to_bottom_comm. exact IHB.
Qed.

Theorem cyclic_invariance :
  forall (phi : A -> B -> outcome) (start : config A B) tr c,
    play phi start tr c ->
    Forall non_tie_duel tr ->
    exists i j,
      deck_A c = Nat.iter i move_top_to_bottom (deck_A start)
      /\
      deck_B c = Nat.iter j move_top_to_bottom (deck_B start).
Proof.
  intros phi start tr c Hplay Hnon.
  destruct (play_non_tie_rotation_counts _ _ _ _ Hplay Hnon) as [HA HB].
  exists (rotation_count_A tr), (rotation_count_B tr).
  split; assumption.
Qed.

Definition phase_state
    (initial_A : list A)
    (initial_B : list B)
    (i j : nat)
    (c : config A B) : Prop :=
  deck_A c = Nat.iter i move_top_to_bottom initial_A /\
  deck_B c = Nat.iter j move_top_to_bottom initial_B.

Theorem phase_transition_rule :
  forall (phi : A -> B -> outcome) initial_A initial_B i j c1 o c2,
    phase_state initial_A initial_B i j c1 ->
    step phi c1 o c2 ->
    match o with
    | WA => phase_state initial_A initial_B i (S j) c2
    | WB => phase_state initial_A initial_B (S i) j c2
    | NN => phase_state initial_A initial_B (S i) (S j) c2
    | TT => True
    end.
Proof.
  intros phi initial_A initial_B i j c1 o c2 Hstate Hstep.
  destruct Hstate as [HA HB].
  inversion Hstep; subst; simpl in *.
  - split.
    + exact HA.
    + change (bs ++ [b] = move_top_to_bottom (Nat.iter j move_top_to_bottom initial_B)).
      rewrite <- HB.
      reflexivity.
  - split.
    + change (as_ ++ [a] = move_top_to_bottom (Nat.iter i move_top_to_bottom initial_A)).
      rewrite <- HA.
      reflexivity.
    + exact HB.
  - exact I.
  - split.
    + change (as_ ++ [a] = move_top_to_bottom (Nat.iter i move_top_to_bottom initial_A)).
      rewrite <- HA.
      reflexivity.
    + change (bs ++ [b] = move_top_to_bottom (Nat.iter j move_top_to_bottom initial_B)).
      rewrite <- HB.
      reflexivity.
Qed.

Definition trace_outcomes (tr : list duel) : list outcome :=
  map (fun d => let '(_, _, o) := d in o) tr.

Lemma play_concat :
  forall phi c1 tr1 c2 tr2 c3,
    play phi c1 tr1 c2 ->
    play phi c2 tr2 c3 ->
    play phi c1 (tr1 ++ tr2) c3.
Proof.
  intros phi c1 tr1 c2 tr2 c3 H12 H23.
  induction H12 as [c | a as_ b bs tr c Hphi H12 IH | a as_ b bs tr c Hphi H12 IH
                  | a as_ b bs tr c Hphi H12 IH | a as_ b bs tr c Hphi H12 IH].
  - simpl. exact H23.
  - simpl. apply PlayWA; [exact Hphi | exact (IH H23)].
  - simpl. apply PlayWB; [exact Hphi | exact (IH H23)].
  - simpl. apply PlayTT; [exact Hphi | exact (IH H23)].
  - simpl. apply PlayNN; [exact Hphi | exact (IH H23)].
Qed.

Lemma step_deterministic :
  forall phi c o1 c1 o2 c2,
    step phi c o1 c1 ->
    step phi c o2 c2 ->
    o1 = o2 /\ c1 = c2.
Proof.
  intros phi c o1 c1 o2 c2 Hstep1 Hstep2.
  inversion Hstep1; inversion Hstep2; subst; try congruence;
    repeat match goal with
           | H : {| deck_A := _; deck_B := _ |} = {| deck_A := _; deck_B := _ |} |- _ =>
               inversion H; subst; clear H
           end;
    split; reflexivity.
Qed.

Lemma no_step_from_empty :
  forall phi o c2,
    ~ step phi {| deck_A := []; deck_B := [] |} o c2.
Proof.
  intros phi o c2 Hstep.
  inversion Hstep.
Qed.

Lemma runs_concat :
  forall phi c1 os1 c2 os2 c3,
    runs phi c1 os1 c2 ->
    runs phi c2 os2 c3 ->
    runs phi c1 (os1 ++ os2) c3.
Proof.
  intros phi c1 os1 c2 os2 c3 H12 H23.
  induction H12 as [c | c_start c_mid c_end o os Hstep H12 IH].
  - simpl. exact H23.
  - simpl. apply RunsCons with c_mid.
    + exact Hstep.
    + exact (IH H23).
Qed.

Lemma terminal_runs_deterministic :
  forall phi c os1 os2,
    runs phi c os1 {| deck_A := []; deck_B := [] |} ->
    runs phi c os2 {| deck_A := []; deck_B := [] |} ->
    os1 = os2.
Proof.
  intros phi c os1 os2 Hrun1 Hrun2.
  revert c os2 Hrun1 Hrun2.
  induction os1 as [| o os1 IH]; intros c os2 Hrun1 Hrun2.
  - assert (c = {| deck_A := []; deck_B := [] |}) as Hempty.
    {
      inversion Hrun1; subst; reflexivity.
    }
    subst c.
    inversion Hrun2; subst.
    + reflexivity.
    + exfalso. eapply no_step_from_empty. exact H.
  - inversion Hrun1 as [| c1 c2 c3 o1 os1' Hstep1 Htail1]; subst.
    destruct os2 as [| o2 os2].
    + assert (c = {| deck_A := []; deck_B := [] |}) as Hempty.
      {
        inversion Hrun2; subst; reflexivity.
      }
      rewrite Hempty in Hstep1.
      exfalso. eapply no_step_from_empty. exact Hstep1.
    + inversion Hrun2 as [| ? ? c4 o2' os2' Hstep2 Htail2]; subst.
      destruct (step_deterministic _ _ _ _ _ _ Hstep1 Hstep2) as [Ho Hc].
      subst.
      f_equal.
      eapply IH.
      * exact Htail1.
      * exact Htail2.
Qed.

Lemma play_to_runs :
  forall phi c1 tr c2,
    play phi c1 tr c2 ->
    runs phi c1 (trace_outcomes tr) c2.
Proof.
  intros phi c1 tr c2 Hplay.
  induction Hplay as [c | a as_ b bs tr c Hphi Hplay IH | a as_ b bs tr c Hphi Hplay IH
                    | a as_ b bs tr c Hphi Hplay IH | a as_ b bs tr c Hphi Hplay IH].
  - simpl. apply RunsNil.
  - simpl. apply RunsCons with {| deck_A := a :: as_; deck_B := bs ++ [b] |}.
    + apply StepWA. exact Hphi.
    + exact IH.
  - simpl. apply RunsCons with {| deck_A := as_ ++ [a]; deck_B := b :: bs |}.
    + apply StepWB. exact Hphi.
    + exact IH.
  - simpl. apply RunsCons with {| deck_A := as_; deck_B := bs |}.
    + apply StepTT. exact Hphi.
    + exact IH.
  - simpl. apply RunsCons with {| deck_A := as_ ++ [a]; deck_B := bs ++ [b] |}.
    + apply StepNN. exact Hphi.
    + exact IH.
Qed.

Lemma trace_outcomes_nonempty :
  forall tr,
    tr <> [] ->
    trace_outcomes tr <> [].
Proof.
  intros tr Hne.
  destruct tr as [| d tr'].
  - contradiction.
  - simpl. discriminate.
Qed.

Lemma nonempty_prefix_changes_length :
  forall X (prefix suffix : list X),
    prefix <> [] ->
    prefix ++ suffix <> suffix.
Proof.
  intros X prefix suffix Hne Heq.
  destruct prefix as [| x xs].
  - exfalso. apply Hne. reflexivity.
  - exfalso.
    apply (f_equal (@length X)) in Heq.
    rewrite length_app in Heq.
    simpl in Heq.
    lia.
Qed.

Theorem no_repeated_states_within_phase :
  forall (phi : A -> B -> outcome) (start : config A B) tr,
    game_trace phi start tr ->
    ~ exists prefix cycle suffix mid,
        tr = prefix ++ cycle ++ suffix /\
        cycle <> [] /\
        play phi start prefix mid /\
        play phi mid cycle mid /\
        game_trace phi mid suffix.
Proof.
  intros phi start tr Hgame.
  intros Hrepeat.
  destruct Hrepeat as [prefix [cycle [suffix [mid [Htr [Hcycle [Hpre [Hloop Hsuffix]]]]]]]].
  subst tr.
  pose proof (play_to_runs _ _ _ _ Hloop) as Hrun_loop.
  pose proof (play_to_runs _ _ _ _ Hsuffix) as Hrun_suffix.
  pose proof (runs_concat _ _ _ _ _ _ Hrun_loop Hrun_suffix) as Hrun_cycle_suffix.
  pose proof (terminal_runs_deterministic _ _ _ _ Hrun_suffix Hrun_cycle_suffix) as Hsame.
  apply (nonempty_prefix_changes_length _ (trace_outcomes cycle) (trace_outcomes suffix)).
  - exact (trace_outcomes_nonempty _ Hcycle).
  - symmetry. exact Hsame.
Qed.

End PaperCore.

Definition state := (nat * nat)%type.

Definition bounded_state (m : nat) (s : state) : Prop :=
  fst s < m /\ snd s < m.

Definition phase_space (m : nat) : list state :=
  list_prod (seq 0 m) (seq 0 m).

Lemma bounded_in_phase_space :
  forall m i j,
    i < m ->
    j < m ->
    In (i, j) (phase_space m).
Proof.
  intros m i j Hi Hj.
  unfold phase_space.
  apply in_prod.
  - apply in_seq. lia.
  - apply in_seq. lia.
Qed.

Lemma bounded_list_in_phase_space :
  forall m states,
    Forall (bounded_state m) states ->
    incl states (phase_space m).
Proof.
  intros m states Hbounded s Hin.
  apply Forall_forall with (x := s) in Hbounded; [| exact Hin].
  destruct Hbounded as [Hs1 Hs2].
  destruct s as [i j].
  simpl in *.
  apply bounded_in_phase_space; assumption.
Qed.

Lemma phase_space_length :
  forall m,
    length (phase_space m) = m * m.
Proof.
  intro m.
  unfold phase_space.
  change (length (list_prod (seq 0 m) (seq 0 m)) = m * m).
  rewrite length_prod.
  rewrite !length_seq.
  lia.
Qed.

Theorem phasewise_bound :
  forall m visited forbidden,
    NoDup visited ->
    NoDup forbidden ->
    (forall s, In s visited -> ~ In s forbidden) ->
    Forall (bounded_state m) visited ->
    Forall (bounded_state m) forbidden ->
    length forbidden = m - 1 ->
    length visited <= m * m - m + 1.
Proof.
  intros m visited forbidden HnodupV HnodupF Hdisj HboundedV HboundedF HlenF.
  assert (HnodupVF : NoDup (visited ++ forbidden)).
  {
    apply NoDup_app.
    - exact HnodupV.
    - exact HnodupF.
    - intros s HinV HinF.
      exact (Hdisj s HinV HinF).
  }
  assert (Hincl : incl (visited ++ forbidden) (phase_space m)).
  {
    intros s Hin.
    apply in_app_or in Hin.
    destruct Hin as [HinV | HinF].
    - apply (bounded_list_in_phase_space _ _ HboundedV); exact HinV.
    - apply (bounded_list_in_phase_space _ _ HboundedF); exact HinF.
  }
  pose proof (NoDup_incl_length HnodupVF Hincl) as Hcount.
  rewrite length_app in Hcount.
  rewrite phase_space_length in Hcount.
  rewrite HlenF in Hcount.
  lia.
Qed.

Lemma sum_upto_one :
  forall n,
    sum_upto (fun _ => 1) n = n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma sum_upto_id :
  forall n,
    2 * sum_upto (fun m => m) n = n * (n + 1).
Proof.
  induction n as [| n IH].
  - reflexivity.
  - simpl.
    change (2 * (sum_upto (fun m : nat => m) n + S n) = S n * (S n + 1)).
    rewrite Nat.mul_add_distr_l.
    rewrite IH.
    lia.
Qed.

Lemma sum_upto_square :
  forall n,
    6 * sum_upto (fun m => m * m) n = n * (n + 1) * (2 * n + 1).
Proof.
  induction n as [| n IH].
  - reflexivity.
  - simpl.
    change (6 * (sum_upto (fun m : nat => m * m) n + S n * S n) =
            S n * (S n + 1) * (2 * S n + 1)).
    rewrite Nat.mul_add_distr_l.
    rewrite IH.
    lia.
Qed.

Lemma sum_upto_phase_plus_id :
  forall n,
    sum_upto phase_term n + sum_upto (fun m => m) n =
    sum_upto (fun m => m * m) n + sum_upto (fun _ => 1) n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - simpl.
    replace ((sum_upto phase_term n + phase_term (S n)) + (sum_upto (fun m => m) n + S n))
      with ((sum_upto phase_term n + sum_upto (fun m => m) n) + (phase_term (S n) + S n)) by nia.
    replace ((sum_upto (fun m => m * m) n + S n * S n) + (sum_upto (fun _ => 1) n + 1))
      with ((sum_upto (fun m => m * m) n + sum_upto (fun _ => 1) n) + (S n * S n + 1)) by nia.
    rewrite IH.
    unfold phase_term.
    nia.
Qed.

Theorem upper_bound :
  forall n,
    sum_upto phase_term n = n * (n * n + 2) / 3.
Proof.
  intro n.
  assert (Hdecomp := sum_upto_phase_plus_id n).
  assert (Hsq := sum_upto_square n).
  assert (Hid := sum_upto_id n).
  assert (Hone := sum_upto_one n).
  apply Nat.mul_cancel_l with (p := 3).
  discriminate.
  assert (Hmult : 3 * sum_upto phase_term n = n * (n * n + 2)).
  {
    apply Nat.mul_cancel_l with (p := 2).
    discriminate.
    nia.
  }
  rewrite Hmult.
  apply (proj2 (Nat.Div0.div_exact (n * (n * n + 2)) 3)).
  apply (proj2 (Nat.Lcm0.mod_divide (n * (n * n + 2)) 3)).
  exists (sum_upto phase_term n).
  nia.
Qed.

Lemma T_as_sum_upto :
  forall n,
    T n = sum_upto phase_term n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem T_closed_form :
  forall n,
    T n = n * (n * n + 2) / 3.
Proof.
  intro n.
  rewrite T_as_sum_upto.
  apply upper_bound.
Qed.

Definition phi_direct (n i j : nat) : outcome :=
  if Nat.eqb (i + j) (n - 1) then TT
  else if Nat.eqb (i + j) (n - 2) then NN
  else WA.

Definition phi_local (m u v : nat) : outcome :=
  if Nat.eqb (u + v) (m - 1) then TT
  else if Nat.eqb (u + v) (m - 2) then NN
  else WA.

Theorem table_restriction :
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
  | WA => Some (u, (S v) mod m)
  | NN => Some ((S u) mod m, (S v) mod m)
  | TT => None
  | WB => None
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

Lemma local_m2_exact_three_step_trace :
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
    phi_local m 0 v = WA.
Proof.
  intros m v Hm Hv.
  unfold phi_local.
  simpl.
  destruct (Nat.eqb_spec v (m - 1)) as [Heq1|Hneq1].
  - lia.
  - destruct (Nat.eqb_spec v (m - 2)) as [Heq2|Hneq2].
    + lia.
    + reflexivity.
Qed.

Lemma phi_local_row0_at_boundary_is_NN :
  forall m,
    m > 2 ->
    phi_local m 0 (m - 2) = NN.
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
    phi_local m u v = WA.
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
    phi_local m u v = WA.
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
    phi_local m u (m - 2 - u) = NN.
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

Theorem exact_cardinality_of_row_sets :
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

Lemma phi_local_last_row_nonzero_is_WA :
  forall m v,
    m > 2 ->
    1 <= v <= m - 1 ->
    phi_local m (m - 1) v = WA.
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
    phi_local m (m - 1) 0 = TT.
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

Theorem final_row_dynamics :
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

Theorem small_phase_checks :
  (local_step 1 (0, 0) = None /\ 1 = 1 * 1 - 1 + 1) /\
  ((exists s1 s2,
      local_step 2 (0, 0) = Some s1 /\
      local_step 2 s1 = Some s2 /\
      local_step 2 s2 = None /\
      s2 = (1, 0)) /\
   3 = 2 * 2 - 2 + 1).
Proof.
  split.
  - split.
    + apply local_step_m1_terminates_immediately.
    + lia.
  - split.
    + apply local_m2_exact_three_step_trace.
    + lia.
Qed.

Theorem local_staircase_budget :
  forall m,
    (m = 1 -> phase_term m = 1) /\
    (m = 2 -> phase_term m = 3) /\
    (m > 2 -> phase_term m = (m - 1) * (m - 1) + m).
Proof.
  intro m.
  split.
  - intro Hm1.
    subst m.
    unfold phase_term.
    lia.
  - split.
    + intro Hm2.
      subst m.
      unfold phase_term.
      lia.
    + intro Hm.
      unfold phase_term.
      nia.
Qed.

Lemma move_top_to_bottom_seq_concat :
  forall m k,
    k < m ->
    move_top_to_bottom (seq k (m - k) ++ seq 0 k) =
    seq (S k) (m - S k) ++ seq 0 (S k).
Proof.
  intros m k Hkm.
  assert (Hdecomp : seq k (m - k) = k :: seq (S k) (m - S k)).
  {
    assert (Hlen : m - k = S (m - S k)) by lia.
    rewrite Hlen.
    simpl seq.
    reflexivity.
  }
  rewrite Hdecomp.
  simpl move_top_to_bottom.
  rewrite seq_S.
  replace (0 + k) with k by lia.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma iter_move_top_to_bottom_seq :
  forall m k,
    k <= m ->
    Nat.iter k move_top_to_bottom (seq 0 m) = seq k (m - k) ++ seq 0 k.
Proof.
  intros m k Hkm.
  revert m Hkm.
  induction k as [|k IH]; intros m Hkm.
  - simpl.
    rewrite Nat.sub_0_r.
    simpl.
    now rewrite app_nil_r.
  - simpl.
    rewrite IH by lia.
    apply move_top_to_bottom_seq_concat.
    lia.
Qed.

Theorem accumulated_row_offset :
  forall m,
    m >= 2 ->
    Nat.iter (m - 1) move_top_to_bottom (seq 0 m) =
      (m - 1) :: seq 0 (m - 1).
Proof.
  intros m Hm.
  rewrite iter_move_top_to_bottom_seq by lia.
  replace (m - (m - 1)) with 1 by lia.
  simpl seq.
  reflexivity.
Qed.

Theorem phase_reset :
  forall n m,
    m >= 2 ->
    exists a_tail b_tail,
      phase_term m = m * m - m + 1 /\
      Nat.iter (m - 1) move_top_to_bottom (seq 0 m) = (m - 1) :: a_tail /\
      seq (n - m) m = (n - m) :: b_tail /\
      a_tail = seq 0 (m - 1) /\
      b_tail = seq (n - m + 1) (m - 1).
Proof.
  intros n m Hm.
  exists (seq 0 (m - 1)), (seq (n - m + 1) (m - 1)).
  split.
  - unfold phase_term.
    reflexivity.
  - split.
    + apply accumulated_row_offset.
      exact Hm.
    + split.
      * destruct m as [|m']; [lia|].
        destruct m' as [|m'']; [lia|].
        simpl seq.
        replace (S (n - S (S m''))) with (n - S (S m'') + 1) by lia.
        reflexivity.
      * split; reflexivity.
Qed.

Theorem staircase_closed_form :
  forall n,
    T n = n * (n * n + 2) / 3.
Proof.
  exact T_closed_form.
Qed.

Section PaperAliases.

Context {A B : Type}.

Lemma lem_only_ties_remove_cards :
  forall (phi : A -> B -> outcome) (start : config A B) os n,
    length (deck_A start) = n ->
    length (deck_B start) = n ->
    game phi start os ->
    tie_count os = n.
Proof.
  exact only_ties_remove_cards.
Qed.

Lemma lem_tie_matching :
  forall (phi : A -> B -> outcome) (start : config A B) tr,
    NoDup (deck_A start) ->
    NoDup (deck_B start) ->
    game_trace phi start tr ->
    perfect_matching_on phi (deck_A start) (deck_B start) (tie_pairs tr).
Proof.
  exact tie_matching.
Qed.

Lemma lem_cyclic_invariance :
  forall (phi : A -> B -> outcome) (start : config A B) tr c,
    play phi start tr c ->
    Forall non_tie_duel tr ->
    exists i j,
      deck_A c = Nat.iter i move_top_to_bottom (deck_A start) /\
      deck_B c = Nat.iter j move_top_to_bottom (deck_B start).
Proof.
  exact cyclic_invariance.
Qed.

Lemma lem_phase_transition_rule :
  forall (phi : A -> B -> outcome) initial_A initial_B i j c1 o c2,
    phase_state initial_A initial_B i j c1 ->
    step phi c1 o c2 ->
    match o with
    | WA => phase_state initial_A initial_B i (S j) c2
    | WB => phase_state initial_A initial_B (S i) j c2
    | NN => phase_state initial_A initial_B (S i) (S j) c2
    | TT => True
    end.
Proof.
  exact phase_transition_rule.
Qed.

Lemma lem_no_repeated_states :
  forall (phi : A -> B -> outcome) (start : config A B) tr,
    game_trace phi start tr ->
    ~ exists prefix cycle suffix mid,
        tr = prefix ++ cycle ++ suffix /\
        cycle <> [] /\
        play phi start prefix mid /\
        play phi mid cycle mid /\
        game_trace phi mid suffix.
Proof.
  exact no_repeated_states_within_phase.
Qed.

End PaperAliases.

Lemma thm_phasewise :
  forall m visited forbidden,
    NoDup visited ->
    NoDup forbidden ->
    (forall s, In s visited -> ~ In s forbidden) ->
    Forall (bounded_state m) visited ->
    Forall (bounded_state m) forbidden ->
    length forbidden = m - 1 ->
    length visited <= m * m - m + 1.
Proof.
  exact phasewise_bound.
Qed.

Lemma cor_upper :
  forall n,
    sum_upto phase_term n = n * (n * n + 2) / 3.
Proof.
  exact upper_bound.
Qed.

Lemma lem_restrict :
  forall n m u v,
    m <= n ->
    m >= 2 ->
    u < m ->
    v < m ->
    phi_direct n u (v + (n - m)) = phi_local m u v.
Proof.
  exact table_restriction.
Qed.

Lemma lem_row_dynamics :
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
  exact intermediate_row_dynamics.
Qed.

Lemma lem_final_row :
  forall m,
    m > 2 ->
    (forall v,
      1 <= v <= m - 1 ->
      local_step m (m - 1, v) = Some (m - 1, (v + 1) mod m)) /\
    local_step m (m - 1, 0) = None.
Proof.
  exact final_row_dynamics.
Qed.

Lemma lem_row_cardinality :
  forall m u,
    m > 2 ->
    (0 <= u <= m - 2 -> length (visited_cols_row m u) = m - 1) /\
    (u = m - 1 -> length (visited_cols_row m u) = m).
Proof.
  exact exact_cardinality_of_row_sets.
Qed.

Lemma lem_small_local :
  (local_step 1 (0, 0) = None /\ 1 = 1 * 1 - 1 + 1) /\
  ((exists s1 s2,
      local_step 2 (0, 0) = Some s1 /\
      local_step 2 s1 = Some s2 /\
      local_step 2 s2 = None /\
      s2 = (1, 0)) /\
   3 = 2 * 2 - 2 + 1).
Proof.
  exact small_phase_checks.
Qed.

Lemma lem_row_offset :
  forall m,
    m >= 2 ->
    Nat.iter (m - 1) move_top_to_bottom (seq 0 m) =
      (m - 1) :: seq 0 (m - 1).
Proof.
  exact accumulated_row_offset.
Qed.

Lemma lem_phase_reset :
  forall n m,
    m >= 2 ->
    exists a_tail b_tail,
      phase_term m = m * m - m + 1 /\
      Nat.iter (m - 1) move_top_to_bottom (seq 0 m) = (m - 1) :: a_tail /\
      seq (n - m) m = (n - m) :: b_tail /\
      a_tail = seq 0 (m - 1) /\
      b_tail = seq (n - m + 1) (m - 1).
Proof.
  exact phase_reset.
Qed.

Lemma thm_tight_local_closed_form :
  forall n,
    T n = n * (n * n + 2) / 3.
Proof.
  exact staircase_closed_form.
Qed.

Theorem thm_tight :
  forall n,
    T n = n * (n * n + 2) / 3.
Proof.
  exact thm_tight_local_closed_form.
Qed.

Section MainTheoremScaffold.

Parameter Game_n : nat -> Type.
Parameter dur : forall n, Game_n n -> nat.

Definition main_bound (n : nat) : nat := n * (n * n + 2) / 3.

Definition exact_maximum (n M : nat) : Prop :=
  (forall g : Game_n n, dur n g <= M) /\
  (exists g : Game_n n, dur n g = M).

Definition thm_main_upper_obligation : Prop :=
  forall n (g : Game_n n),
    dur n g <= main_bound n.

Definition thm_main_lower_obligation : Prop :=
  forall n,
    exists g : Game_n n, dur n g = main_bound n.

Theorem thm_main :
  thm_main_upper_obligation ->
  thm_main_lower_obligation ->
  forall n,
    exact_maximum n (main_bound n).
Proof.
  intros Hupper Hlower n.
  unfold exact_maximum.
  split.
  - intros g.
    apply Hupper.
  - apply Hlower.
Qed.

End MainTheoremScaffold.

(*
  This file is standalone and compiles with only the Coq standard library.
  It formalizes the deterministic semantic core, the abstract phasewise upper
  bound, and the local staircase arithmetic/dynamics used in the manuscript.
  It now also contains paper-facing alias names (`lem_*`, `thm_*`, `cor_*`)
  that track the LaTeX labels more closely, including `thm_tight` and an
  obligation-based scaffold `thm_main`.

  The manuscript's final global staircase induction is still not fully
  mechanized here. In particular, the paper statements corresponding to
  monotonic row development, local injectivity, full local staircase traversal,
  the fully dynamic deck-level phase reset, tightness as a terminating game
  construction, and the unconditional final max-duration theorem remain
  separate formalization work.
*)

End DetCDP05.
