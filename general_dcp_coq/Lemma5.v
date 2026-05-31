From Stdlib Require Import List Arith Lia Program.Equality.
Require Import Lemma1.
Require Import Lemma2.
Import ListNotations.

Section NoRepeatedStates.

Context {A B : Type}.

Notation playAB := (@play A B).
Notation stepAB := (@step A B).
Notation runsAB := (@runs A B).

Definition trace_outcomes (tr : list (@duel A B)) : list outcome :=
  map (fun d => let '(_, _, o) := d in o) tr.

Lemma play_concat :
  forall phi c1 tr1 c2 tr2 c3,
    playAB phi c1 tr1 c2 ->
    playAB phi c2 tr2 c3 ->
    playAB phi c1 (tr1 ++ tr2) c3.
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
    stepAB phi c o1 c1 ->
    stepAB phi c o2 c2 ->
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
    ~ stepAB phi {| deck_A := []; deck_B := [] |} o c2.
Proof.
  intros phi o c2 Hstep.
  inversion Hstep.
Qed.

Lemma runs_concat :
  forall phi c1 os1 c2 os2 c3,
    runsAB phi c1 os1 c2 ->
    runsAB phi c2 os2 c3 ->
    runsAB phi c1 (os1 ++ os2) c3.
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
    runsAB phi c os1 {| deck_A := []; deck_B := [] |} ->
    runsAB phi c os2 {| deck_A := []; deck_B := [] |} ->
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
    playAB phi c1 tr c2 ->
    runsAB phi c1 (trace_outcomes tr) c2.
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

Theorem lemma5_no_repeated_states :
  forall phi start tr,
    game_trace phi start tr ->
    ~ exists prefix cycle suffix mid,
        tr = prefix ++ cycle ++ suffix /\
        cycle <> [] /\
        playAB phi start prefix mid /\
        playAB phi mid cycle mid /\
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

End NoRepeatedStates.