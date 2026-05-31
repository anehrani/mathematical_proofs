From Stdlib Require Import List Arith Lia.
Import ListNotations.

Section CardDuelProcess.

Context {A B : Type}.

Inductive outcome := WA | WB | TT | NN.

Definition outcome_eq_dec : forall x y : outcome, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Record config := {
  deck_A : list A;
  deck_B : list B
}.

Inductive step (phi : A -> B -> outcome) : config -> outcome -> config -> Prop :=
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

Inductive runs (phi : A -> B -> outcome) : config -> list outcome -> config -> Prop :=
| RunsNil : forall c,
    runs phi c [] c
| RunsCons : forall c1 c2 c3 o os,
    step phi c1 o c2 ->
    runs phi c2 os c3 ->
    runs phi c1 (o :: os) c3.

Definition tie_weight (o : outcome) : nat :=
  match o with
  | TT => 1
  | _ => 0
  end.

Definition tie_count (os : list outcome) : nat := count_occ outcome_eq_dec os TT.

Definition terminal (c : config) : Prop :=
  deck_A c = [] /\ deck_B c = [].

Definition game (phi : A -> B -> outcome) (start : config) (os : list outcome) : Prop :=
  runs phi start os {| deck_A := []; deck_B := [] |}.

Lemma step_length_accounting :
  forall phi c1 o c2,
    step phi c1 o c2 ->
    length (deck_A c2) + tie_weight o = length (deck_A c1)
    /\
    length (deck_B c2) + tie_weight o = length (deck_B c1).
Proof.
  intros phi c1 o c2 Hstep.
  destruct Hstep; simpl; rewrite ?length_app; simpl; split; lia.
Qed.

Lemma only_ties_remove_cards :
  forall phi c1 o c2,
    step phi c1 o c2 ->
    ((length (deck_A c2) < length (deck_A c1))
      /\
     (length (deck_B c2) < length (deck_B c1)))
    <-> o = TT.
Proof.
  intros phi c1 o c2 Hstep.
  split.
  - intros Hlt.
    inversion Hstep; subst; simpl in *; rewrite ?length_app in *; simpl in *; try lia; reflexivity.
  - intros Ho.
    subst.
    inversion Hstep; subst; simpl; rewrite ?length_app; simpl; lia.
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
    /\
    length (deck_B c2) + tie_count os = length (deck_B c1).
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

Theorem lemma1_exactly_n_ties :
  forall phi start os n,
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

End CardDuelProcess.