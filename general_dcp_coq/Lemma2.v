From Stdlib Require Import List Lia Permutation.
Require Import Lemma1.
Import ListNotations.

Section TieMatching.

Context {A B : Type}.

Definition duel := (A * B * outcome)%type.

Inductive play (phi : A -> B -> outcome) : config -> list duel -> config -> Prop :=
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

Definition game_trace (phi : A -> B -> outcome) (start : config) (tr : list duel) : Prop :=
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

Theorem lemma2_tie_matching :
  forall phi start tr,
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

Corollary lemma2_unique_tie_for_A :
  forall phi start tr a,
    NoDup (deck_A start) ->
    NoDup (deck_B start) ->
    game_trace phi start tr ->
    In a (deck_A start) ->
    exists! b, In (a, b) (tie_pairs tr).
Proof.
  intros phi start tr a HnodupA HnodupB Hgame HinA.
  destruct (lemma2_tie_matching _ _ _ HnodupA HnodupB Hgame)
    as [_ [HpermA [_ [HpairA _]]]].
  assert (HinMap : In a (map fst (tie_pairs tr))).
  {
    eapply Permutation_in.
    - exact HpermA.
    - exact HinA.
  }
  apply in_map_iff in HinMap.
  destruct HinMap as [[a' b] [Hfst HinPair]].
  simpl in Hfst.
  subst a'.
  exists b.
  split.
  - exact HinPair.
  - intros b' HinPair'.
    eapply nodup_tie_left_unique; eauto.
Qed.

End TieMatching.