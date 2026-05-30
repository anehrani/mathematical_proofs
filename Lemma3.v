From Stdlib Require Import List.
Require Import Lemma1.
Require Import Lemma2.
Import ListNotations.

Section CyclicInvariance.

Context {A B : Type}.

Notation duelAB := (@duel A B).

Definition move_top_to_bottom {X : Type} (xs : list X) : list X :=
  match xs with
  | [] => []
  | x :: xs' => xs' ++ [x]
  end.

Definition duel_outcome (d : duelAB) : outcome :=
  let '(_, _, o) := d in o.

Definition non_tie_duel (d : duelAB) : Prop :=
  match duel_outcome d with
  | TT => False
  | _ => True
  end.

Fixpoint rotation_count_A (tr : list duelAB) : nat :=
  match tr with
  | [] => 0
  | (_, _, WB) :: tr' => S (rotation_count_A tr')
  | (_, _, NN) :: tr' => S (rotation_count_A tr')
  | _ :: tr' => rotation_count_A tr'
  end.

Fixpoint rotation_count_B (tr : list duelAB) : nat :=
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

Theorem lemma3_cyclic_invariance :
  forall phi start tr c,
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

End CyclicInvariance.