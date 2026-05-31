From Stdlib Require Import Arith Lia.

Section UpperBoundSum.

Fixpoint sum_upto (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => sum_upto f k + f (S k)
  end.

Definition phase_term (m : nat) : nat := m * m - m + 1.

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
Theorem corollary_upper_sum_identity_multiplied :
  forall n,
    3 * sum_upto phase_term n = n * (n * n + 2).
Proof.
  intro n.
  assert (Hdecomp := sum_upto_phase_plus_id n).
  assert (Hsq := sum_upto_square n).
  assert (Hid := sum_upto_id n).
  assert (Hone := sum_upto_one n).
  apply Nat.mul_cancel_l with (p := 2).
  discriminate.
  nia.
Qed.

Theorem corollary_upper_sum_identity :
  forall n,
    sum_upto phase_term n = n * (n * n + 2) / 3.
Proof.
  intro n.
  apply Nat.mul_cancel_l with (p := 3).
  discriminate.
  rewrite corollary_upper_sum_identity_multiplied.
  apply (proj2 (Nat.Div0.div_exact (n * (n * n + 2)) 3)).
  apply (proj2 (Nat.Lcm0.mod_divide (n * (n * n + 2)) 3)).
  exists (sum_upto phase_term n).
  assert (Hmult := corollary_upper_sum_identity_multiplied n).
  nia.
Qed.

End UpperBoundSum.