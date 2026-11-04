/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The constant gain `1/40` over `n/3` with the κ-image length gap

Formalizes Theorem S4 of `docs/results/explicit-constant-gain-1-40-2026-10-21.md`: every
injective general-position configuration with `n ≥ 10000` has more than `(1/3 + 1/40) n`
distinct distances.

Suppose `D ≤ (1/3 + 1/40) n`. The configuration then lies in the thin annulus with
`sBar = 41821/50000` (`Setting`), and its mean radial excess `yMean` lies in `[0, W]`,
`W = 1 - sBar²`. The certificate splits `[0, W]` into the cases `[Y_k, Y_{k+1}]`; in each case
the kernel-checked certificate `case<k>_check` and the soundness of the row builder
(`Params.false_of_check`) give a contradiction (`false_of_case`).
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry Esgk.S4

private theorem caseY_zero : caseY.get 0 = 0 := by decide +kernel

private theorem caseY_last : caseY.get 60 = wid := by decide +kernel

/-- Some case of the certificate contains `x ∈ [0, W]`. -/
private theorem exists_case {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ (wid : ℝ)) :
    ∃ k < 60, ((caseY.get k : ℚ) : ℝ) ≤ x ∧ x ≤ ((caseY.get (k + 1) : ℚ) : ℝ) := by
  classical
  let k := Nat.findGreatest (fun j ↦ ((caseY.get j : ℚ) : ℝ) ≤ x) 59
  have hk : k ≤ 59 := Nat.findGreatest_le 59
  have hPk : ((caseY.get k : ℚ) : ℝ) ≤ x :=
    Nat.findGreatest_spec (P := fun j ↦ ((caseY.get j : ℚ) : ℝ) ≤ x) (Nat.zero_le 59)
      (by rw [caseY_zero]; simpa using h0)
  refine ⟨k, by omega, hPk, ?_⟩
  rcases Nat.lt_or_ge k 59 with hlt | hge
  · have := Nat.findGreatest_is_greatest (P := fun j ↦ ((caseY.get j : ℚ) : ℝ) ≤ x)
      (Nat.lt_succ_self k) (by omega)
    exact le_of_lt (not_le.1 this)
  · have hk59 : k = 59 := le_antisymm hk hge
    rw [hk59, caseY_last]
    exact h1

private theorem ybar_nonneg {n : ℕ} (S : Setting n) : 0 ≤ S.ybar := by
  unfold Setting.ybar
  exact div_nonneg (Finset.sum_nonneg fun i _ ↦ radialExcess_nonneg S.hρ S.hlo i)
    (Nat.cast_nonneg n)

private theorem ybar_le_wid {n : ℕ} (S : Setting n) : S.ybar ≤ (wid : ℝ) := by
  unfold Setting.ybar
  have hn : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  have hsum : ∑ i, S.y i ≤ ∑ _i : Fin n, (1 - (sig : ℝ) ^ 2) :=
    Finset.sum_le_sum fun i _ ↦ radialExcess_le S.hρ S.hhi i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [div_le_iff₀ hn]
  have hw : ((wid : ℚ) : ℝ) = 1 - (sig : ℝ) ^ 2 := by
    unfold wid
    push_cast
    ring
  rw [hw]
  linarith

/-- **Constant gain `1/40` with the κ-image length gap** (Theorem S4 of
`docs/results/explicit-constant-gain-1-40-2026-10-21.md`). Every injective
general-position configuration of at least `10000` points has more than
`(1/3 + 1/40) n` distinct distances. -/
theorem numDistances_gt_one_third_add_kappa_image_gap {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hn : 10000 ≤ n) :
    (1 / 3 + 1 / 40) * (n : ℝ) < (NumDistances p : ℝ) := by
  by_contra hnot
  let S : Setting n := ⟨p, hp, hgp, hn, le_of_not_gt hnot⟩
  have hch : params.ChordsHold S := chordConds_hold S
  obtain ⟨k, hk, hlo, hhi⟩ := exists_case (ybar_nonneg S) (ybar_le_wid S)
  exact false_of_case S hch k hk hlo hhi

/-- Every fixed linear bound `A n` with `A ≤ 1/3 + 1/40` fails for all large
general-position configurations. -/
theorem eventually_numDistances_gt_linear_of_le_kappa_image_gap
    (A : ℝ) (hA : A ≤ 1 / 3 + 1 / 40) :
    ∀ᶠ n in Filter.atTop, ∀ p : Config n, Function.Injective p →
      InGeneralPosition (Config.toFinset p) → A * (n : ℝ) < (NumDistances p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop 10000] with n hn
  intro p hp hgp
  have h := numDistances_gt_one_third_add_kappa_image_gap hp hgp hn
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end Esgk
