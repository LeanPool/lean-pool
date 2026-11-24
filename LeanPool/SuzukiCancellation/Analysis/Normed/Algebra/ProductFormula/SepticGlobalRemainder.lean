/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Asymptotics.Pow
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.SepticRemainder
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar remainders retaining seventh-order cancellation

The original centered remainder and the quadratic finite-product term give an
eighth-order global remainder at fixed time along integer step counts.

## Main definitions

* `FQFP.septicGlobalRemainder`: the finite-step remainder without a step restriction.

## Main results

* `FQFP.septicGlobalRemainder_le_pow_eight`: a bound for steps at most one.
* `FQFP.isBigO_septicGlobalRemainder`: fixed-time decay along integer step counts.
-/

@[expose] public noncomputable section

open Filter Asymptotics

namespace FQFP

/-- The centered local remainders and the exact quadratic accumulation term. -/
def septicGlobalRemainder (ℓ μ C D h : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) * septicCenteredRemainder ℓ μ C D h +
    (r : ℝ) * ((r : ℝ) - 1) / 2 * septicStepBound ℓ μ C h ^ 2

/-- The distance bound is controlled by its lowest power for steps at most one. -/
lemma septicStepBound_le_pow_five {ℓ μ C h : ℝ}
    (hμ : 0 ≤ μ) (hC : 0 ≤ C) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    septicStepBound ℓ μ C h ≤ h ^ 5 * (ℓ + μ + C) := by
  unfold septicStepBound
  calc
    _ ≤ h ^ 5 * ℓ + h ^ 5 * μ + h ^ 5 * C := by
      gcongr h ^ 5 * ℓ + ?_ * μ + ?_ * C
      · exact pow_le_pow_of_le_one hh hh1 (by decide : 5 ≤ 7)
      · exact pow_le_pow_of_le_one hh hh1 (by decide : 5 ≤ 9)
    _ = _ := by ring

/-- The complete centered polynomial has ninth-order decay for steps at most one. -/
lemma septicCenteredRemainder_le_pow_nine {ℓ μ C D h : ℝ}
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (hC : 0 ≤ C) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    septicCenteredRemainder ℓ μ C D h ≤
      h ^ 9 * (D + ℓ ^ 2 / 2 + ℓ * μ + (5 * ℓ * C + 7 * μ ^ 2) / 14 +
        7 * μ * C / 16) := by
  unfold septicCenteredRemainder
  calc
    _ ≤ h ^ 9 * D + 1 / 2 * h ^ 9 * ℓ ^ 2 + h ^ 9 * ℓ * μ +
        h ^ 9 / 14 * (5 * ℓ * C + 7 * μ ^ 2) + 7 / 16 * h ^ 9 * μ * C := by
      gcongr h ^ 9 * D + 1 / 2 * ?_ * ℓ ^ 2 + ?_ * ℓ * μ +
        ?_ / 14 * (5 * ℓ * C + 7 * μ ^ 2) + 7 / 16 * ?_ * μ * C
      · exact pow_le_pow_of_le_one hh hh1 (by decide : 9 ≤ 10)
      · exact pow_le_pow_of_le_one hh hh1 (by decide : 9 ≤ 12)
      · exact pow_le_pow_of_le_one hh hh1 (by decide : 9 ≤ 14)
      · exact pow_le_pow_of_le_one hh hh1 (by decide : 9 ≤ 16)
    _ = _ := by ring

/-- At fixed time, the full global remainder is bounded by a fixed multiple
of the eighth power of the step. The finite-step theorem needs no such restriction. -/
theorem septicGlobalRemainder_le_pow_eight {ℓ μ C D t h : ℝ} {r : ℕ}
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (hC : 0 ≤ C) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hr : 1 ≤ r) (ht : (r : ℝ) * h = t) :
    septicGlobalRemainder ℓ μ C D h r ≤ h ^ 8 *
      (t * (D + ℓ ^ 2 / 2 + ℓ * μ + (5 * ℓ * C + 7 * μ ^ 2) / 14 +
        7 * μ * C / 16) + t ^ 2 / 2 * (ℓ + μ + C) ^ 2) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd0 : 0 ≤ septicStepBound ℓ μ C h := by
    unfold septicStepBound
    positivity
  have hquad : (r : ℝ) * ((r : ℝ) - 1) / 2 * septicStepBound ℓ μ C h ^ 2 ≤
      (r : ℝ) ^ 2 / 2 * (h ^ 5 * (ℓ + μ + C)) ^ 2 := by
    gcongr
    · nlinarith
    · exact septicStepBound_le_pow_five hμ hC hh hh1
  unfold septicGlobalRemainder
  calc
    _ ≤ (r : ℝ) * (h ^ 9 *
          (D + ℓ ^ 2 / 2 + ℓ * μ + (5 * ℓ * C + 7 * μ ^ 2) / 14 +
            7 * μ * C / 16)) + (r : ℝ) ^ 2 / 2 * (h ^ 5 * (ℓ + μ + C)) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left
        (septicCenteredRemainder_le_pow_nine hℓ hμ hC hh hh1) (Nat.cast_nonneg _)) hquad
    _ = _ := by
      rw [← ht]
      ring

/-- The eighth-order estimate holds eventually at fixed nonnegative time. -/
theorem eventually_septicGlobalRemainder_le_pow_eight {ℓ μ C t : ℝ} (D : ℝ)
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (hC : 0 ≤ C) (ht : 0 ≤ t) :
    ∀ᶠ r : ℕ in atTop, septicGlobalRemainder ℓ μ C D (t / r) r ≤ (t / r) ^ 8 *
      (t * (D + ℓ ^ 2 / 2 + ℓ * μ + (5 * ℓ * C + 7 * μ ^ 2) / 14 +
        7 * μ * C / 16) + t ^ 2 / 2 * (ℓ + μ + C) ^ 2) := by
  have hsmall := (tendsto_const_div_atTop_nhds_zero_nat t).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop 1] with r hsmall hr
  apply septicGlobalRemainder_le_pow_eight hℓ hμ hC
    (div_nonneg ht (Nat.cast_nonneg r)) hsmall.le hr
  exact mul_div_cancel₀ t (by exact_mod_cast (show r ≠ 0 by lia))

/-- Any sequence dominated by the refined remainder has eighth-order decay
in the inverse integer step count at fixed time. -/
theorem isBigO_inv_nat_pow_eight_of_septicGlobalRemainder
    {E : Type*} [Norm E] (F : ℕ → E) {ℓ μ C t : ℝ} (D : ℝ)
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hF : ∀ r : ℕ, 1 ≤ r → ‖F r‖ ≤ septicGlobalRemainder ℓ μ C D (t / r) r) :
    F =O[atTop] (fun r : ℕ ↦ ((r : ℝ)⁻¹) ^ 8) := by
  have hbound := eventually_septicGlobalRemainder_le_pow_eight D hℓ hμ hC ht
  exact isBigO_inv_nat_pow_of_remainder_le <|
    ((eventually_ge_atTop 1).and hbound).mono fun r ⟨hr, hrem⟩ ↦ (hF r hr).trans hrem

/-- The explicit refined remainder itself is eighth order at fixed time. -/
theorem isBigO_septicGlobalRemainder {ℓ μ C t : ℝ} (D : ℝ)
    (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ) (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    (fun r : ℕ ↦ septicGlobalRemainder ℓ μ C D (t / r) r)
      =O[atTop] (fun r : ℕ ↦ ((r : ℝ)⁻¹) ^ 8) := by
  apply isBigO_inv_nat_pow_eight_of_septicGlobalRemainder _ D hℓ hμ hC ht
  intro r hr
  rw [Real.norm_eq_abs, abs_of_nonneg]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold septicGlobalRemainder septicCenteredRemainder septicStepBound
  positivity

end FQFP
