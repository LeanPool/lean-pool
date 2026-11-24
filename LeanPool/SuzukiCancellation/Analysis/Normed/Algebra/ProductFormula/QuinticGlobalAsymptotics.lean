/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Asymptotics.Pow
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ProductFormula.QuinticGlobalRemainder
public import LeanPool.SuzukiCancellation.Analysis.Calculus.TaylorAsymptotics

/-!
# Fixed-time limits from sixth-order global remainders

A uniform sixth-order bound along positive integer step counts gives a sharp
fourth-order global coefficient. A vanishing coefficient gives sixth-order decay.

## Main results

* `FQFP.tendsto_nat_pow_four_mul_norm_of_remainder_le`.
* `FQFP.isBigO_inv_nat_pow_six_of_remainder_le`.
-/

@[expose] public noncomputable section

open Filter Asymptotics
open scoped Topology

namespace FQFP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A sixth-order remainder along integer step counts gives the sharp
fixed-time fourth-order norm coefficient. -/
theorem tendsto_nat_pow_four_mul_norm_of_remainder_le (F : ℕ → E) (K : E)
    (t B : ℝ) (ht : 0 ≤ t)
    (hF : ∀ᶠ n in atTop, ‖F n - (t / n) ^ 4 • K‖ ≤ (t / n) ^ 6 * B) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 4 * ‖F n‖) atTop (𝓝 (t ^ 4 * ‖K‖)) := by
  have hlim : Tendsto (fun n : ℕ ↦ t ^ 4 * (t / n) ^ 2 * B) atTop (𝓝 0) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat t).pow 2).const_mul (t ^ 4)
      |>.mul_const B
  have hvec : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 4 • F n - t ^ 4 • K) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hF, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by lia)
    have heq : (n : ℝ) ^ 4 • F n - t ^ 4 • K =
        (n : ℝ) ^ 4 • (F n - (t / n) ^ 4 • K) := by
      rw [smul_sub, smul_smul]
      congr 1
      congr 1
      field_simp
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (n : ℝ) ^ 4 * ((t / n) ^ 6 * B) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by field_simp
  have hnorm := (hvec.add_const (t ^ 4 • K)).norm
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] using hnorm

omit [NormedSpace ℝ E] in
/-- If the leading operator vanishes, a sixth-order remainder gives
`O(r⁻⁶)` along positive integer step counts. -/
theorem isBigO_inv_nat_pow_six_of_remainder_le (F : ℕ → E) (t B : ℝ)
    (hF : ∀ᶠ n in atTop, ‖F n‖ ≤ (t / n) ^ 6 * B) :
    F =O[atTop] (fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ 6) :=
  isBigO_inv_nat_pow_of_remainder_le hF

/-- The explicit quintic global remainder yields its sharp norm limit along
positive integer step counts. -/
theorem tendsto_nat_pow_four_mul_norm_of_quinticGlobalRemainder (F : ℕ → E) (K : E)
    (ℓ C alpha J t : ℝ) (hℓ : 0 ≤ ℓ) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hF : ∀ n : ℕ, 1 ≤ n → ‖F n - (t / n) ^ 4 • K‖ ≤
      quinticGlobalRemainder ℓ C alpha J t (t / n) n) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 4 * ‖F n‖) Filter.atTop
      (𝓝 (t ^ 4 * ‖K‖)) := by
  obtain ⟨B, hB⟩ := exists_eventually_le_pow_six_of_le_quinticGlobalRemainder hℓ hC ht hF
  exact tendsto_nat_pow_four_mul_norm_of_remainder_le F K t B ht hB

end FQFP
