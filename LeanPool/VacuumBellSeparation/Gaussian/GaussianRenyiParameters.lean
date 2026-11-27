/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCovariancePerturbation

/-!
# The manuscript's Rényi parameters and numerical perturbation bounds

These scalar identities identify the actual thermal multiplier constant
with max(2,1/τ), and give the bounds δ≤1/8 and ‖Y‖≤2/7 from the source
smallness assumption. No purity differential is assumed here.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped Matrix.Norms.L2Operator

/-- Gaussian Rényi tau given by `(r - 1) / r`. -/
def gaussianRenyiTau (r : ℝ) : ℝ := (r - 1) / r

theorem gaussianRenyiTau_pos {r : ℝ} (hr : 1 < r) : 0 < gaussianRenyiTau r :=
  div_pos (sub_pos.mpr hr) (by linarith)

theorem gaussianRenyiTau_lt_one {r : ℝ} (hr : 1 < r) : gaussianRenyiTau r < 1 := by
  unfold gaussianRenyiTau
  exact (div_lt_one (by linarith : 0 < r)).mpr (by linarith)

theorem mul_one_sub_gaussianRenyiTau {r : ℝ} (hr : 1 < r) :
    r * (1 - gaussianRenyiTau r) = 1 := by
  unfold gaussianRenyiTau
  field_simp [ne_of_gt (show 0 < r by linarith)]
  ring

theorem thermalPerturbationConstant_eq_max {τ : ℝ} (hτ : 0 < τ) :
    thermalPerturbationConstant τ = max 2 τ⁻¹ := by
  unfold thermalPerturbationConstant
  rw [add_max]
  congr 1
  · norm_num
  · field_simp [hτ.ne']
    ring

theorem two_le_thermalPerturbationConstant (τ : ℝ) :
    2 ≤ thermalPerturbationConstant τ := by
  unfold thermalPerturbationConstant
  linarith [le_max_left (1 : ℝ) ((1 - τ) / τ)]

theorem thermal_smallness_bounds {τ δ : ℝ} (hδ₀ : 0 ≤ δ)
    (hδ : δ ≤ (4 * thermalPerturbationConstant τ)⁻¹) :
    δ ≤ 1 / 8 ∧ thermalPerturbationConstant τ * δ / (1 - δ) ≤ 2 / 7 := by
  have hk : 2 ≤ thermalPerturbationConstant τ := two_le_thermalPerturbationConstant τ
  have hk₀ : 0 < thermalPerturbationConstant τ := by linarith
  have hfour : 0 < 4 * thermalPerturbationConstant τ := mul_pos (by norm_num) hk₀
  have hmul : δ * (4 * thermalPerturbationConstant τ) ≤ 1 := by
    exact (le_div_iff₀ hfour).mp (by simpa only [one_div] using hδ)
  have hd : δ ≤ 1 / 8 := by nlinarith
  refine ⟨hd, ?_⟩
  apply (div_le_iff₀ (show 0 < 1 - δ by linarith)).mpr
  nlinarith

theorem thermal_smallness_norm_bounds {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hV : V.IsHermitian)
    (hδ : ‖gaussianRelativePerturbation q τ V‖ ≤
      (4 * thermalPerturbationConstant τ)⁻¹) :
    ‖gaussianRelativePerturbation q τ V‖ ≤ 1 / 8 ∧
      ‖thermalSandwichRelativePerturbation q τ V‖ ≤ 2 / 7 := by
  have hb := thermal_smallness_bounds (norm_nonneg _) hδ
  refine ⟨hb.1, ?_⟩
  have hlt : ‖gaussianRelativePerturbation q τ V‖ < 1 := by linarith [hb.1]
  have hn := norm_thermalSandwichRelativePerturbation_le hq₀ hq₁ hτ₀ hτ₁ hV hlt
  exact hn.trans (by simpa only [mul_div_assoc] using hb.2)

theorem renyi_final_numeric_bound {r k δ η : ℝ}
    (hr : 0 ≤ r) (hk : 2 ≤ k) (hδ : δ ≤ 1 / 8) (hη : η ≤ 2 / 7) :
    r / 2 * ((1 - δ)⁻¹ + k / ((1 - δ) * (1 - η))) ≤ 2 * r * k := by
  have hd : 0 < 1 - δ := by linarith
  have he : 0 < 1 - η := by linarith
  have hdi : (1 - δ)⁻¹ ≤ 8 / 7 := by
    apply (inv_le_iff_one_le_mul₀ hd).mpr
    linarith
  have hprod : 5 / 8 ≤ (1 - δ) * (1 - η) := by
    have := mul_le_mul (show 7 / 8 ≤ 1 - δ by linarith)
      (show 5 / 7 ≤ 1 - η by linarith) (by norm_num : (0 : ℝ) ≤ 5 / 7) hd.le
    nlinarith
  have hkdiv : k / ((1 - δ) * (1 - η)) ≤ 8 * k / 5 := by
    apply (div_le_iff₀ (mul_pos hd he)).mpr
    nlinarith
  have hsum : (1 - δ)⁻¹ + k / ((1 - δ) * (1 - η)) ≤ 4 * k := by
    linarith
  calc
    _ ≤ r / 2 * (4 * k) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end VacuumBellSeparation.Gaussian
