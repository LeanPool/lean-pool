/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.L4L6
public import LeanPool.CIVAxisymmetric.Closure.SmallnessFromPower
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gkt Smallness

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- Smallness of the `(2/3)`-power of the `L^6` spatial integral follows from the
`L^6` bound over `B(0,ρ)`: lemma `lem:aniso:closure` in arXiv:2609.20803. -/
theorem gkt_smallness_of_l6_bound {u : ParabolicPoint → Vec3} {ρ C β tη : ℝ} (hρ : 0 < ρ) (hC :
    0 ≤ C)
    (hβ : 0 ≤ β ∧ 4 * β < 1) (htη : tη < 0)
    (hbound : ∀ t ∈ Ioo tη 0,
      (∫⁻ x in vec3Ball 0 ρ, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
        ≤ ENNReal.ofReal (C * (-t) ^ (-β))) :
    ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal ε := by
  rcases hβ with ⟨hβ_left, hβ_right⟩
  have h_one_minus_4β_pos : 0 < 1 - 4 * β := by linarith only [hβ_right]
  have hγ_pos : 0 < 2 * (1 - 4 * β) := by nlinarith only [h_one_minus_4β_pos]
  set K : ℝ := C ^ 4 / (1 - 4 * β) with hK_def
  set γ : ℝ := 2 * (1 - 4 * β) with hγ_def
  set r₁ : ℝ := min ρ (Real.sqrt (-tη)) with hr₁_def
  have hr₁_pos : 0 < r₁ := by
    refine lt_min_iff.mpr ⟨hρ, Real.sqrt_pos.mpr (by linarith only [htη])⟩
  have h_bound_transform : ∀ r : ℝ, 0 ≤ r →
      ENNReal.ofReal (C ^ 4 * r ^ (2 * (1 - 4 * β)) / (1 - 4 * β)) =
      ENNReal.ofReal (K * r ^ γ) := by
    intro r hr_nonneg
    congr 1
    dsimp [K, γ]
    ring
  have h_lintegral_bound : ∀ r : ℝ, 0 < r → r ≤ r₁ →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal (K * r ^ γ) := by
    intro r hr_pos hr_le
    have hr_le_ρ : r ≤ ρ := le_trans hr_le (min_le_left _ _)
    have hr_le_sqrt : r ≤ Real.sqrt (-tη) := le_trans hr_le (min_le_right _ _)
    have h_nonneg_r : 0 ≤ r := by linarith only [hr_pos]
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (-tη) := Real.sqrt_nonneg _
    have hrsq_le : r ^ 2 ≤ -tη := by
      have h_sq_le : r ^ 2 ≤ (Real.sqrt (-tη)) ^ 2 := by
        gcongr
      calc
        r ^ 2 ≤ (Real.sqrt (-tη)) ^ 2 := h_sq_le
        _ = -tη := Real.sq_sqrt (by linarith only [htη])
    have h_l4l6 := lintegral_l4l6_le_of_l6_bound hC ⟨hβ_left, hβ_right⟩ hbound r hr_pos hr_le_ρ
      hrsq_le
    have h_eq : ENNReal.ofReal (C ^ 4 * r ^ (2 * (1 - 4 * β)) / (1 - 4 * β)) =
        ENNReal.ofReal (K * r ^ γ) := h_bound_transform r h_nonneg_r
    rw [h_eq] at h_l4l6
    exact h_l4l6
  exact forall_eps_of_le_ofReal_rpow hγ_pos hr₁_pos h_lintegral_bound

end CIV
