/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCovarianceParameters

/-!
# Exact faithfulness criterion for the actual finite-mode density

A pure thermal factor has an explicit nonzero occupation vector in the
kernel. Together with positivity of every weight in the strict domain,
this proves the converse as well as sufficiency of the covariance bound.
Faithfulness means injectivity of the actual infinite-dimensional density.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- A pure mode supplies a genuine nonzero vector killed by the density. -/
theorem multiModeThermalDensity_has_kernel_of_zero_mode {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (j : Fin m) (hj : q j = 0) :
    ∃ x : MultiModeOscillatorSpace m, x ≠ 0 ∧ multiModeThermalDensity q x = 0 := by
  classical
  let k : Fin m → ℕ := Function.update (fun _ => 0) j 1
  have hw : multiModeThermalWeight q k = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [thermalWeight, k, hj]
  refine ⟨multiModeNumberBasis m k, ?_, ?_⟩
  · intro hx
    have hn := (multiModeNumberBasis m).orthonormal.norm_eq_one k
    rw [hx, norm_zero] at hn
    norm_num at hn
  · rw [multiModeThermalDensity_apply_numberBasis hq₀ hq₁, hw, zero_smul]

theorem multiModeThermalDensity_injective_iff {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) :
    Function.Injective (multiModeThermalDensity q) ↔ ∀ j, 0 < q j := by
  constructor
  · intro hinj j
    by_contra hj
    have hz : q j = 0 := le_antisymm (le_of_not_gt hj) (hq₀ j)
    obtain ⟨x, hx, hDx⟩ := multiModeThermalDensity_has_kernel_of_zero_mode hq₀ hq₁ j hz
    exact hx (hinj (hDx.trans (map_zero (multiModeThermalDensity q)).symm))
  · intro hq
    exact (multiModeThermalDensity_isFaithfulDensity hq hq₁).2.2

theorem multiModeThermalDensity_isFaithfulDensity_iff {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) :
    IsFaithfulDensity (multiModeThermalDensity q) ↔ ∀ j, 0 < q j := by
  constructor
  · exact fun h => (multiModeThermalDensity_injective_iff hq₀ hq₁).mp h.2.2
  · exact fun h => multiModeThermalDensity_isFaithfulDensity h hq₁

theorem covarianceThermalParameter_pos_iff {v : ℝ} (hv : 1 / 2 ≤ v) :
    0 < covarianceThermalParameter v ↔ 1 / 2 < v := by
  unfold covarianceThermalParameter
  rw [div_pos_iff_of_pos_right (by linarith : 0 < 2 * v + 1)]
  constructor <;> intro h <;> linarith

/-- The covariance-product density is faithful exactly when every actual
mode variance is strictly larger than the vacuum value. -/
theorem covarianceProductDensity_isFaithfulDensity_iff {m : ℕ} {ν : Fin m → ℝ}
    (hν : ∀ j, 1 / 2 ≤ ν j) :
    IsFaithfulDensity (covarianceProductDensity ν) ↔ ∀ j, 1 / 2 < ν j := by
  rw [covarianceProductDensity, multiModeThermalDensity_isFaithfulDensity_iff
    (fun j => covarianceThermalParameter_nonneg (hν j))
    (fun j => covarianceThermalParameter_lt_one (hν j))]
  exact forall_congr' fun j => covarianceThermalParameter_pos_iff (hν j)

end VacuumBellSeparation.Gaussian
