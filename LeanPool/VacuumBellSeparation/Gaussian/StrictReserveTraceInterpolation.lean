/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ReserveTraceStrip
public import LeanPool.VacuumBellSeparation.Gaussian.LowerPowerSandwich

/-!
# Genuine nuclear interpolation for a strictly positive bounded reserve

Finite sign tests of the actual middle operator recover its full nuclear
trace. Consequently the scalar three-lines argument gives the operator
inequality, with no finite-dimensional reduction or interpolation premise.
The algebraic factorization below is also valid at zero spectral values.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem operatorTraceNorm_strict_reserve_interpolation
    {R B : E →L[ℂ] E} (hR : IsStrictlyPositive R)
    (hcB : IsCompactOperator B) (hB : IsSelfAdjoint B) (htB : operatorTraceNorm B < ∞)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    operatorTraceNorm (R ^ ((1 - θ) / 2) * B * R ^ ((1 - θ) / 2)) ≤
      operatorTraceNorm (R ^ (1 / 2 : ℝ) * B * R ^ (1 / 2 : ℝ)) ^ (1 - θ) *
        operatorTraceNorm B ^ θ := by
  obtain ⟨κ, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  let S := R ^ ((1 - θ) / 2)
  let Z := S * B * S
  have hS : IsSelfAdjoint S := CFC.rpow_nonneg.isSelfAdjoint
  have hcZ : IsCompactOperator Z := (hcB.clm_comp S).comp_clm S
  have hZ : IsSelfAdjoint Z := selfAdjoint_sandwich_isSelfAdjoint hB hS
  have htG := operatorTraceNorm_selfAdjoint_sandwich_lt_top hcB hB htB
    (show IsSelfAdjoint (R ^ (1 / 2 : ℝ)) from CFC.rpow_nonneg.isSelfAdjoint)
  have h := operatorTraceNorm_le_of_finite_tests hcZ hZ (fun s =>
    reserveTraceStrip_finite_test_interpolation b hR hcB hB htB
      (compactSelfAdjointBasis hcZ hZ).orthonormal s
      (fun i => realSpectralSign i.1.re) (fun i _ => (norm_realSpectralSign _).le) hθ)
  apply h.trans_eq
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr hθ.2),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ.1,
    ENNReal.ofReal_toReal htG.ne, ENNReal.ofReal_toReal htB.ne]

theorem reserve_power_interpolation_factorization {R : E →L[ℂ] E}
    (hR : 0 ≤ R) (B : E →L[ℂ] E) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    R ^ (θ / 2) * (R ^ ((1 - θ) / 2) * B * R ^ ((1 - θ) / 2)) * R ^ (θ / 2) =
      R ^ (1 / 2 : ℝ) * B * R ^ (1 / 2 : ℝ) := by
  have ha : 0 ≤ θ / 2 := div_nonneg hθ.1 (by norm_num)
  have hs : 0 ≤ (1 - θ) / 2 := div_nonneg (sub_nonneg.mpr hθ.2) (by norm_num)
  have hl : R ^ (θ / 2) * R ^ ((1 - θ) / 2) = R ^ (1 / 2 : ℝ) := by
    rw [← positiveOperator_rpow_add_nonneg hR ha hs]
    congr 1
    ring
  have hr : R ^ ((1 - θ) / 2) * R ^ (θ / 2) = R ^ (1 / 2 : ℝ) := by
    rw [← positiveOperator_rpow_add_nonneg hR hs ha]
    congr 1
    ring
  calc
    _ = (R ^ (θ / 2) * R ^ ((1 - θ) / 2)) * B *
        (R ^ ((1 - θ) / 2) * R ^ (θ / 2)) := by noncomm_ring
    _ = _ := by rw [hl, hr]

end VacuumBellSeparation.Gaussian
