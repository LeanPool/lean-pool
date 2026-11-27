/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalQuantumSandwich
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianPurityPerturbation
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianSandwichPerturbation

/-!
# The actual purity estimate for the noncommuting thermal sandwich

The strict output quantum condition is now proved from the input quantum
condition, and the source smallness hypothesis ensures positive real
covariances along the entire segment. The true aggregate purity estimate
therefore applies to the actual Appendix A covariance without an assumed
endpoint condition or commuting input.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ r : ℝ}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem thermalSandwichCovariance_isHermitian
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hgap : (thermalPowerCovariance q τ - V).PosDef) :
    (thermalSandwichCovariance q τ V).IsHermitian := by
  have hT := thermalPowerCovariance_posDef (fun j => (hq₀ j).le) hq₁ hτ
  have hL := thermalWoodburyFactor_posDef hq₀ hq₁ hτ
  have hconj := hgap.inv.posSemidef.mul_mul_conjTranspose_same (thermalWoodburyFactor q τ)
  rw [hL.isHermitian.eq] at hconj
  exact hT.isHermitian.neg.add hconj.isHermitian

theorem thermalSandwichCovariance_posDef_of_small_relative_norm
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hV : V.IsHermitian)
    (hδ : ‖gaussianRelativePerturbation q τ V‖ ≤
      (4 * thermalPerturbationConstant τ)⁻¹) :
    (thermalSandwichCovariance q τ V).PosDef := by
  have hb := thermal_smallness_norm_bounds hq₀ hq₁ hτ₀ hτ₁ hV hδ
  have hgap := thermal_covariance_gap_posDef_of_relative_norm hq₀ hq₁ hτ₀ hτ₁ hV
    (by linarith [hb.1])
  have hT := thermalPowerCovariance_posDef (fun j => (hq₀ j).le) hq₁ (sub_pos.mpr hτ₁)
  have hK := thermalSandwichCovariance_isHermitian hq₀ hq₁ hτ₀ hgap
  have h := covarianceSegment_posDef hT (hK.sub hT.isHermitian)
    (t := 1) zero_le_one le_rfl (show ‖thermalSandwichRelativePerturbation q τ V‖ < 1 by
      linarith [hb.2])
  have he : thermalPowerCovariance q (1 - τ) +
      (thermalSandwichCovariance q τ V - thermalPowerCovariance q (1 - τ)) =
      thermalSandwichCovariance q τ V := by abel
  simpa only [covarianceSegment, one_smul, he] using h

theorem thermalSandwichCovariance_purity_bound
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hr : 1 < r) (hV : V.IsHermitian)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef)
    (hδ : ‖gaussianRelativePerturbation q τ V‖ ≤
      (4 * thermalPerturbationConstant τ)⁻¹) :
    |covariancePurityTrace r (thermalSandwichCovariance q τ V) -
      covariancePurityTrace r (thermalPowerCovariance q (1 - τ))| ≤
      (r / 2) * (thermalPerturbationConstant τ /
        ((1 - ‖gaussianRelativePerturbation q τ V‖) *
          (1 - ‖thermalSandwichRelativePerturbation q τ V‖))) *
            matrixTraceNorm (gaussianRelativePerturbation q τ V) := by
  have hb := thermal_smallness_norm_bounds hq₀ hq₁ hτ₀ hτ₁ hV hδ
  have hz : ‖gaussianRelativePerturbation q τ V‖ < 1 := by linarith [hb.1]
  have hy : ‖thermalSandwichRelativePerturbation q τ V‖ < 1 := by linarith [hb.2]
  have hgap := thermal_covariance_gap_posDef_of_relative_norm hq₀ hq₁ hτ₀ hτ₁ hV hz
  have hT := thermalPowerCovariance_posDef (fun j => (hq₀ j).le) hq₁ (sub_pos.mpr hτ₁)
  have hK := thermalSandwichCovariance_isHermitian hq₀ hq₁ hτ₀ hgap
  have hQT := thermalPowerCovariance_quantum_posDef hq₀ hq₁ (sub_pos.mpr hτ₁)
  have hQK := (thermalSandwichCovariance_quantum_posDef_iff hq₀ hq₁ hτ₀ hgap).mpr hQ
  let T : RealSymmetricMatrixSpace (Fin m × Fin 2) := ⟨_, hT.isHermitian.isSelfAdjoint⟩
  let Δ : RealSymmetricMatrixSpace (Fin m × Fin 2) := ⟨_, (hK.sub hT.isHermitian).isSelfAdjoint⟩
  have he : thermalPowerCovariance q (1 - τ) +
      (thermalSandwichCovariance q τ V - thermalPowerCovariance q (1 - τ)) =
      thermalSandwichCovariance q τ V := by abel
  have hsegment := covariancePurityTrace_segment_bound hr T Δ hT hQT
    (by simpa only [T, Δ, he] using hQK) hy
  have hs : |covariancePurityTrace r (thermalSandwichCovariance q τ V) -
      covariancePurityTrace r (thermalPowerCovariance q (1 - τ))| ≤
      (r / 2) / (1 - ‖thermalSandwichRelativePerturbation q τ V‖) *
        matrixTraceNorm (thermalSandwichRelativePerturbation q τ V) := by
    simpa only [T, Δ, he, thermalSandwichRelativePerturbation] using hsegment
  have hn := matrixTraceNorm_thermalSandwichRelativePerturbation_le hq₀ hq₁ hτ₀ hτ₁ hV hz
  calc
    _ ≤ (r / 2) / (1 - ‖thermalSandwichRelativePerturbation q τ V‖) *
        (thermalPerturbationConstant τ / (1 - ‖gaussianRelativePerturbation q τ V‖) *
          matrixTraceNorm (gaussianRelativePerturbation q τ V)) :=
      hs.trans (mul_le_mul_of_nonneg_left hn (by positivity))
    _ = _ := by simp only [div_eq_mul_inv, _root_.mul_inv_rev]; ring

end VacuumBellSeparation.Gaussian
