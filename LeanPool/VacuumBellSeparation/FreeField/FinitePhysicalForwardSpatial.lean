/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteForwardRenyiEnvelope
public import LeanPool.VacuumBellSeparation.FreeField.FinitePhysicalGaussianEstimates
public import LeanPool.VacuumBellSeparation.Gaussian.RenyiExponentialEnvelope

/-!
# Uniform forward estimates on the actual finite physical algebras

The constants are independent of mass, physical representation and finite
canonical systems. Actual model existence, source estimates and Rényi
comparison supply both the forward effect inequality and the full complex
contraction covariance bound. Regional exhaustion is a separate step.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal InnerProductSpace Matrix.Norms.L2Operator

theorem exists_uniform_finite_physical_forward (n : ℕ) :
    ∃ Sgeo A Q₀ : ℝ, 0 < Sgeo ∧ 0 < A ∧ 0 < Q₀ ∧
      ∀ (m : ℝ) (hm : 0 < m) (s : ℝ), Sgeo ≤ s →
        A / s ^ 2 ≤ 1 / (8 * ((n + 2 : ℕ) : ℝ)) →
        ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum m H) (U W : Set (EuclideanSpace ℝ (Fin 3))),
          U ⊆ Metric.ball 0 1 → W ⊆ Metric.ball (spatialAxisDisplacement s 0) 1 →
          Disjoint U W → ∀ S T : Submodule ℝ TimeZeroSource,
            IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
            (∀ A₀ ∈ canonicalSourceAlgebra V hm S, ∀ B₀ ∈ canonicalSourceAlgebra V hm T,
              0 ≤ A₀ → A₀ ≤ 1 → 0 ≤ B₀ → B₀ ≤ 1 →
              ENNReal.ofReal (⟪V.vacuum, (A₀ * B₀) V.vacuum⟫_ℂ).re ^ ((n + 2 : ℕ) : ℝ) ≤
                ENNReal.ofReal (Real.exp (8 * ((n + 2 : ℕ) : ℝ) * (A / s ^ 2))) *
                  ENNReal.ofReal ((⟪V.vacuum, A₀ V.vacuum⟫_ℂ).re *
                    (⟪V.vacuum, B₀ V.vacuum⟫_ℂ).re) ^ (((n + 2 : ℕ) : ℝ) - 1)) ∧
            (∀ A₀ ∈ canonicalSourceAlgebra V hm S, ∀ B₀ ∈ canonicalSourceAlgebra V hm T,
              ‖A₀‖ ≤ 1 → ‖B₀‖ ≤ 1 →
              ‖⟪V.vacuum, (A₀ * B₀) V.vacuum⟫_ℂ -
                ⟪V.vacuum, A₀ V.vacuum⟫_ℂ * ⟪V.vacuum, B₀ V.vacuum⟫_ℂ‖ ≤ Q₀ / s) := by
  obtain ⟨Sgeo, A, hSgeo, hA, hbound⟩ := exists_uniform_finite_forward_bounds n
  let r : ℝ := ((n + 2 : ℕ) : ℝ)
  have hr : 2 ≤ r := by
    change (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ)
    exact_mod_cast (show 2 ≤ n + 2 by omega)
  have hr1 : 1 < r := by linarith
  have hr0 : 0 < r := by linarith
  refine ⟨Sgeo, A, 4 * Real.sqrt (r * A), hSgeo, hA, by positivity, ?_⟩
  intro m hm s hs hsmall H _ _ _ V U W hU hW hUW S T hS hT
  have hs0 : 0 < s := hSgeo.trans_le hs
  let _ : FiniteDimensional ℝ ↥(S ⊔ T) := (canonicalSourcePair_sup_isCanonical hUW hS hT).1
  obtain ⟨X⟩ := nonempty_finiteGaussianPairModel hm V S T
    (Metric.isBounded_ball.subset hU) (Metric.isBounded_ball.subset hW) hUW hS hT
  obtain ⟨hop, htrace⟩ := hbound m hm s hs U W hU hW hUW S T hS hT X.modes X.basis
    X.symplectic X.density X.reference X.faithful_reference X.characteristic
      X.reference_characteristic
  have heps : A / s ^ 2 ≤ 1 / 8 := hsmall.trans (by
    change 1 / (8 * r) ≤ (1 / 8 : ℝ)
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)]
    nlinarith)
  obtain ⟨_, _, _, hQ⟩ := finite_high_order_gaussian_renyi_bound
    X.faithful_density X.faithful_reference
    (finiteSourceCovarianceMatrix_isHermitian hm (S ⊔ T) X.basis)
    X.reference_covariance_posDef.isHermitian X.characteristic X.reference_characteristic
    n heps hop htrace
  constructor
  · intro A₀ hA₀ B₀ hB₀ hA0 hA1 hB0 hB1
    have hAB := commuting_canonicalSourceAlgebras hm V S T
      (fun u hu v hv => canonicalSourcePair_cross hUW hS hT hu hv) A₀ hA₀ B₀ hB₀
    exact ((X.effect_renyi_bounds hr1 hA₀ hB₀ hA0 hA1 hB0 hB1 hAB).1).trans
      (_root_.mul_le_mul_left hQ _)
  · intro A₀ hA₀ B₀ hB₀ hAn hBn
    have hcov := X.contraction_covariance_le_renyi hr hA₀ hB₀ hAn hBn
    have hQroot := ENNReal.rpow_le_rpow
      (tsub_le_tsub_right (ENNReal.rpow_le_rpow hQ
        (one_div_nonneg.mpr (sub_pos.mpr hr1).le)) 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hx0 : 0 ≤ 8 * r * (A / s ^ 2) := by positivity
    have hx1 : 8 * r * (A / s ^ 2) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 8 * r by positivity)
      have he : (8 * r) * (1 / (8 * r)) = 1 := by field_simp
      exact h.trans_eq he
    have henv := renyi_exponential_sqrt_envelope hr hx0 hx1
    rw [sqrt_forward_envelope hr0.le hA.le hs0] at henv
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      ((hcov.trans hQroot).trans henv)

end VacuumBellSeparation
