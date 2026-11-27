/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialForwardReserveFactor
public import LeanPool.VacuumBellSeparation.FreeField.FinitePairForwardNormalization

/-!
# Uniform intrinsic finite Gaussian bounds from the original spatial sources

The actual spatial reserve factor discharges the full-source premise of
the high-order compression theorem. Constants precede all masses, finite
systems and densities. Both norms concern the same intrinsic normalized
power covariance perturbation of the actual density operators.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian Matrix
open scoped ENNReal Matrix.Norms.L2Operator

/-- Source high exponent given by `((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)`. -/
def sourceHighExponent (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)

theorem sourceHighExponent_half_le (n : ℕ) : 1 / 2 ≤ sourceHighExponent n := by
  unfold sourceHighExponent
  rw [le_div_iff₀ (by positivity)]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem sourceHighExponent_lt_one (n : ℕ) : sourceHighExponent n < 1 := by
  unfold sourceHighExponent
  rw [div_lt_one (by positivity)]
  exact_mod_cast (show n + 1 < n + 2 by omega)

theorem sourceHighExponent_thermalConst_inv (n : ℕ) :
    (thermalConst (sourceHighExponent n))⁻¹ = (n + 1 : ℕ) := by
  rw [thermalConst_of_half_le (sourceHighExponent_half_le n)]
  unfold sourceHighExponent
  push_cast
  field_simp
  ring

theorem exists_uniform_finite_forward_bounds (n : ℕ) :
    ∃ Sgeo A : ℝ, 0 < Sgeo ∧ 0 < A ∧
      ∀ (m : ℝ) (hm : 0 < m) (s : ℝ), Sgeo ≤ s →
        ∀ (U W : Set (EuclideanSpace ℝ (Fin 3))),
          U ⊆ Metric.ball 0 1 → W ⊆ Metric.ball (spatialAxisDisplacement s 0) 1 →
          ∀ (hUW : Disjoint U W) (S T : Submodule ℝ TimeZeroSource)
            [FiniteDimensional ℝ ↥(S ⊔ T)]
            (hS : IsCanonicalSourceSystem U S) (hT : IsCanonicalSourceSystem W T)
            (d : ℕ) (c : Module.Basis (Fin d × Fin 2) ℝ (FiniteSourceSpace hm (S ⊔ T))),
            finiteSourceSymplecticMatrix hm (S ⊔ T) c = modeSymplecticForm →
            ∀ (ρ σ : MultiModeOscillatorSpace d →L[ℂ] MultiModeOscillatorSpace d),
              IsFaithfulDensity σ →
              HasGaussianPhysicalCharacteristic ρ (finiteSourceCovarianceMatrix hm (S ⊔ T) c) →
              HasGaussianPhysicalCharacteristic σ
                (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) c)
                  (finiteSourceLabelSubspace hm (S ⊔ T) c S)
                  (finiteSourceLabelSubspace hm (S ⊔ T) c T)
                  (canonicalPairLabel_isCompl hm hUW hS hT c)) →
              ‖intrinsicGaussianRelativePerturbation ρ σ (sourceHighExponent n)‖ ≤ A / s ^ 2 ∧
                matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ (sourceHighExponent n)) ≤
                  A / s ^ 2 := by
  have hb := sourceHighExponent_half_le n
  have hb1 := sourceHighExponent_lt_one n
  have hb0 : 0 < sourceHighExponent n := by linarith
  have hc := thermalConst_pos hb0 hb1
  obtain ⟨Sgeo, F, hSgeo, hF, hbound⟩ := exists_uniform_forward_source_factor hb hb1
  refine ⟨Sgeo, (thermalConst (sourceHighExponent n))⁻¹ * F, hSgeo, by positivity, ?_⟩
  intro m hm s hs U W hU hW hUW S T _ hS hT d c hcanonical ρ σ hσ hGρ hGσ
  obtain ⟨Y, hfac, hcY, hY, hn, htrace, _⟩ := hbound m hm s hs U W hU hW
  obtain ⟨hfinite, hfinite₁⟩ := finitePair_forward_source_factorization_bounds hm hUW hS hT c
    hcanonical hσ hGρ hGσ n hfac hcY hY
  -- Restate both bounds at the named exponent (definitional unfolding of `sourceHighExponent`).
  have hfin : ‖intrinsicGaussianRelativePerturbation ρ σ (sourceHighExponent n)‖ ≤
      (thermalConst (sourceHighExponent n))⁻¹ * ‖Y‖ := hfinite
  have hfin₁ : ENNReal.ofReal
        (matrixTraceNorm (intrinsicGaussianRelativePerturbation ρ σ (sourceHighExponent n))) ≤
      ENNReal.ofReal (thermalConst (sourceHighExponent n))⁻¹ * operatorTraceNorm Y := hfinite₁
  constructor
  · calc
      _ ≤ (thermalConst (sourceHighExponent n))⁻¹ * ‖Y‖ := hfin
      _ ≤ (thermalConst (sourceHighExponent n))⁻¹ * (F / s ^ 2) :=
        mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hc.le)
      _ = (thermalConst (sourceHighExponent n))⁻¹ * F / s ^ 2 := by ring
  · have he := hfin₁.trans
      (_root_.mul_le_mul_right htrace (ENNReal.ofReal (thermalConst (sourceHighExponent n))⁻¹))
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)] at he
    have hh := (ENNReal.ofReal_le_ofReal_iff (show 0 ≤
      (thermalConst (sourceHighExponent n))⁻¹ * (F / s ^ 2) by positivity)).mp he
    calc
      _ ≤ (thermalConst (sourceHighExponent n))⁻¹ * (F / s ^ 2) := hh
      _ = (thermalConst (sourceHighExponent n))⁻¹ * F / s ^ 2 := by ring

end VacuumBellSeparation
