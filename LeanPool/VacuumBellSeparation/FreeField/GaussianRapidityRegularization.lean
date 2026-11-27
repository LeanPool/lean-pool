/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.GaussianBoostFourier
public import LeanPool.VacuumBellSeparation.FreeField.PhysicalRapidityExponential

/-!
# Bounded regularization of the full maximal rapidity half-power

For every nonzero Gaussian width the full product exp(-2π²ξ₁) exp(-2π²ε²ξ₁²)
is bounded by exp(π²/(2ε²)). Its actual bounded multiplication operator supplies
an intermediate vector in the maximal half-power graph for every physical ψ.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter
open scoped InnerProductSpace ENNReal

/-- Gaussian half coefficient given by `Real.exp (-2 * Real.pi ^ 2 * ⟪e₁, ξ⟫_ℝ - 2 * Real.pi ^ 2 *
ε ^ 2 * ⟪e₁, ξ⟫_ℝ ^ 2)`. -/
noncomputable def gaussianHalfCoefficient (ε : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Real.exp (-2 * Real.pi ^ 2 * ⟪e₁, ξ⟫_ℝ - 2 * Real.pi ^ 2 * ε ^ 2 * ⟪e₁, ξ⟫_ℝ ^ 2)

theorem gaussianHalfCoefficient_eq (ε : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    gaussianHalfCoefficient ε ξ = (Real.exp (rapidityFrequencyExponent (1 / 2) ξ) : ℂ) *
      gaussianRapidityCoefficient ε ξ := by
  unfold gaussianHalfCoefficient gaussianRapidityCoefficient rapidityFrequencyExponent
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem norm_gaussianHalfCoefficient_le {ε : ℝ} (hε : ε ≠ 0)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖gaussianHalfCoefficient ε ξ‖ ≤ Real.exp (Real.pi ^ 2 / (2 * ε ^ 2)) := by
  rw [gaussianHalfCoefficient, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have he : -2 * Real.pi ^ 2 * ⟪e₁, ξ⟫_ℝ - 2 * Real.pi ^ 2 * ε ^ 2 * ⟪e₁, ξ⟫_ℝ ^ 2 =
      Real.pi ^ 2 / (2 * ε ^ 2) - 2 * Real.pi ^ 2 * (ε * ⟪e₁, ξ⟫_ℝ + 1 / (2 * ε)) ^ 2 := by
    field_simp [hε]
    ring
  rw [he]
  exact sub_le_self _ (by positivity)

theorem memLp_gaussianHalfCoefficient {ε : ℝ} (hε : ε ≠ 0) :
    MemLp (gaussianHalfCoefficient ε) ⊤ rapidityMeasure := by
  have hm : Measurable (gaussianHalfCoefficient ε) := by unfold gaussianHalfCoefficient; fun_prop
  exact memLp_top_of_bound hm.aestronglyMeasurable (Real.exp (Real.pi ^ 2 / (2 * ε ^ 2)))
    (Eventually.of_forall (norm_gaussianHalfCoefficient_le hε))

/-- Continuous linear map for the gaussian half multiplier, of type `RapidityL2 →L[ℂ]
RapidityL2`. -/
noncomputable def gaussianHalfMultiplier {ε : ℝ} (hε : ε ≠ 0) : RapidityL2 →L[ℂ] RapidityL2 :=
  lpMultiplication rapidityMeasure (gaussianHalfCoefficient ε) (memLp_gaussianHalfCoefficient hε)

/-- Continuous linear map for the physical Gaussian half, of type `Lp ℂ 2 (oneParticleMeasure m)
→L[ℂ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def physicalGaussianHalf {m : ℝ} (hm : 0 < m) {ε : ℝ} (hε : ε ≠ 0) :
    Lp ℂ 2 (oneParticleMeasure m) →L[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  (oneParticleRapidityFourier hm).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((gaussianHalfMultiplier hε).comp
      (oneParticleRapidityFourier hm).toContinuousLinearEquiv.toContinuousLinearMap)

theorem gaussianBoostAverage_mem_physicalHalf_graph {m : ℝ} (hm : 0 < m) {ε : ℝ}
    (hε : ε ≠ 0) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    (gaussianBoostAverage hm ε ψ, physicalGaussianHalf hm hε ψ) ∈
      (physicalRapidityExponential hm (1 / 2)).graph := by
  rw [physicalRapidityExponential_mem_graph, oneParticleRapidityFourier_gaussianBoostAverage]
  have he : oneParticleRapidityFourier hm (physicalGaussianHalf hm hε ψ) =
      gaussianHalfMultiplier hε (oneParticleRapidityFourier hm ψ) := by
    change oneParticleRapidityFourier hm ((oneParticleRapidityFourier hm).symm
      (gaussianHalfMultiplier hε (oneParticleRapidityFourier hm ψ))) = _
    exact (oneParticleRapidityFourier hm).apply_symm_apply _
  rw [he]
  filter_upwards [lpMultiplication_ae rapidityMeasure (gaussianHalfCoefficient ε)
    (memLp_gaussianHalfCoefficient hε) (oneParticleRapidityFourier hm ψ),
    lpMultiplication_ae rapidityMeasure (gaussianRapidityCoefficient ε)
      (memLp_gaussianRapidityCoefficient ε) (oneParticleRapidityFourier hm ψ)] with ξ hh hg
  change (lpMultiplication rapidityMeasure (gaussianHalfCoefficient ε)
    (memLp_gaussianHalfCoefficient hε) (oneParticleRapidityFourier hm ψ)) ξ =
      (Real.exp (rapidityFrequencyExponent (1 / 2) ξ) : ℂ) *
        (lpMultiplication rapidityMeasure (gaussianRapidityCoefficient ε)
          (memLp_gaussianRapidityCoefficient ε) (oneParticleRapidityFourier hm ψ)) ξ
  rw [hh, hg, gaussianHalfCoefficient_eq, mul_assoc]

theorem gaussianBoostAverage_preserves_physicalHalf_graph {m : ℝ} (hm : 0 < m) (ε : ℝ)
    {ψ χ : Lp ℂ 2 (oneParticleMeasure m)}
    (hψχ : (ψ, χ) ∈ (physicalRapidityExponential hm (1 / 2)).graph) :
    (gaussianBoostAverage hm ε ψ, gaussianBoostAverage hm ε χ) ∈
      (physicalRapidityExponential hm (1 / 2)).graph := by
  rw [physicalRapidityExponential_mem_graph] at hψχ ⊢
  rw [oneParticleRapidityFourier_gaussianBoostAverage,
    oneParticleRapidityFourier_gaussianBoostAverage]
  filter_upwards [hψχ, lpMultiplication_ae rapidityMeasure (gaussianRapidityCoefficient ε)
    (memLp_gaussianRapidityCoefficient ε) (oneParticleRapidityFourier hm ψ),
    lpMultiplication_ae rapidityMeasure (gaussianRapidityCoefficient ε)
      (memLp_gaussianRapidityCoefficient ε) (oneParticleRapidityFourier hm χ)] with ξ h hh hg
  change (lpMultiplication rapidityMeasure (gaussianRapidityCoefficient ε)
    (memLp_gaussianRapidityCoefficient ε) (oneParticleRapidityFourier hm χ)) ξ =
      (Real.exp (rapidityFrequencyExponent (1 / 2) ξ) : ℂ) *
        (lpMultiplication rapidityMeasure (gaussianRapidityCoefficient ε)
          (memLp_gaussianRapidityCoefficient ε) (oneParticleRapidityFourier hm ψ)) ξ
  rw [hh, hg, h]
  ring

end VacuumBellSeparation
