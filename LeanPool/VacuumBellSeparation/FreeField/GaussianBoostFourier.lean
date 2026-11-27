/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeGaussianAverage
public import LeanPool.VacuumBellSeparation.FreeField.RapidityBoostFourier

/-!
# Exact Gaussian boost average as a physical Fourier multiplier

The standard Gaussian characteristic function fixes every constant. The
Bochner integral is identified by scalar Hilbert pairings and genuine Fubini:
the absolute joint integrand is the L1 product of two actual L2 vectors.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ComplexConjugate ENNReal

/-- Gaussian rapidity coefficient given by `Real.exp (-2 * Real.pi ^ 2 * ε ^ 2 * ⟪e₁, ξ⟫_ℝ ^ 2)`. -/
noncomputable def gaussianRapidityCoefficient (ε : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Real.exp (-2 * Real.pi ^ 2 * ε ^ 2 * ⟪e₁, ξ⟫_ℝ ^ 2)

theorem measurable_gaussianRapidityCoefficient (ε : ℝ) :
    Measurable (gaussianRapidityCoefficient ε) := by
  unfold gaussianRapidityCoefficient
  fun_prop

theorem norm_gaussianRapidityCoefficient_le (ε : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖gaussianRapidityCoefficient ε ξ‖ ≤ 1 := by
  rw [gaussianRapidityCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have h : 0 ≤ 2 * Real.pi ^ 2 * ε ^ 2 * ⟪e₁, ξ⟫_ℝ ^ 2 := by positivity
  nlinarith

theorem memLp_gaussianRapidityCoefficient (ε : ℝ) :
    MemLp (gaussianRapidityCoefficient ε) ⊤ rapidityMeasure :=
  memLp_top_of_bound (measurable_gaussianRapidityCoefficient ε).aestronglyMeasurable 1
    (Eventually.of_forall (norm_gaussianRapidityCoefficient_le ε))

/-- Continuous linear map for the gaussian rapidity multiplier, of type `RapidityL2 →L[ℂ]
RapidityL2`. -/
noncomputable def gaussianRapidityMultiplier (ε : ℝ) : RapidityL2 →L[ℂ] RapidityL2 :=
  lpMultiplication rapidityMeasure (gaussianRapidityCoefficient ε)
    (memLp_gaussianRapidityCoefficient ε)

theorem integral_gaussian_rapidityBoostPhase (ε : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    (∫ t : ℝ, rapidityBoostPhase (ε * t) ξ ∂gaussianReal 0 1) = gaussianRapidityCoefficient ε ξ
      := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) (-2 * Real.pi * ε * ⟪e₁, ξ⟫_ℝ)
  rw [charFun_apply_real] at h
  have he : (fun t : ℝ => rapidityBoostPhase (ε * t) ξ) =
      fun t : ℝ => Complex.exp ((((-2 * Real.pi * ε * ⟪e₁, ξ⟫_ℝ) : ℝ) : ℂ) * t * Complex.I) := by
    funext t
    unfold rapidityBoostPhase
    congr 1
    push_cast
    ring
  rw [he, h, gaussianRapidityCoefficient, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem oneParticleRapidityFourier_gaussianBoostAverage {m : ℝ} (hm : 0 < m) (ε : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleRapidityFourier hm (gaussianBoostAverage hm ε ψ) =
      gaussianRapidityMultiplier ε (oneParticleRapidityFourier hm ψ) := by
  let V := oneParticleRapidityFourier hm
  let f := V ψ
  have hint : Integrable (fun t : ℝ => rapidityBoostMultiplier (ε * t) f) (gaussianReal 0 1) := by
    have h := (V.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (integrable_gaussian_boost hm ε ψ))
    change Integrable (fun t : ℝ => V (oneParticleBoost hm (ε * t) ψ))
      (gaussianReal 0 1) at h
    exact h.congr (Eventually.of_forall fun t =>
      oneParticleRapidityFourier_boost hm (ε * t) ψ)
  have he : V (gaussianBoostAverage hm ε ψ) =
      ∫ t : ℝ, rapidityBoostMultiplier (ε * t) f ∂gaussianReal 0 1 := by
    calc
      V (gaussianBoostAverage hm ε ψ) =
          ∫ t : ℝ, V (oneParticleBoost hm (ε * t) ψ) ∂gaussianReal 0 1 := by
        rw [gaussianBoostAverage_apply]
        exact (V.toLinearIsometry.integral_comp_comm _).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun t =>
        oneParticleRapidityFourier_boost hm (ε * t) ψ)
  rw [he]
  apply ext_inner_left ℂ
  intro v
  rw [← integral_inner hint v]
  have hprod : Integrable (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
      conj (v q.2) * (rapidityBoostPhase (ε * q.1) q.2 * f q.2))
      ((gaussianReal 0 1).prod rapidityMeasure) := by
    have hbase := (L2.integrable_inner (𝕜 := ℂ) v f).norm.comp_snd (gaussianReal 0 1)
    apply hbase.mono'
    · have hf : Measurable (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => f q.2) :=
        (Lp.stronglyMeasurable f).measurable.comp measurable_snd
      have hv : Measurable (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => conj (v q.2)) :=
        Complex.continuous_conj.measurable.comp
          ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)
      have hp : Measurable (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
          rapidityBoostPhase (ε * q.1) q.2) := by
        unfold rapidityBoostPhase
        fun_prop
      exact (hv.mul (hp.mul hf)).aestronglyMeasurable
    · exact Eventually.of_forall fun q => by
        simp only [norm_mul, Complex.norm_conj, norm_rapidityBoostPhase, one_mul,
          RCLike.inner_apply']
        exact le_rfl
  calc
    (∫ t : ℝ, inner ℂ v (rapidityBoostMultiplier (ε * t) f) ∂gaussianReal 0 1) =
        ∫ t : ℝ, ∫ ξ, conj (v ξ) * (rapidityBoostPhase (ε * t) ξ * f ξ) ∂rapidityMeasure
          ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp only
        rw [L2.inner_def]
        unfold rapidityBoostMultiplier
        apply integral_congr_ae
        filter_upwards [lpMultiplication_ae rapidityMeasure (rapidityBoostPhase (ε * t))
          (memLp_rapidityBoostPhase (ε * t)) f] with ξ hξ
        rw [hξ, RCLike.inner_apply']
    _ = ∫ ξ, ∫ t : ℝ, conj (v ξ) * (rapidityBoostPhase (ε * t) ξ * f ξ)
        ∂gaussianReal 0 1 ∂rapidityMeasure := integral_integral_swap hprod
    _ = ∫ ξ, conj (v ξ) * (gaussianRapidityCoefficient ε ξ * f ξ) ∂rapidityMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by
        dsimp only
        rw [integral_const_mul, integral_mul_const, integral_gaussian_rapidityBoostPhase]
    _ = inner ℂ v (gaussianRapidityMultiplier ε f) := by
      rw [L2.inner_def]
      unfold gaussianRapidityMultiplier
      apply integral_congr_ae
      filter_upwards [lpMultiplication_ae rapidityMeasure (gaussianRapidityCoefficient ε)
        (memLp_gaussianRapidityCoefficient ε) f] with ξ hξ
      rw [hξ, RCLike.inner_apply']

end VacuumBellSeparation
