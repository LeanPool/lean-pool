/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Lorentz
public import LeanPool.VacuumBellSeparation.FreeField.Existence

/-!
# Boost invariance of the actual positive one-particle measure

The old complex integral identity is strengthened to equality of measures.
The genuine Jacobian theorem applies to arbitrary measurable sets, so the
result supports pullback on the entire one-particle L2 space, without any
integrability or compact-support condition on the input wave function.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

variable {m : ℝ} (hm : 0 < m)

include hm

theorem continuous_shellBoost (η : ℝ) : Continuous (shellBoost m η) :=
  continuous_iff_continuousAt.mpr fun p => (hasFDerivAt_shellBoost hm.ne' η p).continuousAt

theorem shellBoost_jacobian_weight (η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    ENNReal.ofReal |(shellBoostDeriv m η p).det| *
      (oneParticleWeight m (shellBoost m η p) : ℝ≥0∞) = (oneParticleWeight m p : ℝ≥0∞) := by
  have hw : |(shellBoostDeriv m η p).det| *
      (oneParticleWeight m (shellBoost m η p) : ℝ) = (oneParticleWeight m p : ℝ) := by
    have h := congrArg Complex.re (abs_det_shellBoostDeriv_smul hm.ne' η p 1)
    simpa only [one_mul, Complex.smul_re, smul_eq_mul, Complex.ofReal_re,
      oneParticleWeight_coe hm] using h
  calc
    _ = ENNReal.ofReal (|(shellBoostDeriv m η p).det| *
        (oneParticleWeight m (shellBoost m η p) : ℝ)) := by
      rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_coe_nnreal]
    _ = _ := by rw [hw, ENNReal.ofReal_coe_nnreal]

/-- Genuine invariance of the positive measure, including sets of infinite measure. -/
theorem measurePreserving_shellBoost (η : ℝ) :
    MeasurePreserving (shellBoost m η) (oneParticleMeasure m) (oneParticleMeasure m) := by
  have hmeas := (continuous_shellBoost hm η).measurable
  refine ⟨hmeas, ?_⟩
  apply Measure.ext
  intro s hs
  have hpre := hs.preimage hmeas
  rw [Measure.map_apply hmeas hs, oneParticleMeasure,
    withDensity_apply _ hpre, withDensity_apply _ hs]
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hpre
    (fun p hp => (hasFDerivAt_shellBoost hm.ne' η p).hasFDerivWithinAt)
    (shellBoost_injective m η).injOn (fun p => (oneParticleWeight m p : ℝ≥0∞))
  rw [Set.image_preimage_eq s (shellBoost_surjective m η)] at hj
  simpa only [shellBoost_jacobian_weight hm η] using hj.symm

/-- The boost action with the manuscript's inverse-label convention
U(Λη)ψ(p)=ψ(Λ(-η)p), on the complete one-particle Hilbert space. -/
noncomputable def oneParticleBoostIsometry (η : ℝ) :
    Lp ℂ 2 (oneParticleMeasure m) →ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  Lp.compMeasurePreservingₗᵢ ℂ (shellBoost m (-η)) (measurePreserving_shellBoost hm (-η))

theorem oneParticleBoostIsometry_ae (η : ℝ) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleBoostIsometry hm η ψ =ᵐ[oneParticleMeasure m] ψ ∘ shellBoost m (-η) :=
  Lp.coeFn_compMeasurePreserving ψ (measurePreserving_shellBoost hm (-η))

theorem oneParticleBoostIsometry_neg_apply (η : ℝ) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleBoostIsometry hm (-η) (oneParticleBoostIsometry hm η ψ) = ψ := by
  change Lp.compMeasurePreserving (shellBoost m (- -η)) _
    (Lp.compMeasurePreserving (shellBoost m (-η)) _ ψ) = ψ
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hcomp : shellBoost m (-η) ∘ shellBoost m (- -η) = id := by
    funext p
    simp only [Function.comp_apply, neg_neg, shellBoost_neg_shellBoost, id_eq]
  simp only [hcomp, Lp.compMeasurePreserving_id_apply]

/-- Linear isometry equivalence for the one particle boost, of type `Lp ℂ 2 (oneParticleMeasure m)
≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def oneParticleBoost (η : ℝ) :
    Lp ℂ 2 (oneParticleMeasure m) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  LinearIsometryEquiv.ofSurjective (oneParticleBoostIsometry hm η) (by
    intro ψ
    refine ⟨oneParticleBoostIsometry hm (-η) ψ, ?_⟩
    simpa only [neg_neg] using oneParticleBoostIsometry_neg_apply hm (-η) ψ)

end VacuumBellSeparation
