/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RapidityTranslation
public import LeanPool.VacuumBellSeparation.FreeField.LpMultiplication

/-!
# Exact Fourier diagonalization of the physical boost group

The pinned normalized Fourier transform has kernel exp(-2πi x·ξ).
Translation by negative rapidity therefore has multiplier
exp(-2πi η ξ₁). The identity is extended from actual Schwartz functions
to the complete physical one-particle space by density and boundedness.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory SchwartzMap FourierTransform
open scoped SchwartzMap FourierTransform InnerProductSpace ENNReal

/-- Rapidity boost phase given by `Complex.exp ((-2 * Real.pi * η * ⟪e₁, ξ⟫_ℝ : ℝ) * Complex.I)`. -/
noncomputable def rapidityBoostPhase (η : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp ((-2 * Real.pi * η * ⟪e₁, ξ⟫_ℝ : ℝ) * Complex.I)

theorem measurable_rapidityBoostPhase (η : ℝ) : Measurable (rapidityBoostPhase η) := by
  unfold rapidityBoostPhase
  fun_prop

theorem norm_rapidityBoostPhase (η : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖rapidityBoostPhase η ξ‖ = 1 := by
  rw [rapidityBoostPhase, Complex.norm_exp]
  simp

theorem memLp_rapidityBoostPhase (η : ℝ) : MemLp (rapidityBoostPhase η) ⊤ rapidityMeasure :=
  memLp_top_of_bound (measurable_rapidityBoostPhase η).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ξ => (norm_rapidityBoostPhase η ξ).le)

/-- Continuous linear map for the rapidity boost multiplier, of type `RapidityL2 →L[ℂ]
RapidityL2`. -/
noncomputable def rapidityBoostMultiplier (η : ℝ) : RapidityL2 →L[ℂ] RapidityL2 :=
  lpMultiplication rapidityMeasure (rapidityBoostPhase η) (memLp_rapidityBoostPhase η)

theorem fourier_compSubConst_rapidity (η : ℝ)
    (f : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ)) (ξ : EuclideanSpace ℝ (Fin 3)) :
    𝓕 (f.compSubConstCLM ℂ (η • e₁)) ξ = rapidityBoostPhase η ξ * 𝓕 f ξ := by
  have hf : (f.compSubConstCLM ℂ (η • e₁) : EuclideanSpace ℝ (Fin 3) → ℂ) =
      (f : EuclideanSpace ℝ (Fin 3) → ℂ) ∘ (fun x => x + -(η • e₁)) := by
    funext x
    simp only [compSubConstCLM_apply, Function.comp_apply, sub_eq_add_neg]
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ (EuclideanSpace ℝ (Fin 3))) (f : EuclideanSpace ℝ (Fin 3) → ℂ) (-(η • e₁))) ξ
  rw [← hf] at h
  change 𝓕 (f.compSubConstCLM ℂ (η • e₁)) ξ =
    Real.fourierChar ⟪-(η • e₁), ξ⟫_ℝ • 𝓕 f ξ at h
  rw [inner_neg_left, real_inner_smul_left, Circle.smul_def, Real.fourierChar_apply,
    smul_eq_mul] at h
  have he : 2 * Real.pi * -(η * ⟪e₁, ξ⟫_ℝ) = -2 * Real.pi * η * ⟪e₁, ξ⟫_ℝ := by ring
  simpa only [he, rapidityBoostPhase] using h

theorem rapidityFourier_translation_toLp (η : ℝ)
    (f : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ)) :
    rapidityFourier (rapidityTranslation η (f.toLp 2 rapidityMeasure)) =
      rapidityBoostMultiplier η (rapidityFourier (f.toLp 2 rapidityMeasure)) := by
  rw [rapidityTranslation_toLp, rapidityFourier_toLp, rapidityFourier_toLp,
    rapidityBoostMultiplier]
  apply Lp.ext
  filter_upwards [(𝓕 (f.compSubConstCLM ℂ (η • e₁))).coeFn_toLp 2 rapidityMeasure,
    lpMultiplication_ae rapidityMeasure (rapidityBoostPhase η) (memLp_rapidityBoostPhase η)
      ((𝓕 f).toLp 2 rapidityMeasure), (𝓕 f).coeFn_toLp 2 rapidityMeasure]
    with ξ hf hm hbase
  rw [hf, hm, hbase, fourier_compSubConst_rapidity]

theorem rapidityFourier_translation (η : ℝ) (f : RapidityL2) :
    rapidityFourier (rapidityTranslation η f) =
      rapidityBoostMultiplier η (rapidityFourier f) := by
  have hd : DenseRange (fun g : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ) =>
      g.toLp 2 rapidityMeasure) := denseRange_toLpCLM ENNReal.ofNat_ne_top
  refine hd.induction_on (p := fun g => rapidityFourier (rapidityTranslation η g) =
    rapidityBoostMultiplier η (rapidityFourier g)) f ?_ ?_
  · exact isClosed_eq (rapidityFourier.continuous.comp (rapidityTranslation η).continuous)
      ((rapidityBoostMultiplier η).continuous.comp rapidityFourier.continuous)
  · exact rapidityFourier_translation_toLp η

/-- The full physical boost group with the exact Fourier normalization. -/
theorem oneParticleRapidityFourier_boost {m : ℝ} (hm : 0 < m) (η : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleRapidityFourier hm (oneParticleBoost hm η ψ) =
      rapidityBoostMultiplier η (oneParticleRapidityFourier hm ψ) := by
  change rapidityFourier (rapidityUnitary hm (oneParticleBoost hm η ψ)) =
    rapidityBoostMultiplier η (rapidityFourier (rapidityUnitary hm ψ))
  rw [rapidityUnitary_boost, rapidityFourier_translation]

end VacuumBellSeparation
