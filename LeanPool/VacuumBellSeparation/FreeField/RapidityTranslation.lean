/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RapidityFourier

/-!
# Full rapidity translation and the physical boost group

Translations preserve the actual constant multiple of Lebesgue measure.
The complete one-particle boost group is intertwined with translation by
negative rapidity on this L2 space, including arbitrary L2 vectors.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory SchwartzMap
open scoped SchwartzMap

theorem rapidityTranslate_eq_add (η : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    rapidityTranslate η x = x + η • e₁ := by
  ext i
  fin_cases i <;> simp [rapidityTranslate, e₁]

theorem measurePreserving_rapidityShift (η : ℝ) :
    MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 3) => x - η • e₁)
      rapidityMeasure rapidityMeasure := by
  simpa only [rapidityMeasure, sub_eq_add_neg] using
    (measurePreserving_add_right (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (-(η • e₁))).smul_measure rapidityDensity

/-- Linear isometry for the rapidity translation, of type `RapidityL2 →ₗᵢ[ℂ] RapidityL2`. -/
noncomputable def rapidityTranslation (η : ℝ) : RapidityL2 →ₗᵢ[ℂ] RapidityL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x - η • e₁) (measurePreserving_rapidityShift η)

theorem rapidityTranslation_ae (η : ℝ) (f : RapidityL2) :
    rapidityTranslation η f =ᵐ[rapidityMeasure] fun x => f (x - η • e₁) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_rapidityShift η)

theorem rapidityTranslation_toLp (η : ℝ)
    (f : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ)) :
    rapidityTranslation η (f.toLp 2 rapidityMeasure) =
      (f.compSubConstCLM ℂ (η • e₁)).toLp 2 rapidityMeasure := by
  apply Lp.ext
  have hpull := (measurePreserving_rapidityShift η).quasiMeasurePreserving.ae_eq_comp
    (f.coeFn_toLp 2 rapidityMeasure)
  filter_upwards [rapidityTranslation_ae η (f.toLp 2 rapidityMeasure), hpull,
    (f.compSubConstCLM ℂ (η • e₁)).coeFn_toLp 2 rapidityMeasure] with x hx hf ht
  exact hx.trans (hf.trans ht.symm)

theorem rapidityUnitary_boost {m : ℝ} (hm : 0 < m) (η : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    rapidityUnitary hm (oneParticleBoost hm η ψ) =
      rapidityTranslation η (rapidityUnitary hm ψ) := by
  apply Lp.ext
  have hpull := (measurePreserving_rapidityShift η).quasiMeasurePreserving.ae_eq_comp
    (rapidityUnitary_ae hm ψ)
  filter_upwards [rapidityUnitary_boost_ae hm η ψ,
    rapidityTranslation_ae η (rapidityUnitary hm ψ), hpull] with x hx ht hp
  rw [hx, ht]
  simpa only [Function.comp_apply, rapidityTranslate_eq_add, neg_smul,
    sub_eq_add_neg] using hp.symm

end VacuumBellSeparation
