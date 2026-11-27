/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeWaveL2

/-!
# Actual antiunitary wedge reflection on the full physical Hilbert space

Jψ(p)=conj(ψ(p₁,-p₂,-p₃)). Measure preservation uses the true positive mass-shell
density. The construction is a bounded real-linear map with proved involution,
norm preservation and complex antilinearity.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

theorem measurePreserving_massShell_rotation {m : ℝ} (hm : 0 < m)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    MeasurePreserving R (oneParticleMeasure m) (oneParticleMeasure m) := by
  refine ⟨R.continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply R.continuous.measurable hs, oneParticleMeasure,
    withDensity_apply _ (hs.preimage R.continuous.measurable), withDensity_apply _ hs]
  have h := R.measurePreserving.setLIntegral_comp_preimage hs
    ((measurable_oneParticleWeight hm).coe_nnreal_ennreal)
  simpa only [oneParticleWeight, dispersion_linearIsometryEquiv] using h

/-- Continuous linear map for the physical wedge reflection, of type `Lp ℂ 2 (oneParticleMeasure m)
→L[ℝ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def physicalWedgeReflection {m : ℝ} (hm : 0 < m) :
    Lp ℂ 2 (oneParticleMeasure m) →L[ℝ] Lp ℂ 2 (oneParticleMeasure m) :=
  let reflected := (Lp.compMeasurePreservingₗᵢ ℂ axisReflection
    (measurePreserving_massShell_rotation hm axisReflection)).toContinuousLinearMap
  (Complex.conjCLE.toContinuousLinearMap.compLpL 2 (oneParticleMeasure m)).comp
    (reflected.restrictScalars ℝ)

theorem physicalWedgeReflection_ae {m : ℝ} (hm : 0 < m)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    physicalWedgeReflection hm ψ =ᵐ[oneParticleMeasure m] fun p => conj (ψ (axisReflection p)) := by
  filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL
    (Lp.compMeasurePreserving axisReflection (measurePreserving_massShell_rotation hm
      axisReflection) ψ),
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_massShell_rotation hm axisReflection)]
    with p hc hr
  exact hc.trans (by rw [hr]; rfl)

theorem axisReflection_involutive (p : EuclideanSpace ℝ (Fin 3)) :
    axisReflection (axisReflection p) = p := axisReflection_aux_involutive p

theorem physicalWedgeReflection_involutive {m : ℝ} (hm : 0 < m)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    physicalWedgeReflection hm (physicalWedgeReflection hm ψ) = ψ := by
  apply Lp.ext
  have hpull := (measurePreserving_massShell_rotation hm
    axisReflection).quasiMeasurePreserving.ae_eq_comp
    (physicalWedgeReflection_ae hm ψ)
  filter_upwards [physicalWedgeReflection_ae hm (physicalWedgeReflection hm ψ), hpull]
    with p h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, axisReflection_involutive, Complex.conj_conj]

theorem physicalWedgeReflection_smul {m : ℝ} (hm : 0 < m) (c : ℂ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    physicalWedgeReflection hm (c • ψ) = conj c • physicalWedgeReflection hm ψ := by
  apply Lp.ext
  have hpull := (measurePreserving_massShell_rotation hm
    axisReflection).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_smul c ψ)
  filter_upwards [physicalWedgeReflection_ae hm (c • ψ), hpull,
    Lp.coeFn_smul (conj c) (physicalWedgeReflection hm ψ), physicalWedgeReflection_ae hm ψ]
    with p h₁ h₂ h₃ h₄
  simp only [h₁, h₃, h₄, Function.comp_apply, Pi.smul_apply] at h₂ ⊢
  rw [h₂, smul_eq_mul, map_mul, smul_eq_mul]

theorem norm_physicalWedgeReflection {m : ℝ} (hm : 0 < m)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) : ‖physicalWedgeReflection hm ψ‖ = ‖ψ‖ := by
  let R : Lp ℂ 2 (oneParticleMeasure m) →ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
    Lp.compMeasurePreservingₗᵢ ℂ axisReflection
    (measurePreserving_massShell_rotation hm axisReflection)
  have he : ∀ᵐ p ∂oneParticleMeasure m, ‖physicalWedgeReflection hm ψ p‖ = ‖R ψ p‖ := by
    filter_upwards [physicalWedgeReflection_ae hm ψ,
      Lp.coeFn_compMeasurePreserving ψ (measurePreserving_massShell_rotation hm axisReflection)]
      with p h₁ h₂
    change ‖physicalWedgeReflection hm ψ p‖ =
      ‖Lp.compMeasurePreserving axisReflection
        (measurePreserving_massShell_rotation hm axisReflection) ψ p‖
    rw [h₁, h₂, Function.comp_apply, Complex.norm_conj]
  have hn : ‖physicalWedgeReflection hm ψ‖ = ‖R ψ‖ :=
    le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.le))
      (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.ge))
  exact hn.trans (R.norm_map ψ)

theorem wedgeWaveL2_upper_eq_reflection {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) :
    wedgeWaveL2 hm F hF ((Real.pi : ℂ) * Complex.I) (by simp [Real.pi_pos.le]) =
      physicalWedgeReflection hm (oneParticleL2 hm F) := by
  apply Lp.ext
  have hpull := (measurePreserving_massShell_rotation hm
    axisReflection).quasiMeasurePreserving.ae_eq_comp
    (coeFn_oneParticleL2 hm F)
  filter_upwards [wedgeWaveL2_ae hm F hF ((Real.pi : ℂ) * Complex.I)
    (by simp [Real.pi_pos.le]), physicalWedgeReflection_ae hm (oneParticleL2 hm F), hpull]
    with p h₁ h₂ h₃
  rw [h₁, h₂, wedgeWave_pi_mul_I]
  exact congrArg conj (show (oneParticle m F) (axisReflection p) =
    (oneParticleL2 hm F) (axisReflection p) from h₃.symm)

end VacuumBellSeparation
