/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LorentzShellAction

/-!
# The full original one-particle Lorentz representation

For every actual future-oriented Minkowski automorphism Lambda,
U(Lambda) psi(p) = psi(Lambda^{-1} p) on the full mass-shell L2 space.
Measure invariance and the literal inverse shell map prove unitarity.
Its test-vector intertwining uses the original spacetime Fourier integral.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ)

/-- Linear isometry equivalence for the one particle Lorentz, of type `Lp ℂ 2 (oneParticleMeasure
m) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def oneParticleLorentz :
    Lp ℂ 2 (oneParticleMeasure m) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) := by
  let A : Lp ℂ 2 (oneParticleMeasure m) →ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
    Lp.compMeasurePreservingₗᵢ ℂ (lorentzShellMap m Λ.symm)
    (measurePreserving_lorentzShellMap hm Λ.symm hΛ.symm (IsOrthochronousMap.symm hΛ hfuture))
  apply LinearIsometryEquiv.ofSurjective A
  intro ψ
  refine ⟨Lp.compMeasurePreserving (lorentzShellMap m Λ)
    (measurePreserving_lorentzShellMap hm Λ hΛ hfuture) ψ, ?_⟩
  change Lp.compMeasurePreserving (lorentzShellMap m Λ.symm) _
    (Lp.compMeasurePreserving (lorentzShellMap m Λ) _ ψ) = ψ
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : lorentzShellMap m Λ ∘ lorentzShellMap m Λ.symm = id := by
    funext p
    simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_symm, id_eq] using
      lorentzShellMap_inverse m Λ.symm hΛ.symm (IsOrthochronousMap.symm hΛ hfuture) p
  simp only [he, Lp.compMeasurePreserving_id_apply]

theorem oneParticleLorentz_ae (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleLorentz hm Λ hΛ hfuture ψ =ᵐ[oneParticleMeasure m]
      fun p => ψ (lorentzShellMap m Λ.symm p) :=
  Lp.coeFn_compMeasurePreserving ψ
    (measurePreserving_lorentzShellMap hm Λ.symm hΛ.symm (IsOrthochronousMap.symm hΛ hfuture))

theorem oneParticleLorentz_oneParticleL2 (F : RealTestFunction) :
    oneParticleLorentz hm Λ hΛ hfuture (oneParticleL2 hm F) =
      oneParticleL2 hm (F.compCLE Λ.symm) := by
  apply Lp.ext
  have hpull := (measurePreserving_lorentzShellMap hm Λ.symm hΛ.symm
    (IsOrthochronousMap.symm hΛ hfuture)).quasiMeasurePreserving.ae_eq_comp
      (coeFn_oneParticleL2 hm F)
  filter_upwards [oneParticleLorentz_ae hm Λ hΛ hfuture (oneParticleL2 hm F), hpull,
    coeFn_oneParticleL2 hm (F.compCLE Λ.symm)] with p hU hF hcomp
  dsimp only [Function.comp_apply] at hF
  rw [hU, hF, hcomp, oneParticle_lorentzMap m Λ.symm hΛ.symm
    (IsOrthochronousMap.symm hΛ hfuture)]

theorem oneParticleLorentz_inverse_apply (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleLorentz hm Λ.symm hΛ.symm (IsOrthochronousMap.symm hΛ hfuture)
      (oneParticleLorentz hm Λ hΛ hfuture ψ) = ψ := by
  change Lp.compMeasurePreserving (lorentzShellMap m Λ.symm.symm) _
    (Lp.compMeasurePreserving (lorentzShellMap m Λ.symm) _ ψ) = ψ
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : lorentzShellMap m Λ.symm ∘ lorentzShellMap m Λ.symm.symm = id := by
    funext p
    simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_symm, id_eq] using
      lorentzShellMap_inverse m Λ hΛ hfuture p
  simp only [he, Lp.compMeasurePreserving_id_apply]

end VacuumBellSeparation
