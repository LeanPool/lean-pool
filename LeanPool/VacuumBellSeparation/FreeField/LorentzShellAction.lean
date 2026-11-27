/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LorentzDecomposition
public import LeanPool.VacuumBellSeparation.FreeField.WedgeReflection

/-!
# The actual positive-shell action of every orthochronous Lorentz map

The action is literally the spatial part of Lambda(omega(p),p). The
decomposition theorem proves positive-shell preservation and invariance
of the original positive mass-shell measure, including infinite sets.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

/-- Lorentz shell map. -/
noncomputable def lorentzShellMap (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (p : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (Λ (onShell m p)).2

theorem spatialRotation_onShell (m : ℝ)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : EuclideanSpace ℝ (Fin 3)) :
    spatialRotation R (onShell m p) = onShell m (R p) := by
  simp only [spatialRotation_apply, onShell, dispersion_linearIsometryEquiv]

theorem lorentzMap_onShell (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Λ (onShell m p) = onShell m (lorentzShellMap m Λ p) := by
  obtain ⟨R, S, η, rfl⟩ := lorentzMap_rotation_boost_rotation Λ hΛ hfuture
  simp only [lorentzShellMap, ContinuousLinearEquiv.trans_apply,
    spatialRotation_onShell, boost_onShell]
  rfl

theorem lorentzShellMap_trans (m : ℝ) (Λ Γ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    lorentzShellMap m (Λ.trans Γ) p = lorentzShellMap m Γ (lorentzShellMap m Λ p) := by
  exact congrArg (fun x : Spacetime => (Γ x).2)
    (lorentzMap_onShell m Λ hΛ hfuture p)

theorem lorentzShellMap_inverse (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    lorentzShellMap m Λ.symm (lorentzShellMap m Λ p) = p := by
  change (Λ.symm (onShell m (lorentzShellMap m Λ p))).2 = p
  rw [← lorentzMap_onShell m Λ hΛ hfuture, ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem continuous_lorentzShellMap (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) :
    Continuous (lorentzShellMap m Λ) :=
  (continuous_snd.comp Λ.continuous).comp ((continuous_dispersion m).prodMk continuous_id)

/-- Lorentz shell homeomorph. -/
noncomputable def lorentzShellHomeomorph (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ) :
    EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) where
  toFun := lorentzShellMap m Λ
  invFun := lorentzShellMap m Λ.symm
  left_inv := lorentzShellMap_inverse m Λ hΛ hfuture
  right_inv := by
    intro p
    simpa only [ContinuousLinearEquiv.symm_symm] using
      lorentzShellMap_inverse m Λ.symm hΛ.symm (IsOrthochronousMap.symm hΛ hfuture) p
  continuous_toFun := continuous_lorentzShellMap m Λ
  continuous_invFun := continuous_lorentzShellMap m Λ.symm

theorem measurePreserving_lorentzShellMap {m : ℝ} (hm : 0 < m)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (hfuture : IsOrthochronousMap Λ) :
    MeasurePreserving (lorentzShellMap m Λ) (oneParticleMeasure m) (oneParticleMeasure m) := by
  obtain ⟨R, S, η, rfl⟩ := lorentzMap_rotation_boost_rotation Λ hΛ hfuture
  have he : lorentzShellMap m (((spatialRotation R).trans (boost η)).trans (spatialRotation S)) =
      (S : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ∘ shellBoost m η ∘ R := by
    funext p
    simp only [lorentzShellMap, ContinuousLinearEquiv.trans_apply,
      spatialRotation_onShell, boost_onShell, Function.comp_apply]
    rfl
  rw [he]
  exact (measurePreserving_massShell_rotation hm S).comp
    ((measurePreserving_shellBoost hm η).comp (measurePreserving_massShell_rotation hm R))

/-- The spacetime volume substitution for arbitrary future-oriented Lorentz maps. -/
theorem measurePreserving_lorentzMap (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ) :
    MeasurePreserving Λ (volume : Measure Spacetime) volume := by
  obtain ⟨R, S, η, rfl⟩ := lorentzMap_rotation_boost_rotation Λ hΛ hfuture
  exact (measurePreserving_spatialRotation S).comp
    ((measurePreserving_boost η).comp (measurePreserving_spatialRotation R))

theorem oneParticle_lorentzMap (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ)
    (F : RealTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (F.compCLE Λ) p = oneParticle m F (lorentzShellMap m Λ p) := by
  apply oneParticle_compCLE Λ (measurePreserving_lorentzMap Λ hΛ hfuture)
  intro x
  have h := hΛ (onShell m p) x
  rw [lorentzMap_onShell m Λ hΛ hfuture] at h
  exact h.symm

end VacuumBellSeparation
