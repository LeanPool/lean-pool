/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Lorentz

/-!
# Literal Minkowski-preserving spacetime automorphisms

The form and spacetime carrier are those of the original physical model.
The defining condition is preservation of that bilinear form; positive
time-axis orientation and determinant one are separate explicit predicates.
An automorphism fixing the time axis is proved to be a spatial isometry.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

/-- Predicate for Lorentz map. -/
def IsLorentzMap (Λ : Spacetime ≃L[ℝ] Spacetime) : Prop :=
  ∀ x y, minkowskiForm (Λ x) (Λ y) = minkowskiForm x y

/-- Condition that a spacetime map preserves the future time direction. -/
def IsOrthochronousMap (Λ : Spacetime ≃L[ℝ] Spacetime) : Prop :=
  0 < (Λ (1, 0)).1

/-- Predicate for proper Lorentz map defined as `IsLorentzMap Λ ∧ LinearMap.det
Λ.toLinearEquiv.toLinearMap = 1`. -/
def IsProperLorentzMap (Λ : Spacetime ≃L[ℝ] Spacetime) : Prop :=
  IsLorentzMap Λ ∧ LinearMap.det Λ.toLinearEquiv.toLinearMap = 1

theorem IsLorentzMap.symm {Λ : Spacetime ≃L[ℝ] Spacetime} (hΛ : IsLorentzMap Λ) :
    IsLorentzMap Λ.symm := by
  intro x y
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (hΛ (Λ.symm x) (Λ.symm y)).symm

theorem IsLorentzMap.trans {Λ Γ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (hΓ : IsLorentzMap Γ) : IsLorentzMap (Λ.trans Γ) := by
  intro x y
  exact (hΓ (Λ x) (Λ y)).trans (hΛ x y)

theorem isLorentzMap_boost (η : ℝ) : IsLorentzMap (boost η) :=
  minkowskiForm_boost η

theorem isLorentzMap_spatialRotation
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    IsLorentzMap (spatialRotation R) := by
  intro x y
  simp only [minkowskiForm, spatialRotation_apply, LinearIsometryEquiv.inner_map_map]

theorem lorentz_timeAxis_square {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) : (Λ (1, 0)).1 ^ 2 - ‖(Λ (1, 0)).2‖ ^ 2 = 1 := by
  have h := hΛ (1, 0) (1, 0)
  simpa only [minkowskiForm, real_inner_self_eq_norm_sq, one_mul, inner_zero_left,
    sub_zero, ← pow_two, one_pow] using h

theorem lorentz_timeAxis_inverse_time {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) : (Λ.symm (1, 0)).1 = (Λ (1, 0)).1 := by
  have h := hΛ (Λ.symm (1, 0)) (1, 0)
  simpa only [ContinuousLinearEquiv.apply_symm_apply, minkowskiForm,
    one_mul, mul_one, inner_zero_left, inner_zero_right, sub_zero] using h.symm

theorem IsOrthochronousMap.symm {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ) : IsOrthochronousMap Λ.symm := by
  change 0 < (Λ.symm (1, 0)).1
  rw [lorentz_timeAxis_inverse_time hΛ]
  exact hfuture

theorem lorentz_fixed_timeAxis_spatial_time_zero {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (he : Λ (1, 0) = (1, 0))
    (x : EuclideanSpace ℝ (Fin 3)) : (Λ (0, x)).1 = 0 := by
  have h := hΛ (0, x) (1, 0)
  rw [he] at h
  simpa only [minkowskiForm, mul_one, zero_mul, inner_zero_right, sub_zero] using h

theorem lorentz_fixed_timeAxis_spatial_norm {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (he : Λ (1, 0) = (1, 0))
    (x : EuclideanSpace ℝ (Fin 3)) : ‖(Λ (0, x)).2‖ = ‖x‖ := by
  have h := hΛ (0, x) (0, x)
  simp only [minkowskiForm, lorentz_fixed_timeAxis_spatial_time_zero hΛ he,
    zero_mul, real_inner_self_eq_norm_sq, zero_sub] at h
  nlinarith [norm_nonneg ((Λ (0, x)).2), norm_nonneg x]

/-- Linear isometry equivalence for the lorentz fixed time rotation, of type `EuclideanSpace ℝ (Fin
3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def lorentzFixedTimeRotation (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (he : Λ (1, 0) = (1, 0)) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) := by
  have hes : Λ.symm (1, 0) = (1, 0) := by
    calc Λ.symm (1, 0) = Λ.symm (Λ (1, 0)) := congrArg Λ.symm he.symm
         _ = (1, 0) := Λ.symm_apply_apply _
  let A : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3))).comp
      (Λ.toLinearEquiv.toLinearMap.comp (LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3))))
  let B : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3))).comp
      (Λ.symm.toLinearEquiv.toLinearMap.comp (LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3))))
  have ha (x : EuclideanSpace ℝ (Fin 3)) : Λ (0, x) = (0, A x) := by
    apply Prod.ext
    · exact lorentz_fixed_timeAxis_spatial_time_zero hΛ he x
    · rfl
  have hb (x : EuclideanSpace ℝ (Fin 3)) : Λ.symm (0, x) = (0, B x) := by
    apply Prod.ext
    · exact lorentz_fixed_timeAxis_spatial_time_zero hΛ.symm hes x
    · rfl
  exact
    { toLinearEquiv :=
        { A with
          invFun := B
          left_inv := fun x => by
            have h := congrArg (fun q : Spacetime => q.2) (Λ.symm_apply_apply (0, x))
            rw [ha, hb] at h
            exact h
          right_inv := fun x => by
            have h := congrArg (fun q : Spacetime => q.2) (Λ.apply_symm_apply (0, x))
            rw [hb, ha] at h
            exact h }
      norm_map' := lorentz_fixed_timeAxis_spatial_norm hΛ he }

theorem lorentzFixedTimeRotation_factorization (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (he : Λ (1, 0) = (1, 0)) :
    Λ = spatialRotation (lorentzFixedTimeRotation Λ hΛ he) := by
  apply ContinuousLinearEquiv.ext
  funext x
  have hx : x = x.1 • ((1, 0) : Spacetime) + (0, x.2) := by ext <;> simp
  have hs : Λ (0, x.2) = (0, lorentzFixedTimeRotation Λ hΛ he x.2) :=
    Prod.ext (lorentz_fixed_timeAxis_spatial_time_zero hΛ he x.2) rfl
  calc
    Λ x = Λ (x.1 • ((1, 0) : Spacetime) + (0, x.2)) := congrArg Λ hx
    _ = x.1 • ((1, 0) : Spacetime) + (0, lorentzFixedTimeRotation Λ hΛ he x.2) := by
      rw [map_add, map_smul, he, hs]
    _ = spatialRotation (lorentzFixedTimeRotation Λ hΛ he) x := by
      simp [spatialRotation_apply]

end VacuumBellSeparation
