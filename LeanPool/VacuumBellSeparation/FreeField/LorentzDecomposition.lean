/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LorentzMap
public import LeanPool.VacuumBellSeparation.FreeField.Corollary

/-!
# Full orthochronous Lorentz decomposition in the original spacetime model

Rotate the spatial part of Lambda e0 onto e1, then use its actual rapidity
to remove the boost. The remaining literal automorphism fixes e0, hence
is a spatial isometry. This proves the decomposition for every future-
oriented Minkowski isometry, including the proper transformations needed
by the manuscript. No connectedness or manifold result is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

theorem lorentz_timeAxis_time_ge_one {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ) : 1 ≤ (Λ (1, 0)).1 := by
  have hs := lorentz_timeAxis_square hΛ
  have hp : 0 < (Λ (1, 0)).1 := hfuture
  nlinarith [sq_nonneg ‖(Λ (1, 0)).2‖]

/-- Every actual future-oriented Lorentz map is a spatial isometry, an
e1 boost, and another spatial isometry, in the stated composition order. -/
theorem lorentzMap_rotation_boost_rotation (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ) :
    ∃ (R S : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (η : ℝ),
      Λ = ((spatialRotation R).trans (boost η)).trans (spatialRotation S) := by
  let v := (Λ (1, 0)).2
  let t := (Λ (1, 0)).1
  obtain ⟨R, hR⟩ := exists_linearIsometryEquiv_apply_eq_norm_smul_e₁ v
  let η := Real.arsinh ‖v‖
  have hc : Real.cosh η = t := by
    have hs := lorentz_timeAxis_square hΛ
    have hp : 0 < t := hfuture
    have he : 1 + ‖v‖ ^ 2 = t ^ 2 := by dsimp [v, t]; linarith
    dsimp only [η]
    rw [Real.cosh_arsinh, he, Real.sqrt_sq hp.le]
  have hs : Real.sinh η = ‖v‖ := Real.sinh_arsinh _
  let B := (boost η).trans (spatialRotation R.symm)
  have hB : IsLorentzMap B := (isLorentzMap_boost η).trans (isLorentzMap_spatialRotation R.symm)
  have hBe : B (1, 0) = Λ (1, 0) := by
    have hv : R.symm (‖v‖ • e₁) = v := by rw [← hR, LinearIsometryEquiv.symm_apply_apply]
    apply Prod.ext
    · change (boost η (1, 0)).1 = t
      simp only [boost_apply, boostCLM_apply, mul_one, inner_zero_right, mul_zero, add_zero, hc]
    · change R.symm ((boost η (1, 0)).2) = v
      simpa only [boost_apply, boostCLM_apply, mul_one, inner_zero_right, mul_zero,
        add_zero, zero_add, hs] using hv
  let Q := Λ.trans B.symm
  have hQ : IsLorentzMap Q := hΛ.trans hB.symm
  have hQe : Q (1, 0) = (1, 0) := by
    change B.symm (Λ (1, 0)) = (1, 0)
    rw [← hBe, ContinuousLinearEquiv.symm_apply_apply]
  let S := lorentzFixedTimeRotation Q hQ hQe
  have hQs : Q = spatialRotation S := lorentzFixedTimeRotation_factorization Q hQ hQe
  refine ⟨S, R.symm, η, ?_⟩
  apply ContinuousLinearEquiv.ext
  funext x
  calc
    Λ x = B (Q x) := by simp only [Q, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    _ = B (spatialRotation S x) := by rw [hQs]
    _ = (((spatialRotation S).trans (boost η)).trans (spatialRotation R.symm)) x := rfl

/-- Covariance of the original one-particle pairing for every actual
orthochronous Lorentz map, derived from the literal boost/rotation proofs. -/
theorem oneParticleInner_lorentzMap {m : ℝ} (hm : m ≠ 0)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (hfuture : IsOrthochronousMap Λ) (F G : RealTestFunction) :
    oneParticleInner m (F.compCLE Λ) (G.compCLE Λ) = oneParticleInner m F G := by
  obtain ⟨R, S, η, rfl⟩ := lorentzMap_rotation_boost_rotation Λ hΛ hfuture
  exact oneParticleInner_compCLE_trans
    (oneParticleInner_compCLE_trans (oneParticleInner_spatialRotation m R)
      (oneParticleInner_boost hm η)) (oneParticleInner_spatialRotation m S) F G

end VacuumBellSeparation
