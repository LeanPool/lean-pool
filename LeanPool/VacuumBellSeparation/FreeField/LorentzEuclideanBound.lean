/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.EuclideanWedgeContainment
public import LeanPool.VacuumBellSeparation.FreeField.LorentzMap
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Quantitative genuine Euclidean bounds for Lorentz maps

The time row is the Minkowski pairing with the inverse time axis.
Euclidean Cauchy--Schwarz and preservation of the Minkowski square give
the operator-norm bound 2 gamma for both a future Lorentz map and its
inverse. This avoids assuming a singular-value formula.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

theorem spacetimeEuclideanNorm_sq (x : Spacetime) :
    spacetimeEuclideanNorm x ^ 2 = x.1 ^ 2 + ‖x.2‖ ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem minkowskiForm_sq_le_euclidean (x y : Spacetime) :
    minkowskiForm x y ^ 2 ≤ spacetimeEuclideanNorm x ^ 2 * spacetimeEuclideanNorm y ^ 2 := by
  have h := real_inner_mul_inner_self_le
    (WithLp.toLp 2 (x.1, -x.2) : EuclideanSpacetime) (WithLp.toLp 2 y)
  rw [spacetimeEuclideanNorm_sq, spacetimeEuclideanNorm_sq]
  simpa only [WithLp.prod_inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply', star_trivial,
    map_neg, starRingEnd_apply, star_trivial,
    inner_neg_left, inner_neg_right, real_inner_self_eq_norm_sq, neg_neg, sub_neg_eq_add, ← pow_two,
    ← sub_eq_add_neg, minkowskiForm] using h

theorem lorentz_timeComponent_eq_form {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (x : Spacetime) :
    (Λ x).1 = minkowskiForm (Λ.symm (1, 0)) x := by
  have h := hΛ (Λ.symm (1, 0)) x
  simpa only [ContinuousLinearEquiv.apply_symm_apply, minkowskiForm,
    one_mul, inner_zero_left, sub_zero] using h

theorem lorentz_inverse_timeAxis_euclidean_sq {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) :
    spacetimeEuclideanNorm (Λ.symm (1, 0)) ^ 2 = 2 * (Λ (1, 0)).1 ^ 2 - 1 := by
  have h := lorentz_timeAxis_square hΛ.symm
  rw [lorentz_timeAxis_inverse_time hΛ] at h
  rw [spacetimeEuclideanNorm_sq, lorentz_timeAxis_inverse_time hΛ]
  linarith

theorem spacetimeEuclideanNorm_lorentz_le {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ) (x : Spacetime) :
    spacetimeEuclideanNorm (Λ x) ≤ 2 * (Λ (1, 0)).1 * spacetimeEuclideanNorm x := by
  have hc := minkowskiForm_sq_le_euclidean (Λ.symm (1, 0)) x
  rw [← lorentz_timeComponent_eq_form hΛ x, lorentz_inverse_timeAxis_euclidean_sq hΛ] at hc
  have hform := hΛ x x
  simp only [minkowskiForm, real_inner_self_eq_norm_sq, ← pow_two] at hform
  have hx := spacetimeEuclideanNorm_sq x
  have hy := spacetimeEuclideanNorm_sq (Λ x)
  have hs : spacetimeEuclideanNorm (Λ x) ^ 2 ≤
      (2 * (Λ (1, 0)).1 * spacetimeEuclideanNorm x) ^ 2 := by
    nlinarith [sq_nonneg x.1]
  have hn : 0 ≤ 2 * (Λ (1, 0)).1 * spacetimeEuclideanNorm x :=
    mul_nonneg (mul_nonneg (by norm_num) hfuture.le) (spacetimeEuclideanNorm_nonneg x)
  nlinarith [spacetimeEuclideanNorm_nonneg (Λ x)]

theorem spacetimeEuclideanOperatorNorm_lorentz_le {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ) :
    spacetimeEuclideanOperatorNorm Λ ≤ 2 * (Λ (1, 0)).1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hfuture.le)
  intro y
  have h := spacetimeEuclideanNorm_lorentz_le hΛ hfuture (spacetimeEuclideanEquiv.symm y)
  rw [← norm_spacetimeEuclideanEquiv, ← norm_spacetimeEuclideanEquiv,
    ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

theorem spacetimeEuclideanOperatorNorm_lorentz_inverse_le
    {Λ : Spacetime ≃L[ℝ] Spacetime} (hΛ : IsLorentzMap Λ) (hfuture : IsOrthochronousMap Λ) :
    spacetimeEuclideanOperatorNorm Λ.symm ≤ 2 * (Λ (1, 0)).1 := by
  have h := spacetimeEuclideanOperatorNorm_lorentz_le hΛ.symm
    (IsOrthochronousMap.symm hΛ hfuture)
  rwa [lorentz_timeAxis_inverse_time hΛ] at h

end VacuumBellSeparation
