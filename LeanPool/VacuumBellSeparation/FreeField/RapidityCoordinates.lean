/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Lorentz
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Actual rapidity coordinates on the massive three-dimensional shell

The first coordinate is rapidity and the remaining two are unchanged transverse
momenta. This is a homeomorphism of the original Euclidean momentum space, not
a restriction to a longitudinal slice.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

/-- Transverse mass given by `Real.sqrt (m ^ 2 + (x 1) ^ 2 + (x 2) ^ 2)`. -/
noncomputable def transverseMass (m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.sqrt (m ^ 2 + (x 1) ^ 2 + (x 2) ^ 2)

theorem transverseMass_pos {m : ℝ} (hm : 0 < m) (x : EuclideanSpace ℝ (Fin 3)) :
    0 < transverseMass m x := by
  apply Real.sqrt_pos.mpr
  positivity

theorem transverseMass_sq (m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    transverseMass m x ^ 2 = m ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  exact Real.sq_sqrt (by positivity)

/-- Rapidity momentum given by `!₂[transverseMass m x * Real.sinh (x 0), x 1, x 2]`. -/
noncomputable def rapidityMomentum (m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[transverseMass m x * Real.sinh (x 0), x 1, x 2]

/-- Momentum rapidity given by `!₂[Real.arsinh (p 0 / transverseMass m p), p 1, p 2]`. -/
noncomputable def momentumRapidity (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[Real.arsinh (p 0 / transverseMass m p), p 1, p 2]

@[simp] theorem transverseMass_rapidityMomentum (m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    transverseMass m (rapidityMomentum m x) = transverseMass m x := rfl

@[simp] theorem transverseMass_momentumRapidity (m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    transverseMass m (momentumRapidity m x) = transverseMass m x := rfl

theorem momentumRapidity_rapidityMomentum {m : ℝ} (hm : 0 < m)
    (x : EuclideanSpace ℝ (Fin 3)) : momentumRapidity m (rapidityMomentum m x) = x := by
  have hM := (transverseMass_pos hm x).ne'
  ext i
  fin_cases i
  · change Real.arsinh ((transverseMass m x * Real.sinh (x 0)) / transverseMass m x) = x 0
    rw [mul_div_cancel_left₀ _ hM, Real.arsinh_sinh]
  · rfl
  · rfl

theorem rapidityMomentum_momentumRapidity {m : ℝ} (hm : 0 < m)
    (p : EuclideanSpace ℝ (Fin 3)) : rapidityMomentum m (momentumRapidity m p) = p := by
  have hM := (transverseMass_pos hm p).ne'
  ext i
  fin_cases i
  · change transverseMass m p * Real.sinh (Real.arsinh (p 0 / transverseMass m p)) = p 0
    rw [Real.sinh_arsinh, mul_div_cancel₀ _ hM]
  · rfl
  · rfl

@[fun_prop] theorem continuous_transverseMass (m : ℝ) : Continuous (transverseMass m) := by
  unfold transverseMass
  fun_prop

@[fun_prop] theorem continuous_rapidityMomentum (m : ℝ) : Continuous (rapidityMomentum m) := by
  unfold rapidityMomentum
  fun_prop

@[fun_prop] theorem continuous_momentumRapidity {m : ℝ} (hm : 0 < m) :
    Continuous (momentumRapidity m) := by
  have hM : ∀ x, transverseMass m x ≠ 0 := fun x => (transverseMass_pos hm x).ne'
  have hcoord : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => p 0 / transverseMass m p) :=
    (by fun_prop : Continuous (fun p : EuclideanSpace ℝ (Fin 3) => p 0)).div
      (continuous_transverseMass m) hM
  change Continuous (fun p : EuclideanSpace ℝ (Fin 3) => WithLp.toLp 2
    ![Real.arsinh (p 0 / transverseMass m p), p 1, p 2])
  have hv : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      (![Real.arsinh (p 0 / transverseMass m p), p 1, p 2] : Fin 3 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
        Real.arsinh (p 0 / transverseMass m p))
      exact Real.continuous_arsinh.comp hcoord
    · change Continuous (fun p : EuclideanSpace ℝ (Fin 3) => p 1)
      exact (continuous_apply 1).comp (PiLp.continuous_ofLp 2 _)
    · change Continuous (fun p : EuclideanSpace ℝ (Fin 3) => p 2)
      exact (continuous_apply 2).comp (PiLp.continuous_ofLp 2 _)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp hv

/-- The full massive shell parametrization, retaining both transverse momenta. -/
noncomputable def rapidityHomeomorph {m : ℝ} (hm : 0 < m) :
    EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) where
  toFun := rapidityMomentum m
  invFun := momentumRapidity m
  left_inv := momentumRapidity_rapidityMomentum hm
  right_inv := rapidityMomentum_momentumRapidity hm
  continuous_toFun := continuous_rapidityMomentum m
  continuous_invFun := continuous_momentumRapidity hm

theorem dispersion_rapidityMomentum {m : ℝ} (hm : 0 < m)
    (x : EuclideanSpace ℝ (Fin 3)) :
    dispersion m (rapidityMomentum m x) = transverseMass m x * Real.cosh (x 0) := by
  have hsq := dispersion_sq m (rapidityMomentum m x)
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at hsq
  change dispersion m (rapidityMomentum m x) ^ 2 =
    m ^ 2 + ((transverseMass m x * Real.sinh (x 0)) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2) at hsq
  have hM := transverseMass_sq m x
  have hch := Real.cosh_sq_sub_sinh_sq (x 0)
  have hnonneg := (dispersion_pos hm.ne' (rapidityMomentum m x)).le
  have hright := mul_pos (transverseMass_pos hm x) (Real.cosh_pos (x 0))
  have hmult := congrArg (fun t : ℝ => transverseMass m x ^ 2 * t) hch
  have heq : dispersion m (rapidityMomentum m x) ^ 2 =
      (transverseMass m x * Real.cosh (x 0)) ^ 2 := by nlinarith
  nlinarith

/-- Rapidity translate given by `!₂[x 0 + η, x 1, x 2]`. -/
noncomputable def rapidityTranslate (η : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) := !₂[x 0 + η, x 1, x 2]

@[simp] theorem transverseMass_rapidityTranslate (m η : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    transverseMass m (rapidityTranslate η x) = transverseMass m x := rfl

/-- The physical shell boost is literal translation of the rapidity coordinate. -/
theorem shellBoost_rapidityMomentum {m : ℝ} (hm : 0 < m) (η : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    shellBoost m η (rapidityMomentum m x) = rapidityMomentum m (rapidityTranslate η x) := by
  have he (p : EuclideanSpace ℝ (Fin 3)) : ⟪e₁, p⟫_ℝ = p 0 := by
    simp [e₁, EuclideanSpace.inner_single_left]
  rw [shellBoost, he, dispersion_rapidityMomentum hm]
  ext i
  fin_cases i <;> simp [rapidityMomentum, rapidityTranslate, transverseMass, e₁,
    Real.sinh_add]; ring

theorem momentumRapidity_shellBoost {m : ℝ} (hm : 0 < m) (η : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    momentumRapidity m (shellBoost m η p) = rapidityTranslate η (momentumRapidity m p) := by
  calc
    _ = momentumRapidity m (shellBoost m η (rapidityMomentum m (momentumRapidity m p))) := by
      rw [rapidityMomentum_momentumRapidity hm]
    _ = _ := by rw [shellBoost_rapidityMomentum hm, momentumRapidity_rapidityMomentum hm]

end VacuumBellSeparation
