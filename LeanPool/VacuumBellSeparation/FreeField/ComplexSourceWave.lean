/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeWaveEntire
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroL2
public import LeanPool.VacuumBellSeparation.Shell.NullDiscs

/-!
# The literal complex-shell wave of the original Cauchy data

The spatial Fourier integral uses the complex bilinear spatial product,
with no conjugation. Psi(f,g)(z)=fhat(z_sp)+i z0 ghat(z_sp) is defined on
the original complex four-dimensional space. Its boost argument has all
three spatial coordinates and lies on the original massive quadric.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

/-- Complex spatial Fourier given by `∫ x : EuclideanSpace ℝ (Fin 3), Complex.exp (-(Complex.I *
spatialDot z (fun i => (x i : ℂ)))) * (f.1 x : ℂ)`. -/
noncomputable def complexSpatialFourier (f : SpatialTestFunction) (z : Fin 3 → ℂ) : ℂ :=
  ∫ x : EuclideanSpace ℝ (Fin 3),
    Complex.exp (-(Complex.I * spatialDot z (fun i => (x i : ℂ)))) * (f.1 x : ℂ)

/-- Complex source wave given by `complexSpatialFourier u.1 z.2 + Complex.I * z.1 *
complexSpatialFourier u.2 z.2`. -/
noncomputable def complexSourceWave (u : TimeZeroSource) (z : ℂ × (Fin 3 → ℂ)) : ℂ :=
  complexSpatialFourier u.1 z.2 + Complex.I * z.1 * complexSpatialFourier u.2 z.2

theorem real_spatialDot (p x : EuclideanSpace ℝ (Fin 3)) :
    spatialDot (fun i => (p i : ℂ)) (fun i => (x i : ℂ)) = (⟪p, x⟫_ℝ : ℂ) := by
  simp only [spatialDot, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    star_trivial, Complex.ofReal_sum, Complex.ofReal_mul, mul_comm]

theorem complexSpatialFourier_ofReal (f : SpatialTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    complexSpatialFourier f (fun i => (p i : ℂ)) = spatialFourier f p := by
  unfold complexSpatialFourier spatialFourier
  simp only [real_spatialDot]

theorem complexSourceWave_onShell (m : ℝ) (u : TimeZeroSource)
    (p : EuclideanSpace ℝ (Fin 3)) :
    complexSourceWave u ((dispersion m p : ℂ), fun i => (p i : ℂ)) = timeZeroOneParticle m u p := by
  simp only [complexSourceWave, complexSpatialFourier_ofReal, timeZeroOneParticle]

/-- Complexification of a coordinate boost of an on-shell spatial momentum. -/
noncomputable def complexShellBoost (m : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    ℂ × (Fin 3 → ℂ) :=
  ((dispersion m p : ℂ) * Complex.cosh ζ + (p 0 : ℂ) * Complex.sinh ζ,
    ![(p 0 : ℂ) * Complex.cosh ζ + (dispersion m p : ℂ) * Complex.sinh ζ,
      (p 1 : ℂ), (p 2 : ℂ)])

theorem complexShellBoost_mem_shell (m : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    complexShellBoost m ζ p ∈ complexShell m := by
  have hd : (dispersion m p : ℂ) ^ 2 =
      (m : ℂ) ^ 2 + ((p 0 : ℂ) ^ 2 + (p 1 : ℂ) ^ 2 + (p 2 : ℂ) ^ 2) := by
    have h := dispersion_sq m p
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at h
    exact_mod_cast h
  change (complexShellBoost m ζ p).1 ^ 2 -
    spatialDot (complexShellBoost m ζ p).2 (complexShellBoost m ζ p).2 = (m : ℂ) ^ 2
  simp only [complexShellBoost, spatialDot_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_one, Matrix.cons_val_succ]
  linear_combination hd + ((dispersion m p : ℂ) ^ 2 - (p 0 : ℂ) ^ 2) *
    Complex.cosh_sq_sub_sinh_sq ζ

theorem complexShellBoost_phase (m : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3))
    (x : Spacetime) :
    (complexShellBoost m ζ p).1 * (x.1 : ℂ) -
      spatialDot (complexShellBoost m ζ p).2 (fun i => (x.2 i : ℂ)) =
        boostPhase m (-ζ) p x := by
  have he (q : EuclideanSpace ℝ (Fin 3)) : ⟪e₁, q⟫_ℝ = q 0 := by
    simp [e₁, EuclideanSpace.inner_single_left]
  rw [boostPhase, he p, he x.2, ← real_spatialDot p x.2]
  simp only [complexShellBoost, spatialDot_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_one, Matrix.cons_val_succ,
    Complex.cosh_neg, Complex.sinh_neg]
  ring

end VacuumBellSeparation
