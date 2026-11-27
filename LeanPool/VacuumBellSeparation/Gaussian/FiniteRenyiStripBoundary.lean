/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteRenyiStrip

/-!
# The actual high boundary of finite Schatten interpolation

The finite reference sandwich is strictly positive because every real
power of a strictly positive matrix is invertible. The imaginary phases
are actual unitaries; keeping their order gives the genuine complex
trace Holder bound on the right boundary of the strip.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveMatrix_rpow_isUnit {A : Matrix ι ι ℂ} (hA : A.PosDef) (p : ℝ) :
    IsUnit (A ^ p) := by
  apply IsUnit.of_mul_eq_one (A ^ (-p : ℝ))
  rw [← positiveMatrixComplexPower_real hA p, ← positiveMatrixComplexPower_real hA (-p),
    ← positiveMatrixComplexPower_add, ← Complex.ofReal_add, add_neg_cancel,
    Complex.ofReal_zero, positiveMatrixComplexPower_zero]

theorem positiveMatrix_rpow_posDef {A : Matrix ι ι ℂ} (hA : A.PosDef) (p : ℝ) :
    (A ^ p).PosDef :=
  (CFC.rpow_nonneg (a := A) (y := p)).posSemidef.posDef_iff_isUnit.mpr
    (positiveMatrix_rpow_isUnit hA p)

/-- Finite Rényi sandwich given by `σ ^ (-τ / 2) * ρ * σ ^ (-τ / 2)`. -/
def finiteRenyiSandwich (ρ σ : Matrix ι ι ℂ) (τ : ℝ) : Matrix ι ι ℂ :=
  σ ^ (-τ / 2) * ρ * σ ^ (-τ / 2)

theorem finiteRenyiSandwich_posDef {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (τ : ℝ) : (finiteRenyiSandwich ρ σ τ).PosDef := by
  have h := (positiveMatrix_rpow_isUnit hσ (-τ / 2)).posDef_star_left_conjugate_iff.mpr hρ
  simpa only [(CFC.rpow_nonneg (a := σ) (y := -τ / 2)).isSelfAdjoint.star_eq,
    finiteRenyiSandwich] using h

theorem positiveMatrix_real_imaginary_power_commute {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (s t : ℝ) :
    A ^ s * (positiveMatrixImaginaryPower hA t : Matrix ι ι ℂ) =
      (positiveMatrixImaginaryPower hA t : Matrix ι ι ℂ) * A ^ s := by
  rw [← positiveMatrixComplexPower_real hA s, positiveMatrixImaginaryPower_coe,
    ← positiveMatrixComplexPower_add, ← positiveMatrixComplexPower_add]
  congr 1
  exact add_comm _ _

omit [DecidableEq ι] in
private theorem trace_one_edge_cycle (R S X U V : Matrix ι ι ℂ)
    (hSV : S * V = V * S) :
    ((X * U) * (S * V) * R * (S * V)).trace =
      ((S * R * S) * V * X * (U * V)).trace := by
  nth_rw 1 [hSV]
  calc
    _ = ((X * U * V) * ((S * R * S) * V)).trace := by
      simp only [mul_assoc]
    _ = (((S * R * S) * V) * (X * U * V)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

theorem finiteRenyiStripFunction_one_edge_identity {ρ σ X : Matrix ι ι ℂ}
    (hσ : σ.PosDef) (hX : X.PosDef) (τ : ℝ) {z : ℂ} (hz : z.re = 1) :
    finiteRenyiStripFunction hσ hX ρ τ z =
      (finiteRenyiSandwich ρ σ τ *
        (positiveMatrixImaginaryPower hσ ((-τ / 2) * z.im) : Matrix ι ι ℂ) *
        positiveMatrixComplexPower hX (2 * τ : ℝ) *
        ((positiveMatrixImaginaryPower hX (2 * τ * z.im) *
          positiveMatrixImaginaryPower hσ ((-τ / 2) * z.im) : unitary (Matrix ι ι ℂ)) :
            Matrix ι ι ℂ)).trace := by
  rw [finiteRenyiStripFunction,
    positiveMatrixComplexPower_real_mul_one_re hX (2 * τ) hz,
    positiveMatrixComplexPower_real_mul_one_re hσ (-τ / 2) hz,
    positiveMatrixComplexPower_real hX (2 * τ), Submonoid.coe_mul, finiteRenyiSandwich]
  exact trace_one_edge_cycle ρ (σ ^ (-τ / 2)) (X ^ (2 * τ))
    (positiveMatrixImaginaryPower hX (2 * τ * z.im))
    (positiveMatrixImaginaryPower hσ ((-τ / 2) * z.im))
    (positiveMatrix_real_imaginary_power_commute hσ _ _)

theorem ennreal_finiteRenyiStripFunction_one_edge {ρ σ X : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hX : X.PosDef) (τ : ℝ)
    {p q : ℝ} (hpq : p.HolderConjugate q) {z : ℂ} (hz : z.re = 1) :
    ENNReal.ofReal ‖finiteRenyiStripFunction hσ hX ρ τ z‖ ≤
      finitePositivePowerTrace (finiteRenyiSandwich ρ σ τ) p ^ (1 / p) *
        finitePositivePowerTrace X (2 * τ * q) ^ (1 / q) := by
  rw [finiteRenyiStripFunction_one_edge_identity hσ hX τ hz]
  have h := finiteComplexPower_trace_holder (finiteRenyiSandwich_posDef hρ hσ τ) hX
    (positiveMatrixImaginaryPower hσ ((-τ / 2) * z.im))
    (positiveMatrixImaginaryPower hX (2 * τ * z.im) *
      positiveMatrixImaginaryPower hσ ((-τ / 2) * z.im)) 1 (2 * τ : ℝ) hpq
  simpa only [positiveMatrixComplexPower_one, Complex.one_re, Complex.ofReal_re, one_mul] using h

end VacuumBellSeparation.Gaussian
