/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FinitePowerBounds
public import Mathlib.Analysis.Complex.Hadamard

/-!
# The actual finite spectral interpolation function

This file constructs the scalar trace function used in the source
Schatten interpolation argument and proves its entire regularity and
uniform vertical-strip boundedness. These hypotheses are established
from genuine finite spectral powers, rather than packaged as assumptions.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Set
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite Rényi strip function. -/
def finiteRenyiStripFunction {σ X : Matrix ι ι ℂ} (hσ : σ.PosDef) (hX : X.PosDef)
    (ρ : Matrix ι ι ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  (positiveMatrixComplexPower hX (((2 * τ : ℝ) : ℂ) * z) *
    positiveMatrixComplexPower hσ (((-τ / 2 : ℝ) : ℂ) * z) * ρ *
    positiveMatrixComplexPower hσ (((-τ / 2 : ℝ) : ℂ) * z)).trace

theorem differentiable_finiteRenyiStripFunction {σ X : Matrix ι ι ℂ}
    (hσ : σ.PosDef) (hX : X.PosDef) (ρ : Matrix ι ι ℂ) (τ : ℝ) :
    Differentiable ℂ (finiteRenyiStripFunction hσ hX ρ τ) := by
  let T : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have hx := (differentiable_positiveMatrixComplexPower hX).comp
    (differentiable_id.const_mul (((2 * τ : ℝ) : ℂ)) :
      Differentiable ℂ (fun z : ℂ => ((2 * τ : ℝ) : ℂ) * z))
  have hs := (differentiable_positiveMatrixComplexPower hσ).comp
    (differentiable_id.const_mul (((-τ / 2 : ℝ) : ℂ)) :
      Differentiable ℂ (fun z : ℂ => ((-τ / 2 : ℝ) : ℂ) * z))
  exact T.differentiable.comp (((hx.mul hs).mul_const ρ).mul hs)

theorem finiteRenyiStripFunction_bounded {σ X : Matrix ι ι ℂ}
    (hσ : σ.PosDef) (hX : X.PosDef) (ρ : Matrix ι ι ℂ) (τ : ℝ) :
    BddAbove ((norm ∘ finiteRenyiStripFunction hσ hX ρ τ) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  let T : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  obtain ⟨CX, hCX, hx⟩ := exists_bound_positiveMatrixComplexPower_real_mul_strip hX (2 * τ)
  obtain ⟨CS, hCS, hs⟩ := exists_bound_positiveMatrixComplexPower_real_mul_strip hσ (-τ / 2)
  refine ⟨‖T‖ * (CX * CS * ‖ρ‖ * CS), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hprod : ‖positiveMatrixComplexPower hX (((2 * τ : ℝ) : ℂ) * z) *
      positiveMatrixComplexPower hσ (((-τ / 2 : ℝ) : ℂ) * z) * ρ *
      positiveMatrixComplexPower hσ (((-τ / 2 : ℝ) : ℂ) * z)‖ ≤ CX * CS * ‖ρ‖ * CS :=
    norm_mul_le_of_le (norm_mul_le_of_le (norm_mul_le_of_le (hx z hz) (hs z hz)) le_rfl) (hs z hz)
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hprod (norm_nonneg T))

theorem positiveMatrixComplexPower_real_mul_imaginary {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (c : ℝ) {z : ℂ} (hz : z.re = 0) :
    positiveMatrixComplexPower hA ((c : ℂ) * z) =
      (positiveMatrixImaginaryPower hA (c * z.im) : Matrix ι ι ℂ) := by
  rw [positiveMatrixImaginaryPower_coe]
  congr 1
  have hz' : z = (z.im : ℂ) * Complex.I := by
    simpa only [hz, Complex.ofReal_zero, zero_add] using (Complex.re_add_im z).symm
  calc
    (c : ℂ) * z = (c : ℂ) * ((z.im : ℂ) * Complex.I) :=
      congrArg (fun w : ℂ => (c : ℂ) * w) hz'
    _ = ((c * z.im : ℝ) : ℂ) * Complex.I := by rw [Complex.ofReal_mul]; ring

theorem positiveMatrixComplexPower_real_mul_one_re {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (c : ℝ) {z : ℂ} (hz : z.re = 1) :
    positiveMatrixComplexPower hA ((c : ℂ) * z) =
      A ^ c * (positiveMatrixImaginaryPower hA (c * z.im) : Matrix ι ι ℂ) := by
  rw [positiveMatrixComplexPower_split]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.mul_im, add_zero, hz, mul_one]

theorem norm_finiteRenyiStripFunction_zero_edge {ρ σ X : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hX : X.PosDef) (τ : ℝ) {z : ℂ} (hz : z.re = 0) :
    ‖finiteRenyiStripFunction hσ hX ρ τ z‖ ≤ ρ.trace.re := by
  let UX := positiveMatrixImaginaryPower hX (2 * τ * z.im)
  let US := positiveMatrixImaginaryPower hσ ((-τ / 2) * z.im)
  have he : finiteRenyiStripFunction hσ hX ρ τ z =
      (ρ * ((US * UX * US : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)).trace := by
    unfold finiteRenyiStripFunction
    rw [positiveMatrixComplexPower_real_mul_imaginary hX _ hz,
      positiveMatrixComplexPower_real_mul_imaginary hσ _ hz]
    change (((UX : Matrix ι ι ℂ) * (US : Matrix ι ι ℂ)) * ρ * (US : Matrix ι ι ℂ)).trace =
      (ρ * ((US : Matrix ι ι ℂ) * (UX : Matrix ι ι ℂ) * (US : Matrix ι ι ℂ))).trace
    rw [Matrix.trace_mul_cycle ((UX : Matrix ι ι ℂ) * (US : Matrix ι ι ℂ)) ρ (US : Matrix ι ι ℂ),
      Matrix.trace_mul_comm ((US : Matrix ι ι ℂ) * ((UX : Matrix ι ι ℂ) * (US : Matrix ι ι ℂ))) ρ]
    simp only [Matrix.mul_assoc]
  rw [he]
  exact norm_trace_positive_mul_unitary_le hρ _

end VacuumBellSeparation.Gaussian
