/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplexMatrixFunctionalCalculus
public import LeanPool.VacuumBellSeparation.Gaussian.FiniteUnitaryTraceHolder
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Genuine entire complex powers of a strictly positive finite matrix

The actual spectral logarithm defines an entire complex exponent family.
On the real axis it equals the existing CFC real power, and imaginary
powers are actual unitaries. Strict positive definiteness is explicit;
this module does not totalize imaginary powers at a zero eigenvalue.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive matrix complex power. -/
def positiveMatrixComplexPower {A : Matrix ι ι ℂ} (hA : A.PosDef) (z : ℂ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hA.isHermitian.eigenvectorUnitary
    (Matrix.diagonal (fun i => Complex.exp (z * (Real.log (hA.isHermitian.eigenvalues i) : ℂ))))

@[simp] theorem positiveMatrixComplexPower_zero {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    positiveMatrixComplexPower hA 0 = 1 := by
  simp only [positiveMatrixComplexPower, zero_mul, Complex.exp_zero, Matrix.diagonal_one, map_one]

theorem positiveMatrixComplexPower_add {A : Matrix ι ι ℂ} (hA : A.PosDef) (z w : ℂ) :
    positiveMatrixComplexPower hA (z + w) =
      positiveMatrixComplexPower hA z * positiveMatrixComplexPower hA w := by
  simp only [positiveMatrixComplexPower, add_mul, Complex.exp_add,
    ← Matrix.diagonal_mul_diagonal, map_mul]

theorem positiveMatrixComplexPower_star {A : Matrix ι ι ℂ} (hA : A.PosDef) (z : ℂ) :
    star (positiveMatrixComplexPower hA z) = positiveMatrixComplexPower hA (conj z) := by
  rw [positiveMatrixComplexPower, ← map_star]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_apply_eq, ← starRingEnd_apply, Pi.conj_apply,
      ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal]
  · simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_apply_ne _ hij]

theorem positiveMatrixComplexPower_real {A : Matrix ι ι ℂ} (hA : A.PosDef) (t : ℝ) :
    positiveMatrixComplexPower hA (t : ℂ) = A ^ t := by
  rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg, hA.isHermitian.cfc_eq,
    Matrix.IsHermitian.cfc]
  unfold positiveMatrixComplexPower
  congr 1
  apply congrArg Matrix.diagonal
  funext i
  simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal]
  rw [Real.rpow_def_of_pos (hA.eigenvalues_pos i), Complex.ofReal_exp, Complex.ofReal_mul]
  congr 1
  ring

@[simp] theorem positiveMatrixComplexPower_one {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    positiveMatrixComplexPower hA 1 = A := by
  have h := positiveMatrixComplexPower_real hA 1
  simpa only [Complex.ofReal_one, CFC.rpow_one A hA.posSemidef.nonneg] using h

/-- Imaginary power of a positive matrix, defined by the functional calculus. -/
def positiveMatrixImaginaryPower {A : Matrix ι ι ℂ} (hA : A.PosDef) (t : ℝ) :
    unitary (Matrix ι ι ℂ) :=
  ⟨positiveMatrixComplexPower hA ((t : ℂ) * Complex.I), by
    constructor
    · rw [positiveMatrixComplexPower_star, ← positiveMatrixComplexPower_add]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
        neg_add_cancel, positiveMatrixComplexPower_zero]
    · rw [positiveMatrixComplexPower_star, ← positiveMatrixComplexPower_add]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
        add_neg_cancel, positiveMatrixComplexPower_zero]⟩

@[simp] theorem positiveMatrixImaginaryPower_coe {A : Matrix ι ι ℂ} (hA : A.PosDef) (t : ℝ) :
    (positiveMatrixImaginaryPower hA t : Matrix ι ι ℂ) =
      positiveMatrixComplexPower hA ((t : ℂ) * Complex.I) := rfl

theorem positiveMatrixComplexPower_split {A : Matrix ι ι ℂ} (hA : A.PosDef) (z : ℂ) :
    positiveMatrixComplexPower hA z =
      A ^ z.re * (positiveMatrixImaginaryPower hA z.im : Matrix ι ι ℂ) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [positiveMatrixComplexPower_add, positiveMatrixComplexPower_real]
  rfl

theorem differentiable_positiveMatrixComplexPower {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    Differentiable ℂ (positiveMatrixComplexPower hA) := by
  let L : (ι → ℂ) →L[ℂ] Matrix ι ι ℂ :=
    (Matrix.diagonalLinearMap ι ℂ ℂ).toContinuousLinearMap
  let conjugation := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hA.isHermitian.eigenvectorUnitary
  let C : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
    conjugation.toAlgEquiv.toAlgHom.toLinearMap.toContinuousLinearMap
  have hd : Differentiable ℂ (fun z : ℂ => fun i : ι =>
      Complex.exp (z * (Real.log (hA.isHermitian.eigenvalues i) : ℂ))) := by
    apply differentiable_pi.mpr
    intro i
    exact ((differentiable_id (𝕜 := ℂ) (E := ℂ)).mul_const _).cexp
  exact C.differentiable.comp (L.differentiable.comp hd)

theorem norm_positiveMatrixComplexPower_eigenvalue {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (z : ℂ) (i : ι) :
    ‖Complex.exp (z * (Real.log (hA.isHermitian.eigenvalues i) : ℂ))‖ =
      hA.isHermitian.eigenvalues i ^ z.re := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Real.rpow_def_of_pos (hA.eigenvalues_pos i)]
  congr 1
  ring

end VacuumBellSeparation.Gaussian
