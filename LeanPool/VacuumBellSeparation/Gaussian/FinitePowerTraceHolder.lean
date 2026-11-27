/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveMatrixComplexPowers

/-!
# Finite positive power traces and unitary Holder bounds

These genuine finite matrix trace identities are the endpoint estimates
for spectral compression interpolation. The arbitrary unitary factors
and complex exponents retain all boundary phases. No passage to the full
infinite-dimensional density is asserted here.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The extended nonnegative real trace of the matrix power, obtained from the real part of the
ordinary matrix trace. -/
def finitePositivePowerTrace (A : Matrix ι ι ℂ) (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (A ^ p).trace.re

theorem finitePositivePowerTrace_eq_eigenvalue_sum {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (p : ℝ) :
    finitePositivePowerTrace A p =
      ∑ i, ENNReal.ofReal (hA.isHermitian.eigenvalues i ^ p) := by
  rw [finitePositivePowerTrace, CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    hA.isHermitian.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal,
    Complex.re_sum]
  simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]
  exact ENNReal.ofReal_sum_of_nonneg fun i _ => Real.rpow_nonneg (hA.eigenvalues_pos i).le p

theorem finitePositivePowerTrace_lt_top (A : Matrix ι ι ℂ) (p : ℝ) :
    finitePositivePowerTrace A p < ∞ := ENNReal.ofReal_lt_top

theorem trace_unitary_conjugates_product (U V W X : unitary (Matrix ι ι ℂ))
    (a b : ι → ℂ) :
    (((U : Matrix ι ι ℂ) * Matrix.diagonal a * star (U : Matrix ι ι ℂ)) *
      (W : Matrix ι ι ℂ) *
      ((V : Matrix ι ι ℂ) * Matrix.diagonal b * star (V : Matrix ι ι ℂ)) *
      (X : Matrix ι ι ℂ)).trace =
      (Matrix.diagonal a * ((star U * W * V : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) *
        Matrix.diagonal b * ((star V * X * U : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)).trace := by
  simp only [Submonoid.coe_mul, Unitary.coe_star]
  calc
    _ = ((U : Matrix ι ι ℂ) *
        (Matrix.diagonal a * (star (U : Matrix ι ι ℂ) * (W : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)) *
          Matrix.diagonal b * (star (V : Matrix ι ι ℂ) * (X : Matrix ι ι ℂ)))).trace := by
      congr 1
      noncomm_ring
    _ = _ := by rw [Matrix.trace_mul_comm]; congr 1; noncomm_ring

theorem finiteComplexPower_trace_holder {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (U V : unitary (Matrix ι ι ℂ))
    (z w : ℂ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ENNReal.ofReal ‖(positiveMatrixComplexPower hA z * (U : Matrix ι ι ℂ) *
      positiveMatrixComplexPower hB w * (V : Matrix ι ι ℂ)).trace‖ ≤
      finitePositivePowerTrace A (z.re * p) ^ (1 / p) *
        finitePositivePowerTrace B (w.re * q) ^ (1 / q) := by
  let UA := hA.isHermitian.eigenvectorUnitary
  let UB := hB.isHermitian.eigenvectorUnitary
  let a : ι → ℂ := fun i => Complex.exp (z * (Real.log (hA.isHermitian.eigenvalues i) : ℂ))
  let b : ι → ℂ := fun i => Complex.exp (w * (Real.log (hB.isHermitian.eigenvalues i) : ℂ))
  have ht : (positiveMatrixComplexPower hA z * (U : Matrix ι ι ℂ) *
      positiveMatrixComplexPower hB w * (V : Matrix ι ι ℂ)).trace =
      (Matrix.diagonal a * ((star UA * U * UB : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) *
        Matrix.diagonal b * ((star UB * V * UA : unitary
          (Matrix ι ι ℂ)) : Matrix ι ι ℂ)).trace := by
    exact trace_unitary_conjugates_product UA UB U V a b
  have ha (i : ι) : ENNReal.ofReal ‖a i‖ ^ p =
      ENNReal.ofReal (hA.isHermitian.eigenvalues i ^ (z.re * p)) := by
    dsimp only [a]
    rw [norm_positiveMatrixComplexPower_eigenvalue hA z i,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hA.eigenvalues_pos i).le _) hpq.nonneg,
      Real.rpow_mul (hA.eigenvalues_pos i).le]
  have hb (i : ι) : ENNReal.ofReal ‖b i‖ ^ q =
      ENNReal.ofReal (hB.isHermitian.eigenvalues i ^ (w.re * q)) := by
    dsimp only [b]
    rw [norm_positiveMatrixComplexPower_eigenvalue hB w i,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hB.eigenvalues_pos i).le _) hpq.symm.nonneg,
      Real.rpow_mul (hB.eigenvalues_pos i).le]
  rw [ht, finitePositivePowerTrace_eq_eigenvalue_sum hA,
    finitePositivePowerTrace_eq_eigenvalue_sum hB]
  simpa only [ha, hb] using ennreal_trace_two_unitary_diagonals_holder
    (star UA * U * UB) (star UB * V * UA) a b hpq

theorem finitePositive_trace_unitary_holder {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (U V : unitary (Matrix ι ι ℂ))
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ENNReal.ofReal ‖(A * (U : Matrix ι ι ℂ) * B * (V : Matrix ι ι ℂ)).trace‖ ≤
      finitePositivePowerTrace A p ^ (1 / p) * finitePositivePowerTrace B q ^ (1 / q) := by
  simpa only [positiveMatrixComplexPower_one, Complex.one_re, one_mul] using
    finiteComplexPower_trace_holder hA hB U V 1 1 hpq

end VacuumBellSeparation.Gaussian
