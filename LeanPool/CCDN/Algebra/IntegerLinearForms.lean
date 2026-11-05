/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.LinearForm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Integer matrices give linear forms. Composition is matrix
multiplication, with an explicit coefficient-height bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The rational linear form `∑ i, a i * X i` with integer coefficient vector `a`. -/
abbrev integerLinearForm {σ : Type*} [Fintype σ] (a : σ → ℤ) : MvPolynomial σ ℚ :=
  linearForm fun i => (a i : ℚ)

/-- The integer linear form with the `i`-th standard basis vector as coefficients is `X i`. -/
lemma integerLinearForm_identity {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    integerLinearForm (fun j => if j = i then 1 else 0) = X i := by
  simp [linearForm]

/-- Substituting the integer linear forms with coefficient rows `b i` into the integer linear
form with coefficients `a` gives the integer linear form with coefficients `∑ i, a i * b i j`,
the product of the row vector `a` with the matrix `b`. -/
lemma integerLinearForm_comp {σ τ : Type*} [Fintype σ] [Fintype τ]
    (a : σ → ℤ) (b : σ → τ → ℤ) :
    aeval (fun i => integerLinearForm (b i)) (integerLinearForm a) =
      integerLinearForm (fun j => ∑ i, a i * b i j) := by
  simp only [integerLinearForm, linearForm, map_sum, map_mul, aeval_C, aeval_X,
    Finset.mul_sum, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [algebraMap_eq, mul_assoc]

/-- If the entries of `a` are bounded by `H` and those of `b` by `T` in absolute value, then
each entry of the product `∑ i, a i * b i j` is bounded by `Fintype.card σ * H * T`. -/
lemma integerLinearForm_matrix_height {σ τ : Type*} [Fintype σ]
    (a : σ → ℤ) (b : σ → τ → ℤ) (H T : ℕ)
    (ha : ∀ i, |a i| ≤ H) (hb : ∀ i j, |b i j| ≤ T) (j : τ) :
    |∑ i, a i * b i j| ≤ Fintype.card σ * H * T := by
  calc
    _ ≤ ∑ i, |a i * b i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : σ, (H : ℤ) * T := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (ha i) (hb i j) (abs_nonneg _) (by positivity)
    _ = _ := by simp [mul_assoc]

end
end CCDN
