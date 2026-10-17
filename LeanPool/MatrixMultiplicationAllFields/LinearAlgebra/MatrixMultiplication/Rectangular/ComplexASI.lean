/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexEqualSummandASI
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialWitnessProduct

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Foundation

namespace Tensor

/-- Identify a standard set of L cubed tags with three independent L-valued tags. -/
def rectangularTagEquiv (L : ℕ) :
    Fin (L ^ 3) ≃ (Fin L × Fin L) × Fin L :=
  Fintype.equivOfCardEq (by simp [pow_succ])

/-- Identify a standard product-sized index set with the three rectangular coordinate sets. -/
def rectangularIndexEquiv (a b c : ℕ) :
    Fin (a * b * c) ≃ Fin a × Fin b × Fin c :=
  Fintype.equivOfCardEq (by simp [mul_assoc])

theorem matrixMultiplication_directSum_symmetrized_rank {a b c L r : ℕ}
    (h : RankAtMost (directSum (fun _ : Fin L => matrixMultiplication a b c)) r) :
    RankAtMost (directSum (fun _ : Fin (L ^ 3) =>
      matrixMultiplication (a * b * c) (a * b * c) (a * b * c))) (r ^ 3) := by
  have hs := matrixCoefficients_directSum_symmetrized_rank h
  exact matrixCoefficients_directSum_rank_of_injective hs
    (rectangularTagEquiv L) (rectangularTagEquiv L).injective
    (rectangularIndexEquiv a b c) (rectangularIndexEquiv a b c).injective

/-- Pull a direct-sum matrix tensor approximation back along injective tag and coordinate
maps. -/
def PolynomialApproximation.matrixCoefficientsDirectSumOfInjective
    {F ι κ A B : Type*} [Field F]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq A] [DecidableEq B] {r d D : ℕ}
    (P : PolynomialApproximation
      (directSum (fun _ : ι => matrixCoefficients (K := F) A A A)) r d D)
    (f : κ → ι) (hf : Function.Injective f) (g : B → A) (hg : Function.Injective g) :
    PolynomialApproximation
      (directSum (fun _ : κ => matrixCoefficients (K := F) B B B)) r d D := by
  let coord : κ × (B × B) → ι × (A × A) :=
    fun x => (f x.1, (g x.2.1, g x.2.2))
  have heq : Tensor.pullback coord coord coord
      (directSum (fun _ : ι => matrixCoefficients (K := F) A A A)) =
      directSum (fun _ : κ => matrixCoefficients (K := F) B B B) := by
    funext x y z
    simp only [Tensor.pullback, coord, directSum, matrixCoefficients, hf.eq_iff, hg.eq_iff]
  rw [← heq]
  exact P.pullback coord coord coord

/-- Symmetrize a direct sum of finite rectangular matrix multiplication tensors into square
ones. -/
def PolynomialApproximation.matrixMultiplicationDirectSumSymmetrized
    {a b c L r d D : ℕ}
    (P : PolynomialApproximation
      (directSum (fun _ : Fin L => matrixMultiplication a b c)) r d D) :
    PolynomialApproximation (directSum (fun _ : Fin (L ^ 3) =>
      matrixMultiplication (a * b * c) (a * b * c) (a * b * c)))
      (r ^ 3) (3 * d) (3 * D) :=
  P.matrixCoefficientsDirectSumSymmetrized.matrixCoefficientsDirectSumOfInjective
    (rectangularTagEquiv L) (rectangularTagEquiv L).injective
    (rectangularIndexEquiv a b c) (rectangularIndexEquiv a b c).injective

end Tensor

theorem mul_rpow_third_le_of_cube {u v w r : ℝ} (hv : 0 ≤ v) (hr : 0 ≤ r)
    (h : u ^ 3 * v ^ w ≤ r ^ 3) : u * v ^ (w / 3) ≤ r := by
  have hpow : (v ^ (w / 3)) ^ (3 : ℕ) = v ^ w := by
    rw [← Real.rpow_mul_natCast hv]
    congr 1
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hr
  simpa only [mul_pow, hpow] using h

namespace Arithmetic

theorem equalRectangular_inequality {a b c L r : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : Tensor.RankAtMost
      (Tensor.directSum (fun _ : Fin L => Tensor.matrixMultiplication a b c)) r) :
    (L : ℝ) * ((a * b * c : ℕ) : ℝ) ^ (omega / 3) ≤ (r : ℝ) := by
  have hv : 1 ≤ a * b * c := Nat.mul_pos (Nat.mul_pos ha hb) hc
  have hs := equalSummand_inequality hv
    (Tensor.matrixMultiplication_directSum_symmetrized_rank h)
  apply mul_rpow_third_le_of_cube (Nat.cast_nonneg (a * b * c)) (Nat.cast_nonneg r)
  simpa only [Nat.cast_pow] using hs

theorem equalRectangular_inequality_of_polynomialApproximation
    {a b c L r d D : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (P : Tensor.PolynomialApproximation
      (Tensor.directSum (fun _ : Fin L => Tensor.matrixMultiplication a b c)) r d D) :
    (L : ℝ) * ((a * b * c : ℕ) : ℝ) ^ (omega / 3) ≤ (r : ℝ) := by
  have hv : 1 ≤ a * b * c := Nat.mul_pos (Nat.mul_pos ha hb) hc
  have hs := equalSummand_inequality_of_polynomialApproximation hv
    P.matrixMultiplicationDirectSumSymmetrized
  apply mul_rpow_third_le_of_cube (Nat.cast_nonneg (a * b * c)) (Nat.cast_nonneg r)
  simpa only [Nat.cast_pow] using hs

end Arithmetic

end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
