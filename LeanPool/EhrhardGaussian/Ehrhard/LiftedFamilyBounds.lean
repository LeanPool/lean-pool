/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.CompactScalarBounds

/-! # Common interpolation bounds for finite scalar families pulled back by a matrix -/

@[expose] public noncomputable section

open EhrhardGaussian.Gaussian (coordinateDerivative)
open scoped BigOperators

namespace EhrhardGaussian.Ehrhard

/-- Linear lifts of a bounded smooth scalar family have uniform derivative and Ornstein–Uhlenbeck
generator bounds. -/
theorem lifted_family_bounds {n k : ℕ} {f : Fin k → ℝ → ℝ}
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hvalue : ∀ i y, |f i y| ≤ B)
    (hderiv : ∀ i y, |deriv (f i) y| ≤ M ∧ |deriv (deriv (f i)) y| ≤ M ∧
      |deriv (deriv (deriv (f i))) y| ≤ M ∧ |y * deriv (f i) y| ≤ M)
    (C : Matrix (Fin k) (Fin n) ℝ) :
    (∀ i, HasPolynomiallyBoundedThirdCoordinateDerivatives (f i ∘ coordinateForm (C i))) ∧
      ∃ A : ℝ, 0 ≤ A ∧ (∀ i x, ‖fderiv ℝ (f i ∘ coordinateForm (C i)) x‖ ≤ A) ∧
        (∀ i j l x, |coordinateDerivative (coordinateDerivative (f i ∘ coordinateForm (C i)) j) l x|
          ≤ A) ∧
        ∀ i x, |ouGenerator (f i ∘ coordinateForm (C i)) x| ≤ A := by
  have hregular (i) := hasPolynomiallyBoundedThird_scalar_comp (hf i) hB hM hM hM (hvalue i)
    (fun y => (hderiv i y).1) (fun y => (hderiv i y).2.1) (fun y => (hderiv i y).2.2.1) (C i)
  let N := fun i => ‖coordinateForm (C i)‖
  let V := fun i => ∑ j, C i j ^ 2
  let R := fun i => M * N i + M * N i ^ 2 + V i * M + M
  have hN (i) : 0 ≤ N i := norm_nonneg _
  have hV (i) : 0 ≤ V i := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hMN (i) : 0 ≤ M * N i := mul_nonneg hM (hN i)
  have hMN₂ (i) : 0 ≤ M * N i ^ 2 := mul_nonneg hM (sq_nonneg _)
  have hVM (i) : 0 ≤ V i * M := mul_nonneg (hV i) hM
  obtain ⟨Q, hQ⟩ := Finite.exists_le R
  have hRA (i) : R i ≤ max 0 Q := (hQ i).trans (le_max_right _ _)
  refine ⟨hregular, max 0 Q, le_max_left _ _, ?_, ?_, ?_⟩
  · intro i x
    apply (norm_fderiv_scalar_comp_le ((hf i).differentiable (by norm_num : (3 : WithTop ℕ∞) ≠ 0))
      (fun y => (hderiv i y).1) (C i) x).trans
    apply le_trans _ (hRA i)
    dsimp only [R]
    linarith only [hMN₂ i, hVM i, hM]
  · intro i j l x
    rw [secondCoordinateDerivative_scalar_comp ((hf i).of_le (by norm_num)), abs_mul]
    have hcoeff : |C i j * C i l| ≤ N i ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul (abs_coordinate_le_norm_coordinateForm (C i) j)
        (abs_coordinate_le_norm_coordinateForm (C i) l) (abs_nonneg _) (hN i)
    have hb := mul_le_mul hcoeff (hderiv i (coordinateForm (C i) x)).2.1 (abs_nonneg _) (sq_nonneg
      _)
    apply hb.trans
    apply le_trans _ (hRA i)
    dsimp only [R]
    nlinarith only [hMN i, hVM i, hM]
  · intro i x
    apply (abs_ouGenerator_scalar_comp_le ((hf i).of_le (by norm_num))
      (fun y => (hderiv i y).2.1) (fun y => (hderiv i y).2.2.2) (C i) x).trans
    apply le_trans _ (hRA i)
    dsimp only [R, V]
    linarith only [hMN i, hMN₂ i]

/-- A finite smooth scalar family with compactly supported derivatives has common derivative bounds.
-/
theorem exists_common_compact_scalar_bounds {k : ℕ} {f : Fin k → ℝ → ℝ}
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hcompact : ∀ i, HasCompactSupport (deriv (f i))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i y, |deriv (f i) y| ≤ M ∧ |deriv (deriv (f i)) y| ≤ M ∧
      |deriv (deriv (deriv (f i))) y| ≤ M ∧ |y * deriv (f i) y| ≤ M := by
  choose M hM hbound using fun i => exists_compact_scalar_derivative_bounds (hf i) (hcompact i)
  obtain ⟨Q, hQ⟩ := Finite.exists_le M
  refine ⟨max 0 Q, le_max_left _ _, ?_⟩
  intro i y
  have hi : M i ≤ max 0 Q := (hQ i).trans (le_max_right _ _)
  exact ⟨(hbound i y).1.trans hi, (hbound i y).2.1.trans hi,
    (hbound i y).2.2.1.trans hi, (hbound i y).2.2.2.trans hi⟩

end EhrhardGaussian.Ehrhard

end
