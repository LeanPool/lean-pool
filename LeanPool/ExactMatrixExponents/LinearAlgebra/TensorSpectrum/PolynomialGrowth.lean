/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagPolynomialBranches
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorCharacterPermutationPowers
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Weighted

/-!
# The weighted growth bound for actual tensor characters

Use the optimized tag inequality on the determinant and tripling
degenerations for each leg permutation separately.
-/

@[expose] public section

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixExponent.Rectangle

namespace MatrixMultiplicationAllFields.TensorSpectrum.PolynomialGrowth

open TensorClass TagHeterogeneous
open PolynomialTensors (polynomialTensor determinantGradedTensor triplingSectorTensor)

variable {K : Type} [CommRing K]

/-- The quantity computed by `f (ofTensor (polynomialTensor (m + 1) (n + 1)))`. -/
def poly (f : Character K) (m n : ℕ) : ℝ :=
  f (ofTensor (polynomialTensor (m + 1) (n + 1)))

section Bounds

variable (hpositive :
  ∀ (f : Character K) (a b : ℕ), 1 ≤ a → 1 ≤ b →
    0 < (f (ofTensor (polynomialTensor a b)) : ℝ))

include hpositive in
/-- Positivity for every padded determinant branch follows from the already
established positive polynomial character values. -/
private theorem determinant_family_value_pos (f : Character K) (a b : ℕ) (j : Fin 2) :
    0 < (f (TensorClass.ofTensor
      (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b) j)) : ℝ) := by
  rw [ofTensor_determinant_family]
  fin_cases j <;> simp only
  · exact hpositive f _ _ (by omega) (by omega)
  · exact hpositive f _ _ (by omega) (by omega)

include hpositive in
/-- The positive middle value uses the actual permuted character. -/
private theorem tripling_middle_value_pos (f : Character K) (a h : ℕ)
    (ha : 1 ≤ a) (hh : 1 ≤ h) :
    0 < (f (TensorClass.ofTensor (triplingMiddleTensor a h)) : ℝ) := by
  rw [ofTensor_triplingMiddle]
  have hp := hpositive (f.permuted 2) a h ha hh
  simpa [TensorClass.Character.permuted_apply, TensorClass.permute,
    TensorClass.permuteHom, TensorClass.swapYZHom] using hp

include hpositive in
/-- These strict positive values are the hypotheses of the uniform tag
inequality, including the padded and reversed middle branch. -/
private theorem tripling_family_value_pos (f : Character K) (a h : ℕ)
    (ha : 1 ≤ a) (hh : 1 ≤ h) (j : Fin 3) :
    0 < (f (TensorClass.ofTensor
      (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h)
        (polynomialTensor a h) j)) : ℝ) := by
  rw [ofTensor_threeFamily]
  fin_cases j <;> simp only
  · exact hpositive f _ _ ha hh
  · exact tripling_middle_value_pos hpositive f a h ha hh
  · exact hpositive f _ _ ha hh

include hpositive in
private theorem poly_pos (f : Character K) (m n : ℕ) : 0 < poly f m n :=
  hpositive f _ _ (by omega) (by omega)

variable (htag :
  ∀ (f : Character K) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {s : ℕ}, 0 < s → ∀ A : Fin s → Tensor K X Y Z,
    (∀ i, 0 < (f (ofTensor (A i)) : ℝ)) → 0 < f.pX →
    (∑ i, (f (ofTensor (A i)) : ℝ) ^ (1 / f.pX)) ^ f.pX ≤
      (f (ofTensor (Tensor.sharedFirst A)) : ℝ))

variable (hdet :
  ∀ (f : Character K) (a b : ℕ),
    (f (ofTensor (determinantGradedTensor a b)) : ℝ) ≤
      (2 : ℝ) ^ f.pX * (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ))

include hpositive htag hdet in
private theorem concave (f : Character K) (hp : 0 < f.pX) (m n : ℕ) :
    poly f m (n + 2) ^ (1 / f.pX) + poly f m n ^ (1 / f.pX) ≤
      2 * poly f m (n + 1) ^ (1 / f.pX) := by
  have h := htag f (by decide : 0 < 2) _
    (determinant_family_value_pos hpositive f m n) hp
  rw [ofTensor_determinant_uniform] at h
  have ht := h.trans (hdet f m n)
  simp only [ofTensor_determinant_family, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at ht
  change (poly f m (n + 2) ^ (1 / f.pX) + poly f m n ^ (1 / f.pX)) ^ f.pX ≤
    (2 : ℝ) ^ f.pX * poly f m (n + 1) at ht
  have h₁ := poly_pos hpositive f m n
  have h₂ := poly_pos hpositive f m (n + 2)
  have he := root_le hp (by positivity) ht
  rwa [Real.mul_rpow (by positivity) (poly_pos hpositive f _ _).le, ← Real.rpow_mul (by norm_num),
    mul_one_div_cancel hp.ne', Real.rpow_one] at he

variable (htrip :
  ∀ (f : Character K) (a h : ℕ), 1 ≤ a → 1 ≤ h →
    (f (ofTensor (triplingSectorTensor a h)) : ℝ) ≤
      (f (ofTensor (polynomialTensor a (3 * h + a - 1))) : ℝ))

include hpositive htag hdet htrip in
theorem poly_row (f : Character K) (hp : 0 < f.pX) (m : ℕ) :
    Row (fun n => poly f m n ^ (1 / f.pX))
      (fun n => (f (swapYZ (ofTensor (polynomialTensor (m + 1) (n + 1)))) : ℝ) ^ (1 / f.pX)) m := by
  refine ⟨fun n => Real.rpow_pos_of_pos (poly_pos hpositive f _ _) _, ?_, ?_⟩
  · apply antitone_nat_of_succ_le
    intro n
    simp only [TensorSpectrum.rowDifference, Nat.add_assoc, Nat.reduceAdd]
    linarith only [concave hpositive htag hdet f hp m n]
  · intro n
    have h := htag f (by decide : 0 < 3) _
      (tripling_family_value_pos hpositive f (m + 1) (n + 1) (by omega) (by omega)) hp
    rw [ofTensor_tripling_uniform] at h
    have ht := h.trans (htrip f (m + 1) (n + 1) (by omega) (by omega))
    simp only [ofTensor_tripling_family, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at ht
    rw [show 3 * (n + 1) + (m + 1) - 1 = (3 * n + m + 2) + 1 by omega] at ht
    have he := root_le hp (by positivity) ht
    unfold poly
    linarith only [he]

private def price (f : Character K) (i : Fin 6) (m n : ℕ) : ℝ :=
  Real.log (poly (f.permuted i) m n)

variable (hupper :
  ∀ (f : Character K) (a b : ℕ), 1 ≤ a → 1 ≤ b →
    (f (ofTensor (polynomialTensor a b)) : ℝ) ≤ (a : ℝ) + (b : ℝ) - 1)

include hpositive hupper in
private theorem price_bound (f : Character K) (i : Fin 6) : LogBound (price f i) := by
  intro m n
  apply Real.log_le_log (poly_pos hpositive _ _ _)
  have h := hupper (f.permuted i) (m + 1) (n + 1) (by omega) (by omega)
  push_cast at h
  unfold poly
  linarith

private theorem price_swap (f : Character K) (i : Fin 6) :
    Function.swap (price f i) = price f (permuteSwapXY i) := by
  funext m n
  unfold Function.swap price poly
  rw [← swapXY_polynomialTensor (m + 1) (n + 1), f.permuted_swapXY]

include hpositive htag hdet htrip in
private theorem paired_prices (f : Character K) (i j : Fin 6) {d : ℝ}
    (hd : 0 < d) (hi : (f.permuted i).pX = d) (hj : (f.permuted j).pX = d)
    (hij : permuteSwapYZ i = j) (hji : permuteSwapYZ j = i) :
    Increments (price f i) (price f j) d := by
  apply increments_of_rows hd (poly_pos hpositive _) (poly_pos hpositive _)
  · intro m
    have h := poly_row hpositive htag hdet htrip (f.permuted i) (hi.symm ▸ hd) m
    simp only [hi, f.permuted_swapYZ, hij] at h
    exact h
  · intro m
    have h := poly_row hpositive htag hdet htrip (f.permuted j) (hj.symm ▸ hd) m
    simp only [hj, f.permuted_swapYZ, hji] at h
    exact h

include hpositive htag hdet htrip hupper in
theorem character_bound (f : Character K) (A B C : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    4 * (f.pX * B * C + f.pY * A * C + f.pZ * A * B) ≤ ((A : ℝ) + B + C) ^ 2 := by
  have h (x : ℝ) (hx : x ≤ 1) (i j : ℕ) : x * i * j ≤ (i : ℝ) * j :=
    mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (by positivity) hx) (by positivity)
  have h₁ := h _ f.pX_le_one B C
  have h₂ := h _ f.pY_le_one A C
  have h₃ := h _ f.pZ_le_one A B
  rcases eq_or_lt_of_le f.pX_nonneg with hx | hx
  · rw [← hx]
    linarith only [h₂, h₃, sq_nonneg ((A : ℝ) - B - C)]
  rcases eq_or_lt_of_le f.pY_nonneg with hy | hy
  · rw [← hy]
    linarith only [h₁, h₃, sq_nonneg ((B : ℝ) - A - C)]
  rcases eq_or_lt_of_le f.pZ_nonneg with hz | hz
  · rw [← hz]
    linarith only [h₁, h₂, sq_nonneg ((C : ℝ) - A - B)]
  refine weighted_growth hx.le hy.le hz.le ?_ ?_ ?_
    (price_bound hpositive hupper f 0) (price_bound hpositive hupper f 2)
    (price_bound hpositive hupper f 3) hA hB hC
  · exact paired_prices hpositive htag hdet htrip f 0 2 hx
      (by rw [f.permuted_pX]; rfl) (by rw [f.permuted_pX]; rfl) rfl rfl
  · rw [price_swap]
    exact paired_prices hpositive htag hdet htrip f 1 3 hy
      (by rw [f.permuted_pX]; rfl) (by rw [f.permuted_pX]; rfl) rfl rfl
  · rw [price_swap, price_swap]
    exact paired_prices hpositive htag hdet htrip f 4 5 hz
      (by rw [f.permuted_pX]; rfl) (by rw [f.permuted_pX]; rfl) rfl rfl

end Bounds

end MatrixMultiplicationAllFields.TensorSpectrum.PolynomialGrowth
