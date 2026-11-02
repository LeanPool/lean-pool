/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.SieveProductLowerBound

/-! # Absorbing a power saving into the main term -/

@[expose] public section

namespace NairTenenbaum

/-- The unit tuple is always an admissible term in the weight at one. -/
theorem PolynomialSystem.value_one_le_weight_one {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) : F 1 ≤ P.weight F 1 := by
  have hone : (1 : Tuple r) ∈ weightFiber P.exponent P.discriminant 1 := by
    rw [mem_weightFiber P.exponent P.exponent_pos]
    simp [Dagger]
  have H := Finset.single_le_sum (s := weightFiber P.exponent P.discriminant 1)
    (f := fun n => pullback P.exponent F n * ∏ i, P.rootVector i (n i) / (n i : ℝ))
    (fun n _ => mul_nonneg (hF _) (Finset.prod_nonneg (fun i _ => div_nonneg
      (Nat.cast_nonneg _) (by positivity)))) hone
  simpa only [Pi.one_apply, rootVector, PNat.val_ofNat, rootCount_one, Nat.cast_one,
    PNat.one_coe, div_self one_ne_zero, Finset.prod_const_one, mul_one, pullback,
    substitute_one, PolynomialSystem.weight, NairTenenbaum.weight] using H

theorem PolynomialSystem.value_one_le_weight_sum {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) {x : ℝ} (hx : 1 ≤ x) :
    F 1 ≤ ∑ n ∈ positiveUpTo x, P.weight F n := by
  apply (P.value_one_le_weight_one hF).trans
  exact Finset.single_le_sum (fun n _ => P.weight_nonneg hF n)
    ((mem_positiveUpTo 1 x).mpr (by simpa using hx))

/-- The inverse sieve estimate is equivalently a lower bound by every fixed
negative power, uniformly in the coefficients. -/
theorem exists_rpow_neg_le_sieveProduct (g : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : Polynomial ℤ, NoFixedPrimeDivisor Q → Q.natDegree ≤ g →
      ∀ x : ℝ, 2 ≤ x → x ^ (-δ) ≤ C * sieveProduct Q x := by
  obtain ⟨C, hC, H⟩ := exists_sieveProduct_inv_le_rpow g hδ
  refine ⟨C, hC, ?_⟩
  intro Q hQ hg x hx
  have hS := sieveProduct_pos hQ x
  have hx₀ : 0 < x := by linarith
  have H' := mul_le_mul_of_nonneg_right (H Q hQ hg x hx)
    (mul_nonneg (Real.rpow_nonneg hx₀.le (-δ)) hS.le)
  have hcancel : x ^ δ * x ^ (-δ) = 1 := by rw [← Real.rpow_add hx₀]; simp
  have hleft : (sieveProduct Q x)⁻¹ * (x ^ (-δ) * sieveProduct Q x) = x ^ (-δ) := by
    field_simp
  have hright : C * x ^ δ * (x ^ (-δ) * sieveProduct Q x) = C * sieveProduct Q x := by
    calc
      _ = C * (x ^ δ * x ^ (-δ)) * sieveProduct Q x := by ring
      _ = _ := by rw [hcancel, mul_one]
  rwa [hleft, hright] at H'

/-- A power-saving error times `F(1)` is dominated by the full main term,
without a normalization assumption on the arithmetic function. -/
theorem exists_powerSaving_le_mainTerm (g : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree ≤ g →
      ∀ (F : ArithmeticMap k), (∀ n, 0 ≤ F n) → ∀ x y : ℝ, 2 ≤ x → 0 ≤ y →
        y * x ^ (-δ) * F 1 ≤ C * mainTerm P F x y := by
  obtain ⟨C, hC, H⟩ := exists_rpow_neg_le_sieveProduct g hδ
  refine ⟨C, hC, ?_⟩
  intro k r P hg F hF x y hx hy
  have H' := mul_le_mul (H P.total P.noFixedPrime hg x hx)
    (P.value_one_le_weight_sum hF (x := x) (by linarith)) (hF 1)
    (mul_nonneg (zero_le_one.trans hC) (sieveProduct_pos P.noFixedPrime x).le)
  have H'' := mul_le_mul_of_nonneg_left H' hy
  simpa only [mainTerm, mul_assoc, mul_left_comm] using H''

end NairTenenbaum
