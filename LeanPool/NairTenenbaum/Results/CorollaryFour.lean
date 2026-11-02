/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyWeightedMean
public import LeanPool.NairTenenbaum.NumberFields.IrreducibleSieveProduct

/-! # Corollary 4: short sums of powers of Hooley's function

For every `t≥1`, the logarithmic exponent is `2^t−t−1` and the
subexponential coefficient is every number greater than `sqrt(2t)`.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

theorem exists_hooleyPolynomialSum_sharp_bound {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {t ε η : ℝ}
    (ht : 1 ≤ t) (hε : 0 < ε) (hη : Real.sqrt (2 * t) < η) :
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ x y : ℝ,
      x₀ < x → x ^ ε ≤ y → y ≤ x →
        hooleyPolynomialSum Q t x y ≤
          C * (y * (Real.log x) ^ ((2 : ℝ) ^ t - t - 1) * hooleySubexponential η x) := by
  have hdeg : 0 < Q.natDegree := by
    rw [← natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective Q]
    exact hirr.natDegree_pos
  obtain ⟨x₁, A, _, hA, HA⟩ := exists_hooleyPolynomialSum_root_bound Q hQ hdeg hε (by
    linarith : 0 < t)
  obtain ⟨x₂, B, hx₂, hB, HB⟩ := exists_irreducible_sieveProduct_log_bound hQ hirr
  obtain ⟨x₃, C, _, hC, HC⟩ := exists_hooleyRootSum_sharp_bound hQ hirr ht hη
  refine ⟨max x₁ (max x₂ x₃), A * B * C,
    hx₂.trans_le ((le_max_left _ _).trans (le_max_right _ _)), mul_pos (mul_pos hA hB) hC,
    fun x y hx hy hyx => ?_⟩
  have hx₁ : x₁ < x := (le_max_left _ _).trans_lt hx
  have hx₂' : x₂ < x := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hx
  have hx₃ : x₃ < x := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hx
  have hl : 0 < Real.log x := Real.log_pos (hx₂.trans hx₂')
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) ε).trans hy
  have hR : 0 ≤ hooleyRootSum Q t x := by
    unfold hooleyRootSum
    exact Finset.sum_nonneg (fun n _ => by positivity)
  have Hpow : (Real.log x) ^ ((2 : ℝ) ^ t - t) / Real.log x =
      (Real.log x) ^ ((2 : ℝ) ^ t - t - 1) := by
    rw [Real.rpow_sub hl ((2 : ℝ) ^ t - t) 1, Real.rpow_one]
  calc
    _ ≤ A * (y * sieveProduct Q x * hooleyRootSum Q t x) := HA x y hx₁ hy hyx
    _ ≤ A * (y * (B / Real.log x) * (C * ((Real.log x) ^ ((2 : ℝ) ^ t - t) * hooleySubexponential
        η x))) := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left (HB x hx₂') hy₀) (HC x hx₃) hR (by positivity)
    _ = (A * B * C) * (y * ((Real.log x) ^ ((2 : ℝ) ^ t - t) / Real.log x) * hooleySubexponential
        η x) := by
      ring
    _ = _ := by rw [Hpow]

/-- The statement of Corollary 4, with the scope recorded in the source alignment. -/
def CorollaryFour : Prop :=
  ∀ Q : ℤ[X], NoFixedPrimeDivisor Q → Irreducible Q →
    ∀ t ε η : ℝ, 1 ≤ t → 0 < ε → Real.sqrt (2 * t) < η →
      ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ x y : ℝ,
        x₀ < x → x ^ ε ≤ y → y ≤ x →
          hooleyPolynomialSum Q t x y ≤
            C * (y * (Real.log x) ^ ((2 : ℝ) ^ t - t - 1) * hooleySubexponential η x)

theorem corollaryFour : CorollaryFour := by
  intro Q hQ hI t ε η ht hε hη
  exact exists_hooleyPolynomialSum_sharp_bound hQ (hQ.irreducible_map hI) ht hε hη

end NairTenenbaum
