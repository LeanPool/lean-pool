/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.RemainderEnergy
public import LeanPool.NoncommutativeAMGM.Parseval

/-!
# Real averages over the root nodes

The explicit remainder energies equal weighted squared-polynomial averages.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Polynomial
open scoped BigOperators ComplexConjugate

/-- A real polynomial regarded as a complex polynomial. -/
noncomputable def complexify (p : Polynomial ℝ) : Polynomial ℂ := p.map Complex.ofRealHom

/-- Real-valued averaging on the nodes `ξζʲ`, `0 ≤ j < m`. -/
noncomputable def rootRealAverage (m : ℕ) (ξ ζ : ℂ) (f : ℂ → ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ j ∈ Finset.range m, f (ξ * ζ ^ j)

theorem rootRealAverage_mul (m : ℕ) (ξ ζ : ℂ) (a : ℝ) (f : ℂ → ℝ) :
    rootRealAverage m ξ ζ (fun z ↦ a * f z) = a * rootRealAverage m ξ ζ f := by
  simp only [rootRealAverage, ← Finset.mul_sum]
  ring

theorem rootRealAverage_div (m : ℕ) (ξ ζ : ℂ) (f : ℂ → ℝ) (a : ℝ) :
    rootRealAverage m ξ ζ (fun z ↦ f z / a) = rootRealAverage m ξ ζ f / a := by
  simp only [rootRealAverage, ← Finset.sum_div]
  ring

theorem rootRealAverage_sum {I : Type*} (s : Finset I) (m : ℕ) (ξ ζ : ℂ)
    (f : I → ℂ → ℝ) :
    rootRealAverage m ξ ζ (fun z ↦ ∑ i ∈ s, f i z) =
      ∑ i ∈ s, rootRealAverage m ξ ζ (f i) := by
  simp only [rootRealAverage, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem coefficientNormSq_complexify (p : Polynomial ℝ) :
    coefficientNormSq (complexify p) = realCoefficientInner p p := by
  simp only [coefficientNormSq, complexify, realCoefficientInner, Polynomial.sum_def,
    support_map_of_injective (f := Complex.ofRealHom) p Complex.ofReal_injective, coeff_map]
  change (∑ i ∈ p.support, ‖(p.coeff i : ℂ)‖ ^ 2) = ∑ i ∈ p.support, p.coeff i * p.coeff i
  simp only [Complex.norm_real, Real.norm_eq_abs]
  simp_rw [sq_abs, pow_two]

/-- Parseval for a real polynomial, including its full reduction modulo `Xᵐ-η`. -/
theorem rootRealAverage_square_eq_remainder {m : ℕ} (hm : 0 < m) {ξ ζ : ℂ} {η : ℝ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ)) (hη : η = 1 ∨ η = -1)
    (p : Polynomial ℝ) :
    rootRealAverage m ξ ζ (fun z ↦ ‖(complexify p).eval z‖ ^ 2) =
      realCoefficientInner (p %ₘ (X ^ m - C η)) (p %ₘ (X ^ m - C η)) := by
  have hηC : (η : ℂ) = 1 ∨ (η : ℂ) = -1 := by
    rcases hη with rfl | rfl <;> norm_num
  have hparse := root_remainder_coefficientNormSq hm hζ hξ hηC (complexify p)
  have hrem : complexify p %ₘ (X ^ m - C (η : ℂ)) =
      complexify (p %ₘ (X ^ m - C η)) := by
    simpa [complexify] using (map_modByMonic (p := p) Complex.ofRealHom
      (monic_X_pow_sub_C (n := m) η hm.ne')).symm
  rw [hrem, coefficientNormSq_complexify] at hparse
  have hcast : (rootRealAverage m ξ ζ (fun z ↦ ‖(complexify p).eval z‖ ^ 2) : ℂ) =
      rootPolynomialSquareAverage m ξ ζ (complexify p) := by
    simp only [rootRealAverage, rootPolynomialSquareAverage]
    push_cast
    simp only [Complex.conj_mul']
  exact Complex.ofReal_injective (hcast.trans hparse)

theorem complexify_differenceFamily_eval (R : Polynomial ℝ) (j : ℕ) (z : ℂ) :
    (complexify (differenceFamily R j)).eval z = (complexify R).eval z * (z ^ 2 - 1) ^ j := by
  simp [complexify, differenceFamily]

theorem differenceFamily_square_div (R : Polynomial ℝ) (j : ℕ) (z : ℂ) :
    ‖(complexify (differenceFamily R j)).eval z‖ ^ 2 / (4 : ℝ) ^ j =
      (‖z ^ 2 - 1‖ ^ 2 / 4) ^ j * ‖(complexify R).eval z‖ ^ 2 := by
  rw [complexify_differenceFamily_eval, norm_mul, norm_pow, mul_pow]
  have hp : (‖z ^ 2 - 1‖ ^ j) ^ 2 = (‖z ^ 2 - 1‖ ^ 2) ^ j := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm j 2]
  rw [hp, div_pow]
  ring

/-- Identification of the actual `Hⱼ` with the weighted root-node average. -/
theorem remainderEnergy_eq_rootRealAverage {m : ℕ} (hm : 0 < m) {ξ ζ : ℂ} {η : ℝ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ)) (hη : η = 1 ∨ η = -1)
    (R : Polynomial ℝ) (j : ℕ) :
    remainderEnergy R m η j = rootRealAverage m ξ ζ
      (fun z ↦ (‖z ^ 2 - 1‖ ^ 2 / 4) ^ j * ‖(complexify R).eval z‖ ^ 2) := by
  rw [remainderEnergy, ← rootRealAverage_square_eq_remainder hm hζ hξ hη,
    ← rootRealAverage_div]
  congr 1
  funext z
  exact differenceFamily_square_div R j z

end NoncommutativeAMGM
