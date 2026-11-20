/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.RootPositivity

/-! # Polynomial lifting from the real interval to the unit circle -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators ComplexConjugate

theorem unitCircle_weight (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z ^ 2 - 1‖ ^ 2 / 4 = 1 - z.re ^ 2 := by
  have hs : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, pow_two, Complex.mul_re, Complex.one_re,
    Complex.sub_im, Complex.mul_im, Complex.one_im, sub_zero]
  nlinarith [sq_nonneg (z.re ^ 2 + z.im ^ 2 - 1)]

theorem unitCircle_quadratic (z : ℂ) (hz : ‖z‖ = 1) :
    z ^ 2 + 1 = (2 * (z.re : ℂ)) * z := by
  have hc := Complex.mul_conj' z
  rw [hz] at hc
  have ha := Complex.add_conj z
  push_cast at ha
  calc
    z ^ 2 + 1 = (z + conj z) * z := by
      have hc1 : z * conj z = 1 := by simpa using hc
      rw [← hc1]
      ring
    _ = (2 * (z.re : ℂ)) * z := by rw [ha]

/-- `zʰ p((z+z⁻¹)/2)`, expressed as an ordinary polynomial. -/
noncomputable def unitCircleLift (h : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ r ∈ Finset.range (h + 1),
    C (p.coeff r / (2 : ℝ) ^ r) * X ^ (h - r) * (X ^ 2 + 1) ^ r

theorem unitCircleLift_natDegree (h : ℕ) (p : Polynomial ℝ) :
    (unitCircleLift h p).natDegree ≤ 2 * h := by
  apply natDegree_sum_le_of_forall_le
  intro r hr
  have hrh : r ≤ h := by have := Finset.mem_range.mp hr; omega
  have ha : (X ^ 2 + (1 : Polynomial ℝ)).natDegree ≤ 2 := by
    simp
  have hb : (C (p.coeff r / (2 : ℝ) ^ r) * X ^ (h - r) : Polynomial ℝ).natDegree ≤ h - r := by
    calc
      _ ≤ (C (p.coeff r / (2 : ℝ) ^ r) : Polynomial ℝ).natDegree +
          (X ^ (h - r) : Polynomial ℝ).natDegree := natDegree_mul_le
      _ ≤ h - r := by simp
  calc
    _ ≤ (C (p.coeff r / (2 : ℝ) ^ r) * X ^ (h - r) : Polynomial ℝ).natDegree +
        ((X ^ 2 + 1 : Polynomial ℝ) ^ r).natDegree := natDegree_mul_le
    _ ≤ (h - r) + 2 * r := by
      rw [natDegree_pow]
      exact Nat.add_le_add hb ((by nlinarith [Nat.mul_le_mul_left r ha]))
    _ ≤ 2 * h := by omega

theorem unitCircleLift_eval (h : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ h)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (complexify (unitCircleLift h p)).eval z = z ^ h * Complex.ofReal (p.eval z.re) := by
  have he : p.eval z.re = ∑ r ∈ Finset.range (h + 1), p.coeff r * z.re ^ r :=
    eval_eq_sum_range' (by omega) _
  simp only [complexify, unitCircleLift, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_add,
    Polynomial.map_one, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one]
  rw [he]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrh : r ≤ h := by have := Finset.mem_range.mp hr; omega
  change (↑(p.coeff r / (2 : ℝ) ^ r) : ℂ) * z ^ (h - r) * (z ^ 2 + 1) ^ r = _
  push_cast
  rw [unitCircle_quadratic z hz, mul_pow, mul_pow]
  have hzpow : z ^ (h - r) * z ^ r = z ^ h := by rw [← pow_add, Nat.sub_add_cancel hrh]
  have htwo : (2 : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  linear_combination (p.coeff r : ℂ) * (z.re : ℂ) ^ r * hzpow

theorem unitCircleLift_square (h : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ h)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(complexify (unitCircleLift h p)).eval z‖ ^ 2 = (p.eval z.re) ^ 2 := by
  rw [unitCircleLift_eval h p hp z hz, norm_mul, norm_pow, hz]
  simp only [one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The real-polynomial weighted quadrature inequality underlying equation (29).
The root parametrization includes both signs of the parity quadrature. -/
theorem real_polynomial_quadrature_nonneg {ξ ζ : ℂ} {η : ℝ}
    (p : Polynomial ℝ) (n : ℝ) (m h k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ)) (hη : η = 1 ∨ η = -1)
    (hp : p.natDegree ≤ h) (hkm : 2 * (h + k) ≤ m + 1)
    (hn0 : 0 < n) (hn : 2 * ((h + k : ℕ) : ℝ) ^ 2 ≤ n) :
    0 ≤ rootRealAverage m ξ ζ (fun z ↦
      betaProduct n k (1 - z.re ^ 2) * (p.eval z.re) ^ 2) := by
  have hηC : (η : ℂ) = 1 ∨ (η : ℂ) = -1 := by
    rcases hη with rfl | rfl <;> norm_num
  have hpos := root_weighted_square_nonneg (unitCircleLift h p) n m h k hm hk
    hζ hξ hη (unitCircleLift_natDegree h p) hkm hn0 hn
  have heq : rootRealAverage m ξ ζ (fun z ↦
      betaProduct n k (‖z ^ 2 - 1‖ ^ 2 / 4) *
        ‖(complexify (unitCircleLift h p)).eval z‖ ^ 2) =
      rootRealAverage m ξ ζ (fun z ↦
        betaProduct n k (1 - z.re ^ 2) * (p.eval z.re) ^ 2) := by
    unfold rootRealAverage
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hz := root_node_norm (by omega : 0 < m) hζ hξ hηC j
    dsimp only
    rw [unitCircle_weight _ hz, unitCircleLift_square h p hp _ hz]
  rwa [heq] at hpos

end NoncommutativeAMGM
