/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.SliceCoefficientPolynomial
public import LeanPool.NoncommutativeAMGM.UnitCircleLift
public import LeanPool.NoncommutativeAMGM.RootCoefficientExtraction

/-! # Positivity of the root-node averages of interpolated slice squares -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

theorem betaProduct_eq_prod (n : ℝ) (k : ℕ) (hk : 1 ≤ k) (u : ℝ) :
    betaProduct n k u = ∏ l ∈ Finset.range k, (u - beta n l) := by
  classical
  unfold betaProduct betaList
  rw [List.map_map]
  change u * ((List.range (k - 1)).map (fun i ↦ u - beta n (i + 1))).prod = _
  rw [← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  have he := Finset.prod_range_succ' (fun i ↦ u - beta n i) (k - 1)
  rw [Nat.sub_add_cancel hk] at he
  rw [he, beta_zero, sub_zero]
  ring

/-- The weighted average of a single coefficient square after the slice-coordinate change. -/
theorem root_slice_weighted_polynomial_nonneg {ξ ζ : ℂ} {η : ℝ}
    (p : Polynomial ℝ) (n m d k : ℕ) (hn : 0 < n) (hm : 2 ≤ m)
    (hk : k ≤ d) (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ))
    (hη : η = 1 ∨ η = -1) (hp : p.natDegree ≤ d - k)
    (hdm : 2 * d ≤ m + 1) (hnd : 2 * d ^ 2 ≤ n) :
    0 ≤ rootRealAverage m ξ ζ (fun z ↦
      (falling ((n : ℝ) / 2 * (1 - z.re)) k *
        falling ((n : ℝ) - (n : ℝ) / 2 * (1 - z.re)) k / falling n (2 * k)) *
          (p.eval ((n : ℝ) / 2 * (1 - z.re))) ^ 2) := by
  classical
  by_cases hk0 : k = 0
  · subst k
    unfold rootRealAverage
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m))
    apply Finset.sum_nonneg
    intro j _
    simp only [Nat.mul_zero, falling_zero, one_mul, div_one]
    exact sq_nonneg _
  · let q := p.comp (sliceCoordinatePolynomial n)
    have hq : q.natDegree ≤ d - k := by
      calc
        _ ≤ p.natDegree * (sliceCoordinatePolynomial n).natDegree := natDegree_comp_le
        _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ (sliceCoordinatePolynomial_natDegree n)
        _ ≤ d - k := by simpa using hp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hndR : 2 * (((d - k) + k : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) := by
      rw [Nat.sub_add_cancel hk]
      exact_mod_cast hnd
    have hpos := real_polynomial_quadrature_nonneg q (n : ℝ) m (d - k) k hm
      (by omega) hζ hξ hη hq (by omega) hn0 hndR
    have heq : rootRealAverage m ξ ζ (fun z ↦
        (falling ((n : ℝ) / 2 * (1 - z.re)) k *
          falling ((n : ℝ) - (n : ℝ) / 2 * (1 - z.re)) k / falling n (2 * k)) *
            (p.eval ((n : ℝ) / 2 * (1 - z.re))) ^ 2) =
        ((n : ℝ) ^ 2 / 4) ^ k / falling n (2 * k) *
          rootRealAverage m ξ ζ (fun z ↦ betaProduct n k (1 - z.re ^ 2) *
            (q.eval z.re) ^ 2) := by
      rw [← rootRealAverage_mul]
      congr 1
      funext z
      have hs : (n : ℝ) - (n : ℝ) / 2 * (1 - z.re) =
          (n : ℝ) / 2 * (1 + z.re) := by ring
      rw [hs, slice_weight_factorization (n : ℝ) z.re hn0.ne' k,
        betaProduct_eq_prod (n : ℝ) k (by omega)]
      simp only [q, eval_comp, sliceCoordinatePolynomial_eval]
      ring
    rw [heq]
    exact mul_nonneg (slice_prefactor_nonneg n k) hpos

/-- Positivity of the actual root-grid slice quadrature on Boolean squares.
This combines the full harmonic norm formula with the quadratic weighted estimate. -/
theorem rootSliceFunctional_square_nonneg {ξ ζ : ℂ} {η : ℝ} {n m d : ℕ}
    (f : BooleanPolynomial n) (hn : 0 < n) (hm : 2 ≤ m)
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ)) (hη : η = 1 ∨ η = -1)
    (hf : BooleanDegreeLE f d) (hdn : 2 * d ≤ n)
    (hdm : 2 * d ≤ m + 1) (hnd : 2 * d ^ 2 ≤ n) :
    0 ≤ rootSliceFunctional n m ξ ζ (f ^ 2) := by
  obtain ⟨p, hp, he⟩ := exists_harmonic_norm_polynomials f hn hdn hf
  unfold rootSliceFunctional
  simp_rw [he]
  rw [rootRealAverage_sum]
  apply Finset.sum_nonneg
  intro k hk
  simp_rw [Finset.mul_sum]
  rw [rootRealAverage_sum]
  apply Finset.sum_nonneg
  intro S _
  exact root_slice_weighted_polynomial_nonneg (p k S) n m d k hn hm
    (by have := Finset.mem_range.mp hk; omega) hζ hξ hη (hp k S) hdm hnd

end NoncommutativeAMGM
