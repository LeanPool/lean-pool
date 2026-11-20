/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.ChebyshevQuadrature

/-! # Real Chebyshev moments of the root-node quadratures -/

@[expose] public section
open Polynomial Polynomial.Chebyshev
open scoped ComplexConjugate BigOperators
namespace NoncommutativeAMGM
theorem chebyshev_unitCircle_eval (r : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    2 * Complex.ofReal ((T ℝ (r : ℤ)).eval z.re) = z ^ r + (conj z) ^ r := by
  induction r using Nat.twoStepInduction with
  | zero => norm_num
  | one =>
    simpa using (Complex.add_conj z).symm
  | more r ih ih1 =>
    have ht := congrArg (fun p : Polynomial ℝ ↦ Complex.ofReal (p.eval z.re))
      (T_add_two ℝ (r : ℤ))
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at ht
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat] at ht
    have hc : z * conj z = 1 := by simpa [hz] using Complex.mul_conj' z
    have ha : z + conj z = 2 * (z.re : ℂ) := by simpa using Complex.add_conj z
    have hr : ((r + 2 : ℕ) : ℤ) = (r : ℤ) + 2 := by omega
    rw [hr, ht]
    calc
      _ = (z + conj z) * (2 * Complex.ofReal ((T ℝ ((r + 1 : ℕ) : ℤ)).eval z.re)) -
          2 * Complex.ofReal ((T ℝ (r : ℤ)).eval z.re) := by
        rw [show ((r + 1 : ℕ) : ℤ) = (r : ℤ) + 1 by omega, ha]
        ring
      _ = (z + conj z) * (z ^ (r + 1) + conj z ^ (r + 1)) - (z ^ r + conj z ^ r) := by
        rw [ih, ih1]
      _ = z ^ (r + 2) + conj z ^ (r + 2) := by
        simp only [pow_succ]
        linear_combination (z ^ r + conj z ^ r) * hc
theorem rootMonomialAverage_nat_le {m : ℕ} (hm : 0 < m) {ξ ζ η : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = η) (hη : η = 1 ∨ η = -1)
    (r : ℕ) (hr : r ≤ m) :
    rootMonomialAverage m ξ ζ (r : ℤ) = if r = 0 then 1 else if r = m then η else 0 := by
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hrZ : (r : ℤ) ≤ m := by exact_mod_cast hr
  rw [rootMonomialAverage_three hm hζ hξ hη (by omega) (by omega)]
  have hneg : (r : ℤ) ≠ -(m : ℤ) := by omega
  by_cases h0 : r = 0
  · subst r
    simp [hm.ne', Ne.symm (ne_of_gt hmZ)]
  · by_cases he : r = m
    · subst r
      simp [hm.ne', hneg]
    · simp [h0, he, hneg]

/-- A root-grid average of `Tᵣ(Re z)` retains only the constant mode and the `m`th mode. -/
theorem rootRealAverage_chebyshev {m : ℕ} (hm : 0 < m) {ξ ζ : ℂ} {η : ℝ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ)) (hη : η = 1 ∨ η = -1)
    (r : ℕ) (hr : r ≤ m) :
    rootRealAverage m ξ ζ (fun z ↦ (T ℝ (r : ℤ)).eval z.re) =
      if r = 0 then 1 else if r = m then η else 0 := by
  classical
  have hηC : (η : ℂ) = 1 ∨ (η : ℂ) = -1 := by
    rcases hη with rfl | rfl <;> norm_num
  have hs : (∑ j ∈ Finset.range m,
      2 * Complex.ofReal ((T ℝ (r : ℤ)).eval (ξ * ζ ^ j).re)) =
      ∑ j ∈ Finset.range m, ((ξ * ζ ^ j) ^ r + conj (ξ * ζ ^ j) ^ r) := by
    apply Finset.sum_congr rfl
    intro j _
    exact chebyshev_unitCircle_eval r _ (root_node_norm hm hζ hξ hηC j)
  have hc : 2 * (rootRealAverage m ξ ζ (fun z ↦ (T ℝ (r : ℤ)).eval z.re) : ℂ) =
      rootMonomialAverage m ξ ζ (r : ℤ) + conj (rootMonomialAverage m ξ ζ (r : ℤ)) := by
    calc
      _ = (m : ℂ)⁻¹ * ∑ j ∈ Finset.range m,
          2 * Complex.ofReal ((T ℝ (r : ℤ)).eval (ξ * ζ ^ j).re) := by
        simp only [rootRealAverage, Complex.ofReal_mul, Complex.ofReal_inv,
          Complex.ofReal_natCast, Complex.ofReal_sum, ← Finset.mul_sum]
        ring
      _ = _ := by
        rw [hs]
        simp only [rootMonomialAverage, zpow_natCast, map_mul, map_inv₀, map_natCast,
          map_sum, map_pow, Finset.sum_add_distrib, mul_add]
  let v : ℝ := if r = 0 then 1 else if r = m then η else 0
  have hmono : rootMonomialAverage m ξ ζ (r : ℤ) = (v : ℂ) := by
    have he := rootMonomialAverage_nat_le hm hζ hξ hηC r hr
    by_cases h0 : r = 0 <;> by_cases hrm : r = m <;> simpa [v, h0, hrm, hm.ne'] using he
  rw [hmono, Complex.conj_ofReal] at hc
  apply Complex.ofReal_injective
  change (rootRealAverage m ξ ζ (fun z ↦ (T ℝ (r : ℤ)).eval z.re) : ℂ) = (v : ℂ)
  linear_combination (1 / 2 : ℂ) * hc

end NoncommutativeAMGM
