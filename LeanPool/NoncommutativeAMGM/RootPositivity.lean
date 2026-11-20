/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.RealRootQuadrature

/-!
# Positivity of the weighted root quadratures

The scalar quadrature conclusion of Sections 3.3–3.6, proved for actual polynomial
inputs and root-node averages, with no assumed harmonic or norm identities.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Polynomial
open scoped BigOperators

theorem list_product_differences (bs : List ℝ) (u : ℝ) :
    (bs.map (fun b ↦ u - b)).prod = ∑ l ∈ Finset.range (bs.length + 1),
      (-1 : ℝ) ^ l * elementarySum bs l * u ^ (bs.length - l) := by
  have ht := congrArg (Polynomial.eval u)
    (Multiset.prod_X_sub_X_eq_sum_esymm (bs : Multiset ℝ))
  simpa [eval_multiset_prod, Multiset.map_map, Function.comp_def,
    elementarySum_eq_esymm, mul_assoc, eval_list_prod, eval_finsetSum] using ht

/-- The product with the zero coefficient `β₀` separated out. -/
noncomputable def betaProduct (n : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  u * ((betaList n k).map (fun b ↦ u - b)).prod

theorem betaProduct_expansion (n : ℝ) (k : ℕ) (hk : 1 ≤ k) (u : ℝ) :
    betaProduct n k u = ∑ l ∈ Finset.range k,
      (-1 : ℝ) ^ l * symmetricBeta n k l * u ^ (k - l) := by
  have hlen : (betaList n k).length = k - 1 := by simp [betaList]
  rw [betaProduct, list_product_differences, Finset.mul_sum, hlen, Nat.sub_add_cancel hk]
  apply Finset.sum_congr rfl
  intro l hl
  have hlk : l < k := Finset.mem_range.mp hl
  change u * ((-1 : ℝ) ^ l * symmetricBeta n k l * u ^ (k - 1 - l)) = _
  rw [show k - l = (k - 1 - l) + 1 by omega, pow_succ]
  ring

/-- The weighted root average is exactly the alternating sum of the actual energies. -/
theorem root_betaProduct_average {m : ℕ} (hm : 0 < m) {ξ ζ : ℂ} {η : ℝ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ)) (hη : η = 1 ∨ η = -1)
    (R : Polynomial ℝ) (n : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    rootRealAverage m ξ ζ (fun z ↦ betaProduct n k (‖z ^ 2 - 1‖ ^ 2 / 4) *
      ‖(complexify R).eval z‖ ^ 2) =
      remainderEnergy R m η k + ∑ i ∈ Finset.range (k - 1),
        (-1 : ℝ) ^ (i + 1) * symmetricBeta n k (i + 1) *
          remainderEnergy R m η (k - (i + 1)) := by
  have hexpand : rootRealAverage m ξ ζ (fun z ↦
      betaProduct n k (‖z ^ 2 - 1‖ ^ 2 / 4) * ‖(complexify R).eval z‖ ^ 2) =
      rootRealAverage m ξ ζ (fun z ↦ ∑ l ∈ Finset.range k,
        ((-1 : ℝ) ^ l * symmetricBeta n k l) *
          ((‖z ^ 2 - 1‖ ^ 2 / 4) ^ (k - l) * ‖(complexify R).eval z‖ ^ 2)) := by
    congr 1
    funext z
    rw [betaProduct_expansion n k hk, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hexpand, rootRealAverage_sum]
  simp_rw [rootRealAverage_mul, ← remainderEnergy_eq_rootRealAverage hm hζ hξ hη]
  have hs := Finset.sum_range_succ' (fun l ↦
    (-1 : ℝ) ^ l * symmetricBeta n k l * remainderEnergy R m η (k - l)) (k - 1)
  rw [Nat.sub_add_cancel hk] at hs
  rw [hs]
  have hS0 : symmetricBeta n k 0 = 1 := elementarySum_zero _
  simp only [pow_zero, hS0, one_mul, Nat.sub_zero]
  ring

/-- The weighted quadrature is nonnegative in the quadratic threshold regime.
The polynomial, its remainders, and all coefficient estimates have been constructed. -/
theorem root_weighted_square_nonneg {ξ ζ : ℂ} {η : ℝ} (R : Polynomial ℝ)
    (n : ℝ) (m h k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ)) (hη : η = 1 ∨ η = -1)
    (hR : R.natDegree ≤ 2 * h) (hkm : 2 * (h + k) ≤ m + 1)
    (hn0 : 0 < n) (hn : 2 * ((h + k : ℕ) : ℝ) ^ 2 ≤ n) :
    0 ≤ rootRealAverage m ξ ζ (fun z ↦ betaProduct n k (‖z ^ 2 - 1‖ ^ 2 / 4) *
      ‖(complexify R).eval z‖ ^ 2) := by
  rw [root_betaProduct_average (by omega) hζ hξ hη R n k hk]
  exact actual_remainder_expansion_nonneg R n η m h k hm hk hR hkm hn0 hn

end NoncommutativeAMGM
