/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Contributions.ShortSumDecomposition

/-! # The four contribution classes in arbitrary integer intervals -/

@[expose] public section

namespace NairTenenbaum

/-- Sum over the integer interval `(a,b]`, with zero-extension at roots. -/
noncomputable def PolynomialSystem.integerSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (a b : ℤ) : ℝ :=
  ∑ t ∈ Finset.Ioc a b, extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

/-- Natural-number short sums are integer-interval sums after rounding the endpoints. -/
theorem PolynomialSystem.shortSum_eq_integerSum {k r : ℕ}
    (P : PolynomialSystem k r) (F : ArithmeticMap k) (x y : ℝ) :
    shortSum P.Q F x y = P.integerSum F (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
  unfold shortSum integerSum
  rw [← shortInterval_natCast_image, Finset.sum_image
    (fun a _ b _ h => Int.natCast_inj.mp h)]

theorem PolynomialSystem.HasSmallCrossingPrime.mem_exceptionalSet {k r : ℕ}
    {P : PolynomialSystem k r} {ε x : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x)
    {a b t : ℤ} (ht : t ∈ Finset.Ioc a b) (H : P.HasSmallCrossingPrime ε x t) :
    t ∈ primePowerExceptionalSet P.R (x ^ ((P.total.natDegree : ℝ) * ε / 2))
      ((x ^ ((P.total.natDegree : ℝ) * ε / 2)) ^ 3) a b := by
  obtain ⟨n, q, hn, hq, hqz, hs, hc⟩ := H
  apply P.mem_primePowerExceptionalSet_of_crossing ht hn hq
    (Real.rpow_nonneg (zero_le_one.trans hx) _) hqz
    (one_le_pow₀ (Real.one_le_rpow hx (by positivity)))
  · simpa only [primePower_scale_identity _ _ (zero_le_one.trans hx)] using hs
  · rw [primePower_scale_identity _ _ (zero_le_one.trans hx)]
    have heq : (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2)) ^ 2 =
        x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hx)]
      congr 1
      norm_num
    simpa only [heq] using hc

theorem PolynomialSystem.HasLargeSmoothDivisorTuple.mem_exceptionalSet {k r : ℕ}
    {P : PolynomialSystem k r} {s : Finset ℕ} {ε x : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x)
    {a b t : ℤ} (ht : t ∈ Finset.Ioc a b) (H : P.HasLargeSmoothDivisorTuple s ε x t) :
    t ∈ smoothDivisorExceptionalSet P.radical s
      (Nat.toPNat' ⌊x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)⌋₊)
      (x ^ (3 * (P.total.natDegree : ℝ) * ε / 2)) a b := by
  obtain ⟨m, hdiv, hsmooth, hlarge, hsmall⟩ := H
  have hxN : 1 ≤ x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε) := Real.one_le_rpow hx (by positivity)
  apply P.mem_smoothDivisorExceptionalSet_of_tuple s _ ht m hdiv hsmooth
  · have heq : (x ^ (3 * (P.total.natDegree : ℝ) * ε / 2)) ^ P.total.natDegree =
        x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hx)]
      congr 1
      ring
    simpa only [heq] using hlarge
  · rw [PNat.toPNat'_coe (Nat.floor_pos.mpr hxN)]
    exact (Nat.le_floor_iff (zero_le_one.trans hxN)).mpr hsmall

/-- The decomposition depends on the value scale, not on the position of the
interval. The exceptional-set classes cover the second and third alternatives. -/
theorem PolynomialSystem.integerSum_le_four_contributions {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n)
    {ε x w₀ : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x) (hw₀ : 1 ≤ w₀) (a b : ℤ) :
    let N := Nat.toPNat' ⌊x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)⌋₊
    P.integerSum F a b ≤
      P.smallRoughContribution F N a b (x ^ ((P.total.natDegree : ℝ) * ε / 16)) +
      P.primePowerContribution F (x ^ ((P.total.natDegree : ℝ) * ε / 2)) a b +
      P.smoothDivisorContribution F (Finset.Icc 0 ⌊w₀⌋₊) N
        (x ^ (3 * (P.total.natDegree : ℝ) * ε / 2)) a b +
      P.intermediatePrefixContribution F N (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2))
        w₀ x ((P.total.natDegree : ℝ) * ε / 16) a b := by
  classical
  dsimp only
  have hT : 1 ≤ x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε) := Real.one_le_rpow hx (by positivity)
  unfold integerSum smallRoughContribution primePowerContribution smoothDivisorContribution
    intermediatePrefixContribution primePowerExceptionalSet smoothDivisorExceptionalSet
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  have hnonneg := extendArithmeticMap_nonneg hF (fun j => ((P.Q j).eval t).natAbs)
  by_cases hzero : P.total.eval t = 0
  · simp only [P.value_weight_eq_zero F hzero, ite_self, add_zero, le_refl]
  have H := P.prefix_classes_exhaustive hε hx hw₀ t hzero
  have H' : P.HasSmallRoughPrefix (Nat.toPNat' ⌊x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)⌋₊)
      (x ^ ((P.total.natDegree : ℝ) * ε / 16)) t ∨
    (∃ p ∈ smallPrimes (x ^ ((P.total.natDegree : ℝ) * ε / 2)), ∃ i,
      (p : ℤ) ^ firstPowerAbove p ((x ^ ((P.total.natDegree : ℝ) * ε / 2)) ^ 3) ∣ (P.R i).eval t) ∨
    (∃ d ∈ smoothLargeDivisors (Finset.Icc 0 ⌊w₀⌋₊)
      (Nat.toPNat' ⌊x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)⌋₊)
      (x ^ (3 * (P.total.natDegree : ℝ) * ε / 2)), (d : ℤ) ∣ P.radical.eval t) ∨
    P.HasIntermediatePrefix (Nat.toPNat' ⌊x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)⌋₊)
      (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2)) w₀ x
      ((P.total.natDegree : ℝ) * ε / 16) t := by
    rcases H with H | H | H | H
    · exact Or.inl ((P.hasSmallRoughPrefixReal_iff hT _ t).mp H)
    · exact Or.inr (Or.inl (Finset.mem_filter.mp (H.mem_exceptionalSet hε hx ht)).2)
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mp (H.mem_exceptionalSet hε hx ht)).2))
    · exact Or.inr (Or.inr (Or.inr ((P.hasIntermediatePrefixReal_iff hT _ _ _ _ t).mp H)))
  exact le_sum_four_indicators hnonneg H'

end NairTenenbaum
