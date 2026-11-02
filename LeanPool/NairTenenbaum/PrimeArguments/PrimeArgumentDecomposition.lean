/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Contributions.IntegerIntervalDecomposition
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentCover
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentFirstContribution

/-! # The four contribution classes restricted to prime arguments -/

@[expose] public section

namespace NairTenenbaum

private theorem le_four_indicator_sum {p q r s : Prop}
    [Decidable p] [Decidable q] [Decidable r] [Decidable s]
    {v : ℝ} (hv : 0 ≤ v) (h : p ∨ q ∨ r ∨ s) :
    v ≤ (if p then v else 0) + (if q then v else 0) +
      (if r then v else 0) + (if s then v else 0) := by
  split_ifs <;> simp_all; linarith

/-- Prime arguments above the analytic scale in an integer interval. Absolute
values allow the decomposition to be stated independently of interval position. -/
noncomputable def PolynomialSystem.primeIntegerSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (x : ℝ) (a b : ℤ) : ℝ := by
  classical
  exact ∑ t ∈ (Finset.Ioc a b).filter (fun t => t.natAbs.Prime ∧ x < t.natAbs),
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

theorem PolynomialSystem.primeIntegerSum_le_four_contributions {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n)
    {ε x w₀ : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x) (hw₀ : 1 ≤ w₀)
    (hcut : x ^ ((P.total.natDegree : ℝ) * ε / 16) ≤ x) (a b : ℤ) :
    let N := Nat.toPNat' ⌊x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)⌋₊
    P.primeIntegerSum F x a b ≤
      P.primeSmallRoughContribution F N a b (x ^ ((P.total.natDegree : ℝ) * ε / 16)) +
      P.primePowerContribution F (x ^ ((P.total.natDegree : ℝ) * ε / 2)) a b +
      P.smoothDivisorContribution F (Finset.Icc 0 ⌊w₀⌋₊) N
        (x ^ (3 * (P.total.natDegree : ℝ) * ε / 2)) a b +
      P.primeIntermediatePrefixContribution F N (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2))
        w₀ x ((P.total.natDegree : ℝ) * ε / 16) a b := by
  classical
  dsimp only
  have hT : 1 ≤ x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε) := Real.one_le_rpow hx (by positivity)
  unfold primeIntegerSum primeSmallRoughContribution primePowerContribution
      smoothDivisorContribution
    primeIntermediatePrefixContribution primePowerExceptionalSet smoothDivisorExceptionalSet
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
  have hlarge : x < t.natAbs → x ^ ((P.total.natDegree : ℝ) * ε / 16) < t.natAbs :=
    fun ht => hcut.trans_lt ht
  by_cases hprime : t.natAbs.Prime ∧ x < t.natAbs
  · simp only [hprime.1, hprime.2, hlarge hprime.2, and_true, ite_true]
    exact le_four_indicator_sum hnonneg H'
  · rw [ite_eq_right hprime]
    exact add_nonneg (add_nonneg (add_nonneg (ite_nonneg hnonneg le_rfl)
      (ite_nonneg hnonneg le_rfl)) (ite_nonneg hnonneg le_rfl)) (ite_nonneg hnonneg le_rfl)

end NairTenenbaum
