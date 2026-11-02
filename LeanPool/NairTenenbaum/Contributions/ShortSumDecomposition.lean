/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Contributions.FirstContributionReal
public import LeanPool.NairTenenbaum.Contributions.IntermediateContributionReal
public import LeanPool.NairTenenbaum.Contributions.SecondContribution
public import LeanPool.NairTenenbaum.Contributions.ThirdContribution

/-! # Exhaustive decomposition of the original short sum

The large-prefix rough-remainder majorant includes the small-total-mass case.
For larger total mass, the first crossing prime gives either that majorant,
the small-prime exceptional contribution, or a large prefix. The latter is
covered by bounded smoothness or the intermediate logarithmic bands.
-/

@[expose] public section

namespace NairTenenbaum

/-- A cutoff past the total mass includes every whole prime power. -/
theorem primeSelect_range_eq_self {r : ℕ} (n : Tuple r) {q : ℕ} (hq : mass n < q) :
    primeSelect n (Finset.range q) = n := by
  rw [primeSelect, Finset.filter_eq_self.mpr, prod_primePart]
  intro p hp
  exact Finset.mem_range.mpr ((Nat.le_of_dvd (mass_pos n) (Nat.dvd_of_mem_primeFactors
      hp)).trans_lt hq)

/-- When the full value is below the divisor bound, an arbitrarily large
cutoff supplies a rough prefix with empty remainder. -/
theorem PolynomialSystem.hasSmallRoughPrefixReal_of_total_mass {k r : ℕ} (P : PolynomialSystem k r)
    {t : ℤ} {n : Tuple r} (hn : ∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs)
    {T : ℝ} (hT : (weightedMass P.exponent n : ℝ) ≤ T) (z : ℝ) :
    P.HasSmallRoughPrefixReal T z t := by
  let q := max (mass n) ⌊z⌋₊ + 1
  have hq : mass n < q := Nat.lt_succ_of_le (le_max_left _ _)
  refine ⟨n, q, hn, ?_, ?_⟩
  · simpa only [primeSelect_range_eq_self n hq] using hT
  · apply Nat.lt_of_floor_lt
    exact Nat.lt_succ_of_le (le_max_right _ _)

/-- Vanishing total polynomial values have zero arithmetic weight under the
explicit zero-extension convention. -/
theorem PolynomialSystem.value_weight_eq_zero {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) {t : ℤ} (ht : P.total.eval t = 0) :
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs) = 0 := by
  rw [PolynomialSystem.total, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at ht
  obtain ⟨j, _, hj⟩ := ht
  unfold extendArithmeticMap
  apply dite_eq_right
  intro h
  have H := h j
  simp only [hj, Int.natAbs_zero, lt_self_iff_false] at H

/-- Every nonzero polynomial value belongs to at least one of the four proved
majorants. The classes may overlap; disjointness is unnecessary for nonnegative
arithmetic weights. -/
theorem PolynomialSystem.prefix_classes_exhaustive {k r : ℕ} (P : PolynomialSystem k r)
    {ε x w₀ : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x) (hw₀ : 1 ≤ w₀) (t : ℤ)
    (ht : P.total.eval t ≠ 0) :
    P.HasSmallRoughPrefixReal (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε))
      (x ^ ((P.total.natDegree : ℝ) * ε / 16)) t ∨
    P.HasSmallCrossingPrime ε x t ∨
    P.HasLargeSmoothDivisorTuple (Finset.Icc 0 ⌊w₀⌋₊) ε x t ∨
    P.HasIntermediatePrefixReal (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε))
      (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2)) w₀ x
      ((P.total.natDegree : ℝ) * ε / 16) t := by
  classical
  obtain ⟨n, hn⟩ := P.exists_valueTuple ht
  have hT : 1 ≤ x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε) := Real.one_le_rpow hx (by positivity)
  obtain htotal | ⟨q, hq, hsmall, hcross⟩ := small_mass_or_prime_threshold P.exponent n hT
  · exact Or.inl (P.hasSmallRoughPrefixReal_of_total_mass hn htotal _)
  by_cases hrough : x ^ ((P.total.natDegree : ℝ) * ε / 16) < (q : ℝ)
  · exact Or.inl ⟨n, q, hn, hsmall, hrough⟩
  have hqcut : (q : ℝ) ≤ x ^ ((P.total.natDegree : ℝ) * ε / 16) := le_of_not_gt hrough
  by_cases hmass : (weightedMass P.exponent (primeSelect n (Finset.range q)) : ℝ) ≤
      x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2)
  · refine Or.inr (Or.inl ⟨n, q, hn, hq, ?_, hmass, hcross⟩)
    exact hqcut.trans (Real.rpow_le_rpow_of_exponent_le hx (by
      have H : 0 ≤ (P.total.natDegree : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε
      linarith))
  have hmass' := lt_of_not_ge hmass
  by_cases hsmooth : ∀ i p, p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors → (p : ℝ) ≤ w₀
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    refine ⟨primeSelect n (Finset.range q), ?_, ?_, hmass', hsmall⟩
    · intro i
      exact Int.natCast_dvd.mpr (by
        simpa only [hn i] using primeSelect_coordinate_dvd n (Finset.range q) i)
    · apply (weightedMass_mem_factoredNumbers_iff P.exponent P.exponent_pos _ _).mpr
      intro i
      apply Nat.mem_factoredNumbers_of_primeFactors_subset (primeSelect n (Finset.range q)
          i).ne_zero
      intro p hp
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Nat.le_floor_iff (zero_le_one.trans hw₀)).mpr
          (hsmooth i p hp)⟩
  · apply Or.inr ∘ Or.inr ∘ Or.inr
    refine ⟨n, q, hn, hsmall, hmass', ?_, ?_⟩
    · intro i p hp
      have H : (p : ℝ) < q := by exact_mod_cast primeSelect_range_prime_lt n q i hp
      exact H.le.trans hqcut
    · push Not at hsmooth
      exact hsmooth

end NairTenenbaum
