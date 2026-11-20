/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.DifferenceFamily

/-!
# Endpoint aliasing under reduction modulo `Xᵐ-η`

If the input degree is at most `m+1`, only its first two coefficients can change
below degree `m`. This is the endpoint protection needed after the parity estimate.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Polynomial
open scoped BigOperators

noncomputable def rootLinearQuotient (p : Polynomial ℝ) (m : ℕ) : Polynomial ℝ :=
  monomial 0 (p.coeff m) + monomial 1 (p.coeff (m + 1))

theorem rootLinearQuotient_coeff (p : Polynomial ℝ) (m i : ℕ) :
    (rootLinearQuotient p m).coeff i =
      (if i = 0 then p.coeff m else 0) + (if i = 1 then p.coeff (m + 1) else 0) := by
  simp [rootLinearQuotient, coeff_monomial, coeff_C, eq_comm]

noncomputable def rootRemainderCandidate (p : Polynomial ℝ) (m : ℕ) (η : ℝ) : Polynomial ℝ :=
  p - rootLinearQuotient p m * (X ^ m - C η)

theorem rootRemainderCandidate_coeff (p : Polynomial ℝ) (m i : ℕ) (η : ℝ) :
    (rootRemainderCandidate p m η).coeff i = p.coeff i -
      (if m ≤ i then (rootLinearQuotient p m).coeff (i - m) else 0) +
        (rootLinearQuotient p m).coeff i * η := by
  simp only [rootRemainderCandidate, mul_sub, coeff_sub, coeff_mul_X_pow', coeff_mul_C]
  ring

theorem rootRemainderCandidate_degree {p : Polynomial ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hp : p.natDegree ≤ m + 1) (η : ℝ) : (rootRemainderCandidate p m η).degree < m := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro i hi
  rw [rootRemainderCandidate_coeff]
  have hi0 : i ≠ 0 := by omega
  have hi1 : i ≠ 1 := by omega
  have hq0 : (rootLinearQuotient p m).coeff i = 0 := by
    simp [rootLinearQuotient_coeff, hi0, hi1]
  rw [hq0, zero_mul, add_zero, ite_eq_left hi]
  by_cases him : i = m
  · subst i
    simp [rootLinearQuotient_coeff]
  by_cases him1 : i = m + 1
  · subst i
    simp [rootLinearQuotient_coeff]
  have hpi : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have his0 : i - m ≠ 0 := by omega
  have his1 : i - m ≠ 1 := by omega
  simp [hpi, rootLinearQuotient_coeff, his0, his1]

/-- Exact polynomial remainder, with its linear quotient exhibited. -/
theorem root_remainder_eq_candidate {p : Polynomial ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hp : p.natDegree ≤ m + 1) (η : ℝ) :
    p %ₘ (X ^ m - C η) = rootRemainderCandidate p m η := by
  apply (div_modByMonic_unique (rootLinearQuotient p m) (rootRemainderCandidate p m η)
    (monic_X_pow_sub_C (n := m) η (by omega)) ?_).2
  constructor
  · unfold rootRemainderCandidate
    ring
  · rw [degree_X_pow_sub_C (by omega)]
    exact rootRemainderCandidate_degree hm hp η

/-- Every coefficient from index `2` through `m-1` survives unchanged. -/
theorem root_remainder_preserves_interior {p : Polynomial ℝ} {m i : ℕ} (hm : 2 ≤ m)
    (hp : p.natDegree ≤ m + 1) (hi : 2 ≤ i) (him : i < m) (η : ℝ) :
    (p %ₘ (X ^ m - C η)).coeff i = p.coeff i := by
  rw [root_remainder_eq_candidate hm hp, rootRemainderCandidate_coeff]
  have hmi : ¬m ≤ i := by omega
  have hi0 : i ≠ 0 := by omega
  have hi1 : i ≠ 1 := by omega
  simp [hmi, rootLinearQuotient_coeff, hi0, hi1]

/-- In either main-theorem parity (`2D=m` or `2D=m+1`), the twice-trimmed
coefficient norm is bounded by the full remainder coefficient norm. -/
theorem twoInterior_le_remainder_norm {p : Polynomial ℝ} {m D : ℕ} (hm : 2 ≤ m)
    (hmD : m ≤ 2 * D) (hDm : 2 * D ≤ m + 1) (hp : p.natDegree ≤ 2 * D) (η : ℝ) :
    twoInteriorCoefficientNormSq D p ≤
      realCoefficientInner (p %ₘ (X ^ m - C η)) (p %ₘ (X ^ m - C η)) := by
  have hrem : (p %ₘ (X ^ m - C η)).degree < m := by
    have hdeg := degree_modByMonic_lt p (monic_X_pow_sub_C (n := m) η (by omega))
    rwa [degree_X_pow_sub_C (by omega)] at hdeg
  rw [realCoefficientNorm_eq_range hrem, twoInteriorCoefficientNormSq]
  have heq : (∑ i ∈ Finset.range (2 * D + 1),
      if 2 ≤ i ∧ i + 2 ≤ 2 * D then p.coeff i ^ 2 else 0) =
      ∑ i ∈ Finset.range m, if 2 ≤ i ∧ i + 2 ≤ 2 * D then p.coeff i ^ 2 else 0 := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i _ hi
    have him : m ≤ i := by simpa using hi
    have hnot : ¬(2 ≤ i ∧ i + 2 ≤ 2 * D) := by omega
    exact ite_eq_right hnot
  rw [heq]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hin : 2 ≤ i ∧ i + 2 ≤ 2 * D
  · rw [ite_eq_left hin, root_remainder_preserves_interior hm (by omega) hin.1
      (Finset.mem_range.mp hi) η]
  · rw [ite_eq_right hin]
    positivity

theorem twoInterior_le_full_norm {p : Polynomial ℝ} {D : ℕ} (hp : p.natDegree ≤ 2 * D) :
    twoInteriorCoefficientNormSq D p ≤ realCoefficientInner p p := by
  have hdeg : p.degree < (2 * D + 1 : ℕ) := by
    apply lt_of_le_of_lt degree_le_natDegree
    exact_mod_cast (Nat.lt_succ_of_le hp)
  rw [realCoefficientNorm_eq_range hdeg, twoInteriorCoefficientNormSq]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · positivity

/-- The endpoint-protected estimate also covers every earlier, lower-degree step. -/
theorem twoInterior_le_remainder_norm_of_le {p : Polynomial ℝ} {m D : ℕ} (hm : 2 ≤ m)
    (hDm : 2 * D ≤ m + 1) (hp : p.natDegree ≤ 2 * D) (η : ℝ) :
    twoInteriorCoefficientNormSq D p ≤
      realCoefficientInner (p %ₘ (X ^ m - C η)) (p %ₘ (X ^ m - C η)) := by
  by_cases hmD : m ≤ 2 * D
  · exact twoInterior_le_remainder_norm hm hmD hDm hp η
  · have hdeg : p.degree < m := by
      apply lt_of_le_of_lt degree_le_natDegree
      exact_mod_cast (show p.natDegree < m by omega)
    have hmod : p %ₘ (X ^ m - C η) = p := by
      apply (modByMonic_eq_self_iff (monic_X_pow_sub_C (n := m) η (by omega))).mpr
      rwa [degree_X_pow_sub_C (by omega)]
    rw [hmod]
    exact twoInterior_le_full_norm hp

end NoncommutativeAMGM
