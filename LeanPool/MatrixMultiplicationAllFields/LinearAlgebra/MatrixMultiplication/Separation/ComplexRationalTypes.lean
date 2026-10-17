/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteControl
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.Rat.Floor

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation

open scoped BigOperators

structure RationalLaw (A : Type*) [Fintype A] where
  mass : A → ℚ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace RationalLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def toFiniteLaw (p : RationalLaw A) : FiniteLaw A where
  mass a := p.mass a
  nonneg a := by exact_mod_cast p.nonneg a
  total := by exact_mod_cast p.total

@[simp] theorem toFiniteLaw_mass (p : RationalLaw A) (a : A) :
    p.toFiniteLaw.mass a = (p.mass a : ℝ) := rfl

theorem exists_exact_counts (p : RationalLaw A) :
    ∃ D : ℕ, 0 < D ∧ ∃ counts : A → ℕ,
      (∑ a, counts a) = D ∧
      ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a := by
  classical
  obtain ⟨D, hD, hcopies⟩ := FiniteControl.exists_exact_rational_tiling
    p.mass p.nonneg (fun _ => 1) (fun _ => Nat.zero_lt_one)
  choose counts hcounts using hcopies
  have hc : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a := by
    intro a
    simpa using (hcounts a).symm
  refine ⟨D, hD, counts, ?_, hc⟩
  have hsum : (∑ a, (counts a : ℚ)) = (D : ℚ) := by
    simp_rw [hc]
    rw [← Finset.mul_sum, p.total, mul_one]
  exact_mod_cast hsum

theorem scale_exact_counts (p : RationalLaw A) (D : ℕ) (counts : A → ℕ)
    (hsum : (∑ a, counts a) = D)
    (hcounts : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a) (k : ℕ) :
    (∑ a, k * counts a) = k * D ∧
      ∀ a, ((k * counts a : ℕ) : ℚ) = ((k * D : ℕ) : ℚ) * p.mass a := by
  constructor
  · rw [← Finset.mul_sum, hsum]
  · intro a
    simp only [Nat.cast_mul]
    rw [hcounts a]
    ring

theorem exact_counts_zero_iff (p : RationalLaw A) {D : ℕ} (hD : 0 < D)
    {counts : A → ℕ}
    (hcounts : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a) (a : A) :
    counts a = 0 ↔ p.mass a = 0 := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  constructor
  · intro hzero
    have hz : (D : ℚ) * p.mass a = 0 := by
      rw [← hcounts a, hzero, Nat.cast_zero]
    exact (mul_eq_zero.mp hz).resolve_left hDq
  · intro hzero
    have hz : (counts a : ℚ) = 0 := by rw [hcounts a, hzero, mul_zero]
    exact_mod_cast hz

theorem exact_counts_real_mass (p : RationalLaw A) {D : ℕ} (hD : 0 < D)
    {counts : A → ℕ}
    (hcounts : ∀ a, (counts a : ℚ) = (D : ℚ) * p.mass a) (a : A) :
    (counts a : ℝ) / (D : ℝ) = p.toFiniteLaw.mass a := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  apply (div_eq_iff hDr).2
  have hc : (counts a : ℝ) = (D : ℝ) * (p.mass a : ℝ) := by
    exact_mod_cast hcounts a
  simpa only [toFiniteLaw_mass, mul_comm] using hc

theorem exists_type_representation (p : RationalLaw A) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      ∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a := by
  obtain ⟨D, hD, counts, hsum, hcounts⟩ := p.exists_exact_counts
  refine ⟨counts, by simpa only [hsum] using hD, ?_⟩
  intro a
  rw [hsum]
  exact p.exact_counts_real_mass hD hcounts a

end RationalLaw

private theorem exists_nonnegative_rat_below (x : ℝ) (hx : 0 ≤ x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℚ, 0 ≤ r ∧ (r : ℝ) ≤ x ∧ (r = 0 ↔ x = 0) ∧
      |(r : ℝ) - x| < δ := by
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0, le_rfl, by simp, by simp, by simpa using hδ⟩
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hlo : max 0 (x - δ) < x := max_lt hxpos (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn hlo
  have hrpos : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hrlo
  have hrposq : (0 : ℚ) < r := by exact_mod_cast hrpos
  refine ⟨r, hrposq.le, hrhi.le,
    iff_of_false (ne_of_gt hrposq) hx0, ?_⟩
  have hrlo' : x - δ < r := lt_of_le_of_lt (le_max_right _ _) hrlo
  rw [abs_of_nonpos (sub_nonpos.mpr hrhi.le)]
  linarith

namespace FiniteLaw

variable {A : Type*} [Fintype A]

theorem exists_rational_approximation (p : FiniteLaw A) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : RationalLaw A,
      (∀ a, q.mass a = 0 ↔ p.mass a = 0) ∧
      ∀ a, |(q.mass a : ℝ) - p.mass a| < ε := by
  classical
  have hpivot : ∃ a, 0 < p.mass a := by
    by_contra h
    have hnonpos : ∀ a, p.mass a ≤ 0 :=
      fun a => le_of_not_gt (fun ha => h ⟨a, ha⟩)
    have hsum : (∑ a, p.mass a) ≤ 0 :=
      Finset.sum_nonpos (fun a _ => hnonpos a)
    rw [p.total] at hsum
    norm_num at hsum
  obtain ⟨a₀, ha₀⟩ := hpivot
  let δ : ℝ := ε / ((Fintype.card A : ℝ) + 1)
  have hcard : 0 ≤ (Fintype.card A : ℝ) := Nat.cast_nonneg _
  have hden : 0 < (Fintype.card A : ℝ) + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ * ((Fintype.card A : ℝ) + 1) = ε :=
    div_mul_cancel₀ ε (ne_of_gt hden)
  have hcardδ : 0 ≤ (Fintype.card A : ℝ) * δ := mul_nonneg hcard hδ.le
  have hδle : δ ≤ ε := by nlinarith
  choose r hrnonneg hrle hrzero hrclose using
    fun a => exists_nonnegative_rat_below (p.mass a) (p.nonneg a) δ hδ
  have hsum : (∑ a, (r a : ℝ)) ≤ 1 := by
    calc
      (∑ a, (r a : ℝ)) ≤ ∑ a, p.mass a :=
        Finset.sum_le_sum (fun a _ => hrle a)
      _ = 1 := p.total
  have hrest : 0 ≤ 1 - ∑ a, (r a : ℝ) := sub_nonneg.mpr hsum
  have hrestq : (0 : ℚ) ≤ 1 - ∑ a, r a := by exact_mod_cast hrest
  have hrest_le : 1 - ∑ a, (r a : ℝ) ≤ (Fintype.card A : ℝ) * δ := by
    calc
      1 - ∑ a, (r a : ℝ) = ∑ a, (p.mass a - (r a : ℝ)) := by
        rw [Finset.sum_sub_distrib, p.total]
      _ ≤ ∑ _a : A, δ := by
        apply Finset.sum_le_sum
        intro a _
        have h := (abs_lt.mp (hrclose a)).1
        linarith
      _ = (Fintype.card A : ℝ) * δ := by simp
  let q : RationalLaw A :=
    { mass := fun a => r a + if a = a₀ then 1 - ∑ b, r b else 0
      nonneg := by
        intro a
        apply add_nonneg (hrnonneg a)
        split_ifs
        · exact hrestq
        · exact le_rfl
      total := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring }
  refine ⟨q, ?_, ?_⟩
  · intro a
    by_cases ha : a = a₀
    · subst a
      have hrpos : 0 < r a₀ :=
        lt_of_le_of_ne (hrnonneg a₀) (Ne.symm (fun hz => (ne_of_gt ha₀) ((hrzero a₀).mp hz)))
      have hqpos : 0 < q.mass a₀ := by
        dsimp [q]
        simp only [ite_true]
        linarith
      exact iff_of_false (ne_of_gt hqpos) (ne_of_gt ha₀)
    · simpa only [q, ite_eq_right ha, add_zero] using hrzero a
  · intro a
    by_cases ha : a = a₀
    · have hqcast : (q.mass a : ℝ) =
          (r a : ℝ) + (1 - ∑ b, (r b : ℝ)) := by
        simp [q, ha]
      rw [hqcast]
      have habs : |(r a : ℝ) + (1 - ∑ b, (r b : ℝ)) - p.mass a| ≤
          |(r a : ℝ) - p.mass a| + (1 - ∑ b, (r b : ℝ)) := by
        calc
          _ = |((r a : ℝ) - p.mass a) + (1 - ∑ b, (r b : ℝ))| := by
            congr 1
            ring
          _ ≤ |(r a : ℝ) - p.mass a| + |1 - ∑ b, (r b : ℝ)| := abs_add_le _ _
          _ = _ := by rw [abs_of_nonneg hrest]
      have hclose := hrclose a
      nlinarith
    · simpa only [q, ite_eq_right ha, add_zero] using
        lt_of_lt_of_le (hrclose a) hδle

theorem exists_exact_type_approximation (p : FiniteLaw A) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ ∃ counts : A → ℕ,
      (∑ a, counts a) = D ∧
      (∀ a, counts a = 0 ↔ p.mass a = 0) ∧
      ∀ a, |(counts a : ℝ) / (D : ℝ) - p.mass a| < ε := by
  obtain ⟨q, hsupport, hclose⟩ := p.exists_rational_approximation ε hε
  obtain ⟨D, hD, counts, hsum, hcounts⟩ := q.exists_exact_counts
  refine ⟨D, hD, counts, hsum, ?_, ?_⟩
  · intro a
    exact (q.exact_counts_zero_iff hD hcounts a).trans (hsupport a)
  · intro a
    rw [q.exact_counts_real_mass hD hcounts a, RationalLaw.toFiniteLaw_mass]
    exact hclose a

end FiniteLaw

end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
