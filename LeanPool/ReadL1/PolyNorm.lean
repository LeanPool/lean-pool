/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

/-!
# Śliwa's coefficient norm and truncation

For a polynomial `f = ∑ cᵢ xⁱ`, Śliwa (p. 636) uses the coefficient norm `|f| = ∑ |cᵢ|`
(`ReadL1.pnorm`), which is submultiplicative (`ReadL1.pnorm_mul_le`), and the truncation `Pₙ`
keeping the powers up to `xⁿ` (`ReadL1.ptrunc`), with `x (Pₙ v) = Pₙ₊₁ (x v)`
(`ReadL1.X_mul_ptrunc`).
-/

@[expose] public section

namespace ReadL1

open Polynomial

/- ### The coefficient norm `|f|` -/

/-- Śliwa's coefficient norm `|∑ cᵢ xⁱ| = ∑ |cᵢ|`. -/
noncomputable def pnorm (p : ℂ[X]) : ℝ := p.sum fun _ c ↦ ‖c‖

lemma pnorm_eq_sum_of_subset (p : ℂ[X]) {s : Finset ℕ} (hs : p.support ⊆ s) :
    pnorm p = ∑ n ∈ s, ‖p.coeff n‖ := by
  rw [pnorm, Polynomial.sum_def]
  exact Finset.sum_subset hs fun n _ hn ↦ by simp [Polynomial.notMem_support_iff.1 hn]

lemma pnorm_nonneg (p : ℂ[X]) : 0 ≤ pnorm p := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

@[simp] lemma pnorm_zero : pnorm 0 = 0 := by simp [pnorm]

lemma pnorm_monomial (n : ℕ) (c : ℂ) : pnorm (monomial n c) = ‖c‖ := by
  simp [pnorm, Polynomial.sum_monomial_index]

lemma pnorm_add_le (p q : ℂ[X]) : pnorm (p + q) ≤ pnorm p + pnorm q := by
  classical
  rw [pnorm_eq_sum_of_subset _ support_add, pnorm_eq_sum_of_subset p Finset.subset_union_left,
    pnorm_eq_sum_of_subset q Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun n _ ↦ by simpa using norm_add_le (p.coeff n) (q.coeff n)

lemma pnorm_sum_le {ι : Type*} (s : Finset ι) (g : ι → ℂ[X]) :
    pnorm (∑ k ∈ s, g k) ≤ ∑ k ∈ s, pnorm (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    exact (pnorm_add_le _ _).trans (by linarith)

/-- **`|f g| ≤ |f| |g|`.** -/
lemma pnorm_mul_le (p q : ℂ[X]) : pnorm (p * q) ≤ pnorm p * pnorm q := by
  rw [Polynomial.mul_eq_sum_sum]
  refine (pnorm_sum_le _ _).trans ?_
  rw [pnorm, Polynomial.sum_def, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ (pnorm_sum_le _ _).trans ?_
  rw [pnorm, Polynomial.sum_def, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦ by rw [pnorm_monomial, norm_mul]

/- ### Truncation -/

/-- `Pₙ`: keep the powers `x⁰, …, xⁿ`. -/
noncomputable def ptrunc (n : ℕ) (p : ℂ[X]) : ℂ[X] :=
  ∑ i ∈ Finset.range (n + 1), monomial i (p.coeff i)

lemma coeff_ptrunc (n : ℕ) (p : ℂ[X]) (k : ℕ) :
    (ptrunc n p).coeff k = if k ≤ n then p.coeff k else 0 := by
  classical
  rw [ptrunc, finsetSum_coeff]
  simp [coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq']

/-- `x (Pₙ v) = Pₙ₊₁ (x v)`. -/
lemma X_mul_ptrunc (n : ℕ) (v : ℂ[X]) : X * ptrunc n v = ptrunc (n + 1) (X * v) := by
  ext k
  rcases k with _ | k
  · simp [coeff_ptrunc]
  · rw [coeff_X_mul, coeff_ptrunc, coeff_ptrunc, coeff_X_mul]
    by_cases hk : k ≤ n
    · rw [ite_eq_left hk, ite_eq_left (by omega)]
    · rw [ite_eq_right hk, ite_eq_right (by omega)]

lemma pnorm_ptrunc_le (n : ℕ) (p : ℂ[X]) : pnorm (ptrunc n p) ≤ pnorm p := by
  classical
  have hs : (ptrunc n p).support ⊆ p.support := fun k hk ↦ by
    rw [Polynomial.mem_support_iff, coeff_ptrunc] at hk
    rw [Polynomial.mem_support_iff]
    split_ifs at hk with h
    · exact hk
    · exact absurd rfl hk
  rw [pnorm_eq_sum_of_subset _ hs, pnorm_eq_sum_of_subset p le_rfl]
  exact Finset.sum_le_sum fun k _ ↦ by
    rw [coeff_ptrunc]; split_ifs <;> simp

/- ### More on truncation and the coefficient norm -/

lemma ptrunc_add (n : ℕ) (p q : ℂ[X]) : ptrunc n (p + q) = ptrunc n p + ptrunc n q := by
  ext k; simp only [coeff_ptrunc, coeff_add]; split_ifs <;> simp

lemma ptrunc_sub (n : ℕ) (p q : ℂ[X]) : ptrunc n (p - q) = ptrunc n p - ptrunc n q := by
  ext k; simp only [coeff_ptrunc, coeff_sub]; split_ifs <;> simp

lemma ptrunc_C_mul (n : ℕ) (c : ℂ) (p : ℂ[X]) : ptrunc n (C c * p) = C c * ptrunc n p := by
  ext k; simp only [coeff_ptrunc, coeff_C_mul]; split_ifs <;> simp

/-- Truncating above the degree changes nothing. -/
lemma ptrunc_of_natDegree_le {n : ℕ} {p : ℂ[X]} (h : p.natDegree ≤ n) : ptrunc n p = p := by
  ext k; rw [coeff_ptrunc]
  split_ifs with hk
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

lemma pnorm_sub_le (p q : ℂ[X]) : pnorm (p - q) ≤ pnorm p + pnorm q := by
  have h := pnorm_add_le p (-q)
  have hneg : pnorm (-q) = pnorm q := by
    rw [pnorm_eq_sum_of_subset (-q) (s := q.support) (by rw [support_neg]),
      pnorm_eq_sum_of_subset q le_rfl]
    simp
  rwa [← sub_eq_add_neg, hneg] at h

lemma pnorm_X_pow (m : ℕ) : pnorm (X ^ m : ℂ[X]) = 1 := by
  rw [← monomial_one_right_eq_X_pow, pnorm_monomial, norm_one]

lemma pnorm_C_mul (c : ℂ) (p : ℂ[X]) : pnorm (C c * p) = ‖c‖ * pnorm p := by
  have hs : (C c * p).support ⊆ p.support := fun k hk ↦ by
    rw [Polynomial.mem_support_iff, coeff_C_mul] at hk
    exact Polynomial.mem_support_iff.2 (right_ne_zero_of_mul hk)
  rw [pnorm_eq_sum_of_subset _ hs, pnorm_eq_sum_of_subset p le_rfl, Finset.mul_sum]
  simp [coeff_C_mul]

/-- `|p| = |p₀| + |divX p|`: the constant term and the rest. -/
lemma pnorm_eq_add_divX (p : ℂ[X]) : pnorm p = ‖p.coeff 0‖ + pnorm (divX p) := by
  have h1 : p.support ⊆ Finset.range (p.natDegree + 1) := supp_subset_range_natDegree_succ
  have h2 : (divX p).support ⊆ Finset.range p.natDegree := fun k hk ↦ by
    rw [Polynomial.mem_support_iff, coeff_divX] at hk
    have := le_natDegree_of_ne_zero hk
    exact Finset.mem_range.2 (by omega)
  rw [pnorm_eq_sum_of_subset p h1, pnorm_eq_sum_of_subset _ h2, Finset.sum_range_succ', add_comm]
  simp [coeff_divX]

lemma pnorm_divX_le (p : ℂ[X]) : pnorm (divX p) ≤ pnorm p := by
  rw [pnorm_eq_add_divX p]; linarith [norm_nonneg (p.coeff 0)]

/-- `|x f| = |f|`. -/
lemma pnorm_X_mul (p : ℂ[X]) : pnorm (X * p) = pnorm p := by
  have h : divX (X * p) = p := by ext k; simp [coeff_divX, coeff_X_mul]
  rw [pnorm_eq_add_divX (X * p), h]
  simp

lemma divX_ptrunc (m : ℕ) (p : ℂ[X]) : divX (ptrunc (m + 1) p) = ptrunc m (divX p) := by
  ext k
  rw [coeff_divX, coeff_ptrunc, coeff_ptrunc, coeff_divX]
  split_ifs <;> first | rfl | omega

/-- `|Pₘ₊₁ y| = |y₀| + |Pₘ (divX y)|`. -/
lemma pnorm_ptrunc_succ (m : ℕ) (p : ℂ[X]) :
    pnorm (ptrunc (m + 1) p) = ‖p.coeff 0‖ + pnorm (ptrunc m (divX p)) := by
  rw [pnorm_eq_add_divX, divX_ptrunc, coeff_ptrunc, ite_eq_left (Nat.zero_le _)]

lemma pnorm_ptrunc_zero (p : ℂ[X]) : pnorm (ptrunc 0 p) = ‖p.coeff 0‖ := by
  rw [ptrunc, Finset.sum_range_one, pnorm_monomial]

end ReadL1
