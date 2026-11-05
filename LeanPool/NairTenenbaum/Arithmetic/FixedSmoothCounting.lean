/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.FractionalAuxiliary
public import LeanPool.NairTenenbaum.Polynomials.PolynomialPreimages

/-! # Subpolynomial counts on a fixed finite prime support -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- A counting constant for integers supported on a fixed finite set of primes. -/
noncomputable def fixedSmoothCountBound (s : Finset ℕ) (η : ℝ) : ℝ :=
  (1 / (1 - (2 : ℝ) ^ (-η))) ^ (s.filter Nat.Prime).card

theorem fixedSmoothCountBound_pos (s : Finset ℕ) {η : ℝ} (hη : 0 < η) :
    0 < fixedSmoothCountBound s η := by
  apply pow_pos
  apply one_div_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hη))

theorem smooth_reciprocal_rpow_sum_le (s : Finset ℕ) {η : ℝ} (hη : 0 < η)
    (S : Finset ℕ+) (hS : ∀ n ∈ S, (n : ℕ) ∈ Nat.factoredNumbers s) :
    (∑ n ∈ S, (n : ℝ) ^ (-η)) ≤ fixedSmoothCountBound s η := by
  have H := fractionalAuxiliary_sum_le (A := 1) (B := 1) (ε := 1) (α := η)
    (σ := -η) (by norm_num) (by norm_num) (by norm_num) (neg_neg_of_pos hη) 0 (by simp) s S hS
  simpa [fractionalAuxiliary, auxiliary, auxiliaryLocal, Real.rpow_neg,
    one_div, fixedSmoothCountBound] using H

theorem smooth_positive_card_le_rpow (s : Finset ℕ) {η X : ℝ} (hη : 0 < η) (hX : 0 ≤ X)
    (S : Finset ℕ+) (hS : ∀ n ∈ S, (n : ℕ) ∈ Nat.factoredNumbers s)
    (hSX : ∀ n ∈ S, (n : ℝ) ≤ X) :
    (S.card : ℝ) ≤ fixedSmoothCountBound s η * X ^ η := by
  have H (n : ℕ+) (hn : n ∈ S) : (1 : ℝ) ≤ X ^ η * (n : ℝ) ^ (-η) := by
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast n.pos
    have H := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hn₀.le (hSX n hn) hη.le)
      (Real.rpow_nonneg hn₀.le (-η))
    rw [← Real.rpow_add hn₀, add_neg_cancel, Real.rpow_zero] at H
    exact H
  calc
    _ = ∑ _n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, X ^ η * (n : ℝ) ^ (-η) := Finset.sum_le_sum H
    _ = X ^ η * ∑ n ∈ S, (n : ℝ) ^ (-η) := (Finset.mul_sum _ _ _).symm
    _ ≤ X ^ η * fixedSmoothCountBound s η :=
      mul_le_mul_of_nonneg_left (smooth_reciprocal_rpow_sum_le s hη S hS) (Real.rpow_nonneg hX _)
    _ = _ := mul_comm _ _

theorem smooth_nat_card_le_rpow (s : Finset ℕ) {η X : ℝ} (hη : 0 < η) (hX : 0 ≤ X)
    (T : Finset ℕ) (hT : ∀ n ∈ T, n ∈ Nat.factoredNumbers s) (hTX : ∀ n ∈ T, (n : ℝ) ≤ X) :
    (T.card : ℝ) ≤ fixedSmoothCountBound s η * X ^ η := by
  classical
  let f : {n : ℕ // n ∈ T} → ℕ+ := fun n => ⟨n.1, Nat.pos_of_ne_zero
      (Nat.ne_zero_of_mem_factoredNumbers (hT n.1 n.2))⟩
  have hf : Function.Injective f := by
    intro n m h
    exact Subtype.ext (congrArg (fun n : ℕ+ => (n : ℕ)) h)
  have H := smooth_positive_card_le_rpow s hη hX (T.attach.image f)
    (by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
      exact hT a.1 a.2)
    (by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
      exact hTX a.1 a.2)
  simpa only [card_image_of_injective _ hf, card_attach] using H

/-- Smooth polynomial values on a fixed prime support are sparse uniformly
in the coefficients and the location of the finite set. -/
theorem polynomial_fixed_smooth_card_le {Q : ℤ[X]} (hQ : 0 < Q.natDegree)
    (S : Finset ℤ) (s : Finset ℕ) {η X : ℝ} (hη : 0 < η) (hX : 0 ≤ X) :
    ((S.filter (fun n => (Q.eval n).natAbs ∈ Nat.factoredNumbers s ∧
      ((Q.eval n).natAbs : ℝ) ≤ X)).card : ℝ) ≤
      (2 * Q.natDegree * fixedSmoothCountBound s η) * X ^ η := by
  classical
  let U := S.filter (fun n => (Q.eval n).natAbs ∈ Nat.factoredNumbers s ∧
    ((Q.eval n).natAbs : ℝ) ≤ X)
  have Hcard : (U.card : ℝ) ≤ (2 * Q.natDegree : ℝ) * (U.image (fun n => (Q.eval n).natAbs)).card
      := by
    exact_mod_cast polynomial_natAbs_image_card_bound hQ U
  have Hsmooth := smooth_nat_card_le_rpow s hη hX (U.image (fun n => (Q.eval n).natAbs))
    (by
      intro a ha
      obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
      exact (mem_filter.mp hn).2.1)
    (by
      intro a ha
      obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
      exact (mem_filter.mp hn).2.2)
  exact (Hcard.trans (mul_le_mul_of_nonneg_left Hsmooth (by positivity))).trans_eq (by ring)

end NairTenenbaum
