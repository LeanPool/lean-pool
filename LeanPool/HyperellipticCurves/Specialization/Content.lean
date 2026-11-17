/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

import LeanPool.HyperellipticCurves.ForMathlib.GroupWithZero

/-!
# The valuation-content of a polynomial

For a valuation `v : K → ℤᵐ⁰` on a field `K`, the `v`-content of a polynomial `p : K[X]` is the
supremum of `v` over its coefficients. A polynomial is `v`-integral iff its content is `≤ 1` and
primitive iff its content is `= 1`. The content is multiplicative under scaling by a constant
(`contentVal_C_mul`), which gives that every nonzero polynomial has a `Kˣ`-multiple of unit
content (`exists_primitive_smul`) — the arithmetic heart of content normalization.

This is the `𝓋`-adic realization of Gauss content used for `lem:content`.
-/

@[expose] public section

open Polynomial

open scoped WithZero

namespace ChabautyColeman

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)

/-- The `v`-content of a polynomial over `K`: the sup of `v` over its coefficients. Junk `0`
at `p = 0`. `p` is `v`-integral iff `contentVal v p ≤ 1`, and primitive iff `= 1`. -/
noncomputable def contentVal (p : K[X]) : ℤᵐ⁰ :=
  p.support.sup fun i ↦ v (p.coeff i)

@[simp] theorem contentVal_zero : contentVal v 0 = 0 := by simp [contentVal]

theorem coeff_le_contentVal (p : K[X]) (i : ℕ) : v (p.coeff i) ≤ contentVal v p := by
  rw [contentVal]
  rcases eq_or_ne (p.coeff i) 0 with h | h
  · rw [h, Valuation.map_zero]; exact zero_le
  · exact Finset.le_sup (f := fun i ↦ v (p.coeff i)) (mem_support_iff.mpr h)

theorem contentVal_eq_zero_iff {p : K[X]} : contentVal v p = 0 ↔ p = 0 := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simp⟩
  ext i
  have := coeff_le_contentVal v p i
  rw [h, le_zero_iff, Valuation.zero_iff] at this
  simp [this]

/-- The content is attained at some coefficient (for `p ≠ 0`). -/
theorem exists_coeff_contentVal {p : K[X]} (hp : p ≠ 0) :
    ∃ i, p.coeff i ≠ 0 ∧ v (p.coeff i) = contentVal v p := by
  have hne : p.support.Nonempty := by rwa [Polynomial.support_nonempty]
  obtain ⟨i, hi, hval⟩ := Finset.exists_mem_eq_sup' hne (fun i ↦ v (p.coeff i))
  rw [mem_support_iff] at hi
  exact ⟨i, hi, by rw [contentVal, ← Finset.sup'_eq_sup hne, hval]⟩

theorem contentVal_C_mul (c : K) (p : K[X]) : contentVal v (C c * p) = v c * contentVal v p := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hsupp : (C c * p).support = p.support := by ext i; simp [mem_support_iff, coeff_C_mul, hc]
  rw [contentVal, hsupp, contentVal, Finset.mul₀_sup]
  exact Finset.sup_congr rfl fun i _ ↦ by rw [coeff_C_mul, map_mul]

/-- **Single-polynomial content normalization.** Any nonzero `p` has a `Kˣ`-multiple `C c * p`
of unit content (primitive). -/
theorem exists_primitive_smul {p : K[X]} (hp : p ≠ 0) :
    ∃ c : Kˣ, contentVal v (C (c : K) * p) = 1 := by
  obtain ⟨i, hi, hval⟩ := exists_coeff_contentVal v hp
  refine ⟨(Units.mk0 (p.coeff i) hi)⁻¹, ?_⟩
  rw [contentVal_C_mul, ← hval, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]
  exact inv_mul_cancel₀ ((Valuation.ne_zero_iff v).mpr hi)

/-- **Pair content normalization.** Two polynomials, not both zero, have a common `Kˣ`-multiple
making the pair jointly primitive (joint content `= 1`). -/
theorem exists_primitive_smul_pair {P Q : K[X]} (hPQ : ¬(P = 0 ∧ Q = 0)) :
    ∃ c : Kˣ, contentVal v (C (c : K) * P) ⊔ contentVal v (C (c : K) * Q) = 1 := by
  obtain ⟨a, ha, haM⟩ : ∃ a : K, a ≠ 0 ∧ v a = contentVal v P ⊔ contentVal v Q := by
    rcases le_total (contentVal v P) (contentVal v Q) with hle | hle
    · rw [sup_eq_right.mpr hle]
      have hQ : Q ≠ 0 := by
        rintro rfl
        rw [contentVal_zero, le_zero_iff, contentVal_eq_zero_iff] at hle
        exact hPQ ⟨hle, rfl⟩
      obtain ⟨i, hi, hval⟩ := exists_coeff_contentVal v hQ
      exact ⟨_, hi, hval⟩
    · rw [sup_eq_left.mpr hle]
      have hP : P ≠ 0 := by
        rintro rfl
        rw [contentVal_zero, le_zero_iff, contentVal_eq_zero_iff] at hle
        exact hPQ ⟨rfl, hle⟩
      obtain ⟨i, hi, hval⟩ := exists_coeff_contentVal v hP
      exact ⟨_, hi, hval⟩
  refine ⟨(Units.mk0 a ha)⁻¹, ?_⟩
  rw [contentVal_C_mul, contentVal_C_mul, ← mul_max, ← haM,
    Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]
  exact inv_mul_cancel₀ ((Valuation.ne_zero_iff v).mpr ha)

end ChabautyColeman
