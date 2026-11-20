/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Analysis.Complex.Basic

/-!
# Root quadrature for Laurent coefficients

The finite geometric-sum proof of Lemma 3.7 avoids contour integration.
The `m` nodes are `ξ ζʲ`, where `ζ` is a primitive `m`th root and `ξᵐ = η`.
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- The sum of all powers of a primitive root, for an arbitrary integer exponent. -/
theorem sum_root_zpow {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (r : ℤ) :
    ∑ j ∈ Finset.range m, (ζ ^ j) ^ r = if (m : ℤ) ∣ r then (m : ℂ) else 0 := by
  classical
  have hcomm (j : ℕ) : (ζ ^ j) ^ r = (ζ ^ r) ^ j := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  simp_rw [hcomm]
  by_cases hd : (m : ℤ) ∣ r
  · rw [ite_eq_left hd, (hζ.zpow_eq_one_iff_dvd r).mpr hd]
    simp
  · rw [ite_eq_right hd]
    have hne : ζ ^ r - 1 ≠ 0 := sub_ne_zero.mpr (mt (hζ.zpow_eq_one_iff_dvd r).mp hd)
    have hp : (ζ ^ r) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hζ.pow_eq_one, one_zpow]
    have h := mul_geom_sum (ζ ^ r) m
    rw [hp, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left hne

/-- Average of a Laurent monomial at the `m` root nodes. -/
noncomputable def rootMonomialAverage (m : ℕ) (ξ ζ : ℂ) (r : ℤ) : ℂ :=
  (m : ℂ)⁻¹ * ∑ j ∈ Finset.range m, (ξ * ζ ^ j) ^ r

theorem rootMonomialAverage_eq {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (ξ : ℂ) (r : ℤ) :
    rootMonomialAverage m ξ ζ r = if (m : ℤ) ∣ r then ξ ^ r else 0 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [rootMonomialAverage, mul_zpow, ← Finset.mul_sum]
  rw [sum_root_zpow hζ]
  split_ifs <;> simp_all [mul_left_comm]

/-- In the exponent range of Lemma 3.7 only `-m`, `0`, and `m` are divisible by `m`. -/
theorem dvd_in_quadrature_range {m : ℕ} (hm : 0 < m) {r : ℤ}
    (hrlo : -(2 * (m : ℤ)) < r) (hrhi : r < 2 * (m : ℤ)) (hd : (m : ℤ) ∣ r) :
    r = -(m : ℤ) ∨ r = 0 ∨ r = m := by
  obtain ⟨q, rfl⟩ := hd
  have hmpos : (0 : ℤ) < m := by exact_mod_cast hm
  have hlo : -1 ≤ q := by
    by_contra h
    have hq : q ≤ -2 := by omega
    nlinarith [mul_nonneg (show 0 ≤ -q - 2 by omega) hmpos.le]
  have hhi : q ≤ 1 := by
    by_contra h
    have hq : 2 ≤ q := by omega
    nlinarith [mul_nonneg (show 0 ≤ q - 2 by omega) hmpos.le]
  interval_cases q <;> simp

/-- Root quadrature as a linear functional on finitely supported Laurent coefficients. -/
noncomputable def rootQuadrature (m : ℕ) (ξ ζ : ℂ) : (ℤ →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (rootMonomialAverage m ξ ζ)

/-- This coefficient definition equals the average of Laurent evaluations at the nodes. -/
theorem rootQuadrature_eq_average (m : ℕ) (ξ ζ : ℂ) (g : ℤ →₀ ℂ) :
    rootQuadrature m ξ ζ g = (m : ℂ)⁻¹ * ∑ j ∈ Finset.range m,
      ∑ r ∈ g.support, g r * (ξ * ζ ^ j) ^ r := by
  simp only [rootQuadrature, Finsupp.linearCombination_apply, Finsupp.sum,
    smul_eq_mul, rootMonomialAverage]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rootMonomialAverage_three {m : ℕ} (hm : 0 < m) {ζ ξ η : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = η) (hη : η = 1 ∨ η = -1)
    {r : ℤ} (hrlo : -(2 * (m : ℤ)) < r) (hrhi : r < 2 * (m : ℤ)) :
    rootMonomialAverage m ξ ζ r =
      (if r = 0 then 1 else 0) +
        η * ((if r = (m : ℤ) then 1 else 0) + (if r = -(m : ℤ) then 1 else 0)) := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hopp : (m : ℤ) ≠ -(m : ℤ) := by
    have : (0 : ℤ) < m := by exact_mod_cast hm
    omega
  have hηinv : η⁻¹ = η := by rcases hη with rfl | rfl <;> norm_num
  rw [rootMonomialAverage_eq hm hζ]
  by_cases h0 : r = 0
  · subst r
    simp [hm.ne', Ne.symm hm0]
  by_cases hp : r = (m : ℤ)
  · subst r
    simp [hm.ne', hopp, hξ]
  by_cases hn : r = -(m : ℤ)
  · subst r
    simp [hm.ne', hopp.symm, zpow_neg, hξ, hηinv]
  have hnd : ¬(m : ℤ) ∣ r := by
    intro hd
    rcases dvd_in_quadrature_range hm hrlo hrhi hd with he | he | he
    · exact hn he
    · exact h0 he
    · exact hp he
  simp [hnd, h0, hp, hn]

/-- Lemma 3.7: only the constant and the two `m`th Laurent coefficients survive.
The support bound is the only degree hypothesis required. -/
theorem rootQuadrature_three_coefficients {m : ℕ} (hm : 0 < m) {ζ ξ η : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = η) (hη : η = 1 ∨ η = -1)
    (g : ℤ →₀ ℂ)
    (hg : ∀ r ∈ g.support, -(2 * (m : ℤ)) < r ∧ r < 2 * (m : ℤ)) :
    rootQuadrature m ξ ζ g = g 0 + η * (g m + g (-(m : ℤ))) := by
  classical
  change (∑ r ∈ g.support, g r * rootMonomialAverage m ξ ζ r) = _
  have heq : (∑ r ∈ g.support, g r * rootMonomialAverage m ξ ζ r) =
      ∑ r ∈ g.support, g r * ((if r = 0 then 1 else 0) +
        η * ((if r = (m : ℤ) then 1 else 0) + (if r = -(m : ℤ) then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [rootMonomialAverage_three hm hζ hξ hη (hg r hr).1 (hg r hr).2]
  rw [heq]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finsupp.if_mem_support]
  by_cases hp : (m : ℤ) ∈ g.support <;> by_cases hn : -(m : ℤ) ∈ g.support <;>
    simp_all [Finsupp.mem_support_iff] <;> ring

end NoncommutativeAMGM
