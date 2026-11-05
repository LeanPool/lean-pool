/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Sieve.SieveProductLowerBound

/-! # Comparing the sifting product at two power-related cutoffs -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- Exact restoration of the factors between two cutoffs. -/
theorem sieveProduct_cutoff_identity {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {w z : ℝ} (hw : 0 ≤ w) (hwz : w ≤ z) :
    sieveProduct Q w = sieveProduct Q z *
      ∏ p ∈ (primeBandNumbers w z).filter Nat.Prime, (1 - (rootCount Q p : ℝ) / p)⁻¹ := by
  let S := (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime
  let f := fun p => 1 - (rootCount Q p : ℝ) / p
  have hlow : S.filter (fun p : ℕ => (p : ℝ) ≤ w) = (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_, hp⟩, hpw⟩
      exact ⟨(Nat.le_floor_iff hw).mpr hpw, hp⟩
    · rintro ⟨hpw, hp⟩
      exact ⟨⟨hpw.trans (Nat.floor_mono hwz), hp⟩, (Nat.le_floor_iff hw).mp hpw⟩
  have hhigh : S.filter (fun p : ℕ => ¬(p : ℝ) ≤ w) = (primeBandNumbers w z).filter Nat.Prime := by
    ext p
    simp only [S, primeBandNumbers, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
      Finset.mem_Icc, Nat.zero_le, true_and, not_le]
    tauto
  have H := Finset.prod_filter_mul_prod_filter_not S (fun p : ℕ => (p : ℝ) ≤ w) f
  rw [hlow, hhigh] at H
  change sieveProduct Q w * (∏ p ∈ (primeBandNumbers w z).filter Nat.Prime, f p) = sieveProduct Q
      z at H
  have hne : (∏ p ∈ (primeBandNumbers w z).filter Nat.Prime, f p) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    exact (sub_pos.mpr ((div_lt_one (by exact_mod_cast hp'.pos : (0 : ℝ) < p)).mpr
      (by exact_mod_cast hQ p hp'))).ne'
  rw [Finset.prod_inv_distrib, ← H]
  change sieveProduct Q w = sieveProduct Q w * _ * _⁻¹
  rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- A coefficient-independent comparison in terms of the logarithm ratio. -/
theorem sieveProduct_cutoff_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {g : ℕ} (hg : Q.natDegree ≤ g) {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z)
    (hgw : 2 * (g : ℝ) ≤ w) :
    sieveProduct Q w ≤ sieveProduct Q z *
      Real.exp (2 * (g : ℝ) * (Real.log 4 * (1 + Real.log z) / Real.log w)) := by
  let T := (primeBandNumbers w z).filter Nat.Prime
  have hlocal (p : ℕ) (hp : p ∈ T) :
      (1 - (rootCount Q p : ℝ) / p)⁻¹ ≤ Real.exp (2 * (g : ℝ) / p) := by
    have hwp := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    apply sieveFactor_inv_le_exp hQ hg (Finset.mem_filter.mp hp).2
    exact_mod_cast hgw.trans hwp.le
  have hprod : (∏ p ∈ T, (1 - (rootCount Q p : ℝ) / p)⁻¹) ≤
      Real.exp (2 * (g : ℝ) * (Real.log 4 * (1 + Real.log z) / Real.log w)) := by
    calc
      _ ≤ ∏ p ∈ T, Real.exp (2 * (g : ℝ) / p) := Finset.prod_le_prod₀
        (fun p hp => inv_nonneg.mpr (sub_nonneg.mpr ((div_le_one
          (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos : (0 : ℝ) < p)).mpr
            (by exact_mod_cast (hQ p (Finset.mem_filter.mp hp).2).le)))) hlocal
      _ = Real.exp (2 * (g : ℝ) * ∑ p ∈ T, (p : ℝ)⁻¹) := by
        rw [← Real.exp_sum, Finset.mul_sum]
        simp only [div_eq_mul_inv]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (primeBand_reciprocal_sum_le hw (hw.trans hwz)) (by positivity))
  rw [sieveProduct_cutoff_identity hQ (by linarith) hwz]
  exact mul_le_mul_of_nonneg_left hprod (sieveProduct_pos hQ z).le

/-- At `w=x^α`, the comparison costs a constant depending only on degree and
`α`, once the smaller cutoff exceeds `2g` and `log x≥1`. -/
theorem sieveProduct_power_cutoff_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {g : ℕ} (hg : Q.natDegree ≤ g) {α x : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1)
    (hx : 1 ≤ x) (hlog : 1 ≤ Real.log x) (hw : 2 ≤ x ^ α) (hgw : 2 * (g : ℝ) ≤ x ^ α) :
    sieveProduct Q (x ^ α) ≤ Real.exp (4 * (g : ℝ) * Real.log 4 / α) * sieveProduct Q x := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hcut : x ^ α ≤ x := by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hx hα₁
  apply (sieveProduct_cutoff_le hQ hg hw hcut hgw).trans
  rw [mul_comm (Real.exp _)]
  apply mul_le_mul_of_nonneg_left _ (sieveProduct_pos hQ x).le
  apply Real.exp_le_exp.mpr
  rw [Real.log_rpow hx₀]
  have hden : 0 < α * Real.log x := mul_pos hα (by linarith)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have H : (1 + Real.log x) / Real.log x ≤ 2 :=
    (div_le_iff₀ (by linarith : 0 < Real.log x)).mpr (by linarith)
  have H' := mul_le_mul_of_nonneg_left H
    (div_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * (g : ℝ)) hlog4) hα.le)
  convert H' using 1 <;> ring

/-- Uniform threshold for the power-cutoff comparison. -/
theorem exists_sieveProduct_power_cutoff_bound (g : ℕ) {α : ℝ}
    (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ Q : ℤ[X],
      NoFixedPrimeDivisor Q → Q.natDegree ≤ g →
      sieveProduct Q (x ^ α) ≤ Real.exp (4 * (g : ℝ) * Real.log 4 / α) * sieveProduct Q x := by
  let M : ℝ := max 2 (2 * (g : ℝ))
  let t : ℝ := max 1 (Real.log M / α)
  have ht₁ : 1 ≤ t := le_max_left _ _
  have hM : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  refine ⟨Real.exp t, Real.one_le_exp_iff.mpr (by linarith), ?_⟩
  intro x hx Q hQ hg
  have hx₁ : 1 ≤ x := (Real.one_le_exp_iff.mpr (by linarith : 0 ≤ t)).trans hx
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx₁
  have hlog : t ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos t) hx
  have hw : M ≤ x ^ α := by
    apply (Real.log_le_log_iff hM (Real.rpow_pos_of_pos hx₀ α)).mp
    rw [Real.log_rpow hx₀]
    have H := (div_le_iff₀ hα).mp ((le_max_right _ _).trans hlog)
    nlinarith
  exact sieveProduct_power_cutoff_le hQ hg hα hα₁ hx₁ (ht₁.trans hlog)
    ((le_max_left _ _).trans hw) ((le_max_right _ _).trans hw)

end NairTenenbaum
