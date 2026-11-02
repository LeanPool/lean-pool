/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Contributions.RealIntervalBounds
public import LeanPool.NairTenenbaum.Polynomials.PolynomialValueBounds

/-! # Common height and growth margins for Theorems 1 and 3

Only one eighth of a power is spent absorbing the degree-dependent evaluation
constant. This leaves a positive saving at the paper's exponent `εδ/3`.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial

theorem primeArgument_growth_margin {g : ℕ} (hg : 0 < g) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ((g : ℝ) + 1 / δ + 1 / 8) * (ε * δ / 3) ≤ 17 * (g : ℝ) * ε / 24 := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hgd := mul_le_mul_of_nonneg_left hδ₁ (Nat.cast_nonneg g : (0 : ℝ) ≤ g)
  have hinner : (g : ℝ) * δ + 1 + δ / 8 ≤ 17 * (g : ℝ) / 8 := by nlinarith
  calc
    _ = ε * ((g : ℝ) * δ + 1 + δ / 8) / 3 := by field_simp
    _ ≤ ε * (17 * (g : ℝ) / 8) / 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinner hε) (by norm_num)
    _ = _ := by ring

theorem eval_natAbs_le_primeArgument_rpow {Q : ℤ[X]} {g : ℕ} (hdeg : Q.natDegree = g)
    {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ)
    (hheight : (polynomialHeight Q : ℝ) ^ δ ≤ x)
    (hlarge : (((g : ℝ) + 1) * 2 ^ g) ^ (8 : ℕ) ≤ x)
    {t : ℤ} (ht : (t.natAbs : ℝ) ≤ 2 * x) :
    ((Q.eval t).natAbs : ℝ) ≤ x ^ ((g : ℝ) + 1 / δ + 1 / 8) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hconst : ((g : ℝ) + 1) * 2 ^ g ≤ x ^ (1 / 8 : ℝ) := by
    have H := Real.rpow_le_rpow (by positivity) hlarge (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at H
    norm_num at H
    exact H
  calc
    _ ≤ (((g : ℝ) + 1) * 2 ^ g) * x ^ ((g : ℝ) + 1 / δ) :=
      eval_natAbs_le_const_rpow_of_height hdeg hx hδ hheight ht
    _ ≤ x ^ (1 / 8 : ℝ) * x ^ ((g : ℝ) + 1 / δ) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring

/-- One coefficient-independent threshold supplies the rounded interval and value bounds. -/
theorem exists_height_interval_threshold (g : ℕ) {δ τ : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (x₀ : ℝ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (Q : ℤ[X]), Q ≠ 0 → Q.natDegree = g →
      ∀ x y : ℝ, c₀ * (polynomialHeight Q : ℝ) ^ δ < x → x ^ τ ≤ y → y ≤ x →
      x₀ ≤ x ∧ (⌊x⌋₊ : ℤ) ≤ (⌊x + y⌋₊ : ℤ) ∧
      y / 2 ≤ ((⌊x + y⌋₊ : ℤ) : ℝ) - (⌊x⌋₊ : ℤ) ∧
      ((⌊x + y⌋₊ : ℤ) : ℝ) - (⌊x⌋₊ : ℤ) ≤ 2 * y ∧
      ∀ t ∈ Finset.Ioc (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ),
        ((Q.eval t).natAbs : ℝ) ≤ x ^ ((g : ℝ) + 1 / δ + 1 / 8) := by
  let c₀ := max x₀ (max 2 (max ((((g : ℝ) + 1) * 2 ^ g) ^ (8 : ℕ))
    ((2 : ℝ) ^ (1 / τ))))
  have ⟨hc₁, hc₂, hcH, hcτ⟩ : x₀ ≤ c₀ ∧ 2 ≤ c₀ ∧
      (((g : ℝ) + 1) * 2 ^ g) ^ (8 : ℕ) ≤ c₀ ∧ (2 : ℝ) ^ (1 / τ) ≤ c₀ := by
    simp [c₀, le_max_iff]
  refine ⟨c₀, by linarith, ?_⟩
  intro Q hQ hdeg x y hx hy hyx
  have hH : (1 : ℝ) ≤ (polynomialHeight Q : ℝ) := one_le_polynomialHeight hQ
  have hHδ : 1 ≤ (polynomialHeight Q : ℝ) ^ δ := Real.one_le_rpow hH hδ.le
  have hcx : c₀ ≤ x := (le_mul_of_one_le_right (by linarith : 0 ≤ c₀) hHδ).trans hx.le
  have hx₂ : 2 ≤ x := hc₂.trans hcx
  have hx₁ : 1 ≤ x := by linarith
  have hheight : (polynomialHeight Q : ℝ) ^ δ ≤ x :=
    (le_mul_of_one_le_left (zero_le_one.trans hHδ) (by linarith : 1 ≤ c₀)).trans hx.le
  have hy₂ : 2 ≤ y := by
    have Hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (hcτ.trans hcx) hτ.le
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hτ.ne',
      Real.rpow_one] at Hpow
    exact Hpow.trans hy
  obtain ⟨hab, hlen, hlen', hvalues⟩ := shortInterval_endpoint_bounds (by linarith : 0 ≤ x) hy₂ hyx
  refine ⟨hc₁.trans hcx, hab, ?_, ?_, ?_⟩
  · simpa only [Int.cast_natCast] using hlen
  · simpa only [Int.cast_natCast] using hlen'
  · intro t ht
    exact eval_natAbs_le_primeArgument_rpow hdeg hx₁ hδ hheight (hcH.trans hcx) (hvalues t ht)

end NairTenenbaum
