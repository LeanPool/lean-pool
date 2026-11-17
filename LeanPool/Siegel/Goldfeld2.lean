/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Siegel.Goldfeld1
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Goldfeld's lemma

For `7/8 ≤ β < 1` with `Re F(β) ≤ 0`:
`‖L(1,χ₁) L(1,χ₂) L(1,χ₁χ₂)‖ ≥ (1-β)/2 · (50000 Q²)^{-4(1-β)}`, `Q = N₁N₂`.
-/

@[expose] public section

open Complex DirichletCharacter Metric Set Filter Topology LSeries Finset

open scoped ComplexOrder LSeries.notation Nat

namespace SiegelThmLib

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
variable {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}

/-- The Taylor coefficients of `G` at `2`, evaluated at `β`. -/
lemma taylor_term_eq (β : ℝ) (n : ℕ) :
    ((n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (G χ₁ χ₂) 2) =
      (((2 - β) ^ n : ℝ) : ℂ) *
        ((n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (LSeries ↗(coeff χ₁ χ₂)) 2) - P χ₁ χ₂ 1) := by
  rw [iteratedDeriv_G]
  have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsq : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  have hb : (β : ℂ) - 2 = -(((2 - β : ℝ)) : ℂ) := by push_cast; ring
  have hinv : (n ! : ℂ)⁻¹ * (n ! : ℂ) = 1 := inv_mul_cancel₀ hfac
  rw [hb, neg_pow, smul_eq_mul, smul_eq_mul]
  push_cast
  linear_combination (-(P χ₁ χ₂ 1) * (2 - (β : ℂ)) ^ n * (n ! : ℂ)⁻¹ * (n ! : ℂ)) * hsq +
    (-(P χ₁ χ₂ 1) * (2 - (β : ℂ)) ^ n) * hinv

/-- Norm of the Taylor terms. -/
lemma norm_taylor_term_le (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hψ : prodChar χ₁ χ₂ ≠ 1)
    {β : ℝ} (hβ : β ≤ 2) (n : ℕ) :
    ‖(n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (G χ₁ χ₂) 2‖ ≤
      4000 * ((N₁ : ℝ) * N₂) ^ 2 * (2 * (2 - β) / 3) ^ n := by
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hb : ‖(β : ℂ) - 2‖ = 2 - β := by
    rw [show (β : ℂ) - 2 = ((β - 2 : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  rw [norm_smul, norm_smul, norm_pow, hb, norm_inv, norm_natCast]
  have h := norm_iteratedDeriv_G_le hχ₁ hχ₂ hψ n
  have hx : 0 ≤ (2 - β) ^ n := pow_nonneg (by linarith) n
  calc (n ! : ℝ)⁻¹ * ((2 - β) ^ n * ‖iteratedDeriv n (G χ₁ χ₂) 2‖)
      ≤ (n ! : ℝ)⁻¹ * ((2 - β) ^ n *
          (n ! * (4000 * ((N₁ : ℝ) * N₂) ^ 2) / (3 / 2) ^ n)) := by gcongr
    _ = 4000 * ((N₁ : ℝ) * N₂) ^ 2 * (2 * (2 - β) / 3) ^ n := by
        rw [show (2 * (2 - β) / 3) ^ n = 2 ^ n * (2 - β) ^ n / 3 ^ n by rw [div_pow, mul_pow],
          div_pow]
        field_simp

/-- Re of the Taylor terms, in terms of the derivatives of the L-series. -/
lemma re_taylor_term (β : ℝ) (n : ℕ) :
    ((n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (G χ₁ χ₂) 2).re =
      (2 - β) ^ n * (((-1) ^ n * iteratedDeriv n (LSeries ↗(coeff χ₁ χ₂)) 2).re /
        (n ! : ℝ) - (P χ₁ χ₂ 1).re) := by
  rw [taylor_term_eq, re_ofReal_mul, sub_re,
    show ((n ! : ℂ))⁻¹ = (((n ! : ℝ))⁻¹ : ℝ) by simp, re_ofReal_mul]
  ring

/-- The main inequality: `Re F(β) ≥ 1 - ‖λ‖ (2-β)^M / (1-β) - 16000 Q² (3/4)^M`. -/
lemma re_F_ge (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hψ : prodChar χ₁ χ₂ ≠ 1) (h₁ : χ₁ ^ 2 = 1)
    (h₂ : χ₂ ^ 2 = 1) {β : ℝ} (hβ1 : 7 / 8 ≤ β) (hβ2 : β < 1) {M : ℕ} (hM : 1 ≤ M) :
    1 - ‖P χ₁ χ₂ 1‖ * (2 - β) ^ M / (1 - β) - 16000 * ((N₁ : ℝ) * N₂) ^ 2 * (3 / 4) ^ M ≤
      (F χ₁ χ₂ β).re := by
  have hMG0 : 0 ≤ 4000 * ((N₁ : ℝ) * N₂) ^ 2 := by positivity
  have hρ0 : 0 < 2 * (2 - β) / 3 := by linarith only [hβ2]
  have hρ1 : 2 * (2 - β) / 3 ≤ 3 / 4 := by linarith only [hβ1]
  -- Taylor expansion of `G` at `2`
  have hdiff : DifferentiableOn ℂ (G χ₁ χ₂) (ball (2 : ℂ) 2) := by
    refine (differentiableOn_G hχ₁ hχ₂ hψ).mono fun z hz => ?_
    rw [mem_ball, dist_eq] at hz
    have h := abs_re_le_norm (z - 2)
    rw [sub_re] at h
    have := (abs_lt.mp (lt_of_le_of_lt h hz)).1
    simp only [mem_ofPred_eq]
    norm_num at this
    linarith only [this]
  have hβmem : (β : ℂ) ∈ ball (2 : ℂ) 2 := by
    rw [mem_ball, dist_eq, show (β : ℂ) - 2 = ((β - 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_nonpos (by linarith only [hβ2])]
    linarith only [hβ1]
  have hT := Complex.hasSum_taylorSeries_on_ball hdiff hβmem
  have hR := Complex.hasSum_re hT
  -- lower bounds for the terms
  have hr_tail : ∀ n, -(4000 * ((N₁ : ℝ) * N₂) ^ 2 * (2 * (2 - β) / 3) ^ n) ≤
      ((n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (G χ₁ χ₂) 2).re := by
    intro n
    have h := norm_taylor_term_le hχ₁ hχ₂ hψ (β := β) (by linarith only [hβ2]) n
    have h' := neg_abs_le
      (((n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (G χ₁ χ₂) 2).re)
    have h'' := abs_re_le_norm ((n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (G χ₁ χ₂) 2)
    exact (neg_le_neg (h''.trans h)).trans h'
  have hr_head : ∀ n, (if n = 0 then (1 : ℝ) else 0) - (2 - β) ^ n * (P χ₁ χ₂ 1).re ≤
      ((n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (G χ₁ χ₂) 2).re := by
    intro n
    rw [re_taylor_term]
    have hD := Dn_nonneg h₁ h₂ n
    have hDre : 0 ≤ ((-1) ^ n * iteratedDeriv n (LSeries ↗(coeff χ₁ χ₂)) 2).re :=
      (Complex.le_def.mp hD).1
    have hxn : 0 ≤ (2 - β) ^ n := pow_nonneg (by linarith only [hβ2]) n
    have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    split_ifs with hn
    · subst hn
      have h0 := one_le_D0 h₁ h₂ (χ₁ := χ₁) (χ₂ := χ₂)
      simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one,
        div_one]
      linarith only [h0]
    · have : 0 ≤ ((-1) ^ n * iteratedDeriv n (LSeries ↗(coeff χ₁ χ₂)) 2).re / (n ! : ℝ) :=
        div_nonneg hDre hfac.le
      nlinarith only [mul_nonneg hxn this]
  -- split the sum at `M`
  have hsplit := Summable.sum_add_tsum_nat_add M hR.summable
  rw [hR.tsum_eq] at hsplit
  have hhead : 1 - (P χ₁ χ₂ 1).re * ∑ n ∈ range M, (2 - β) ^ n ≤
      ∑ n ∈ range M, ((n ! : ℂ)⁻¹ • ((β : ℂ) - 2) ^ n • iteratedDeriv n (G χ₁ χ₂) 2).re := by
    have h1 := Finset.sum_le_sum fun n (_ : n ∈ range M) => hr_head n
    have h2 : ∑ n ∈ range M, ((if n = 0 then (1 : ℝ) else 0) - (2 - β) ^ n * (P χ₁ χ₂ 1).re) =
        1 - (P χ₁ χ₂ 1).re * ∑ n ∈ range M, (2 - β) ^ n := by
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr (by omega)),
        ← Finset.sum_mul]
      ring
    exact h2 ▸ h1
  have hgeo : Summable fun n : ℕ =>
      4000 * ((N₁ : ℝ) * N₂) ^ 2 * (2 * (2 - β) / 3) ^ (n + M) := by
    simp_rw [pow_add]
    exact ((summable_geometric_of_lt_one hρ0.le (by linarith only [hρ1])).mul_right _).mul_left _
  have htail : -(4000 * ((N₁ : ℝ) * N₂) ^ 2 * (2 * (2 - β) / 3) ^ M * 4) ≤
      ∑' n, ((((n + M) ! : ℂ))⁻¹ • ((β : ℂ) - 2) ^ (n + M) •
        iteratedDeriv (n + M) (G χ₁ χ₂) 2).re := by
    have hsr := (summable_nat_add_iff M).mpr hR.summable
    have h1 := hgeo.neg.tsum_le_tsum (fun n => hr_tail (n + M)) hsr
    have h2 : ∑' n, -(4000 * ((N₁ : ℝ) * N₂) ^ 2 * (2 * (2 - β) / 3) ^ (n + M)) =
        -(4000 * ((N₁ : ℝ) * N₂) ^ 2 * (2 * (2 - β) / 3) ^ M * (1 - 2 * (2 - β) / 3)⁻¹) := by
      rw [tsum_neg]
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right,
        tsum_geometric_of_lt_one hρ0.le (by linarith only [hρ1])]
      ring
    have h3 : (1 - 2 * (2 - β) / 3)⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ (by linarith only [hρ1]) (by norm_num)]
      linarith only [hρ1]
    have h4 : 4000 * ((N₁ : ℝ) * N₂) ^ 2 * (2 * (2 - β) / 3) ^ M * (1 - 2 * (2 - β) / 3)⁻¹ ≤
        4000 * ((N₁ : ℝ) * N₂) ^ 2 * (2 * (2 - β) / 3) ^ M * 4 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    rw [h2] at h1
    exact (neg_le_neg h4).trans h1
  have hρM : (2 * (2 - β) / 3) ^ M ≤ (3 / 4 : ℝ) ^ M := pow_le_pow_left₀ hρ0.le hρ1 M
  have hGre : 1 - (P χ₁ χ₂ 1).re * ∑ n ∈ range M, (2 - β) ^ n -
      16000 * ((N₁ : ℝ) * N₂) ^ 2 * (3 / 4) ^ M ≤ (G χ₁ χ₂ β).re := by
    have : 4000 * ((N₁ : ℝ) * N₂) ^ 2 * (2 * (2 - β) / 3) ^ M * 4 ≤
        16000 * ((N₁ : ℝ) * N₂) ^ 2 * (3 / 4) ^ M := by
      nlinarith only [hρM, hMG0]
    linarith only [hhead, htail, hsplit, this]
  -- pass from `G` to `F`
  have hβ1' : (β : ℂ) ≠ 1 := by
    exact_mod_cast hβ2.ne
  have hFG : F χ₁ χ₂ β = G χ₁ χ₂ β + P χ₁ χ₂ 1 / ((β - 1 : ℝ) : ℂ) := by
    rw [G_eq hβ1']; push_cast; ring
  have hFre : (F χ₁ χ₂ β).re = (G χ₁ χ₂ β).re + (P χ₁ χ₂ 1).re / (β - 1) := by
    rw [hFG, add_re, div_ofReal_re]
  have hgs : ∑ n ∈ range M, (2 - β) ^ n = ((2 - β) ^ M - 1) / ((2 - β) - 1) :=
    geom_sum_eq (by linarith only [hβ2]) M
  have hlam : (P χ₁ χ₂ 1).re ≤ ‖P χ₁ χ₂ 1‖ := re_le_norm _
  have hxM : 0 ≤ (2 - β) ^ M / (1 - β) :=
    div_nonneg (pow_nonneg (by linarith only [hβ2]) M) (sub_nonneg.mpr hβ2.le)
  have hkey : 1 - (P χ₁ χ₂ 1).re * ∑ n ∈ range M, (2 - β) ^ n + (P χ₁ χ₂ 1).re / (β - 1) =
      1 - (P χ₁ χ₂ 1).re * (2 - β) ^ M / (1 - β) := by
    rw [hgs]
    have h1 : (2 - β - 1) = 1 - β := by ring
    have h2 : β - 1 = -(1 - β) := by ring
    rw [h1, h2]
    have h3 : (1 - β) ≠ 0 := (sub_pos.mpr hβ2).ne'
    field_simp [h3]
    ring
  have hfin : -(‖P χ₁ χ₂ 1‖ * (2 - β) ^ M / (1 - β)) ≤
      -((P χ₁ χ₂ 1).re * (2 - β) ^ M / (1 - β)) := by
    rw [neg_le_neg_iff, mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hlam hxM
  rw [hFre]
  linarith only [hGre, hkey, hfin]

/-- `x ≤ (4/3)^{4(x-1)}` for `x ≥ 1`. -/
lemma le_four_thirds_rpow {u : ℝ} (hu : 0 ≤ u) : 1 + u ≤ (4 / 3 : ℝ) ^ (4 * u) := by
  have hlog : (1 : ℝ) / 4 ≤ Real.log (4 / 3) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at this ⊢; linarith
  rw [Real.rpow_def_of_pos (by norm_num)]
  calc 1 + u = u + 1 := by ring
    _ ≤ Real.exp u := Real.add_one_le_exp u
    _ ≤ Real.exp (Real.log (4 / 3) * (4 * u)) := by
        apply Real.exp_le_exp.mpr; nlinarith

/-- **Goldfeld's lemma.** -/
theorem goldfeld (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hψ : prodChar χ₁ χ₂ ≠ 1) (h₁ : χ₁ ^ 2 = 1)
    (h₂ : χ₂ ^ 2 = 1) {β : ℝ} (hβ1 : 7 / 8 ≤ β) (hβ2 : β < 1) (hF : (F χ₁ χ₂ β).re ≤ 0) :
    (1 - β) / 2 * (50000 * ((N₁ : ℝ) * N₂) ^ 2) ^ (-(4 * (1 - β))) ≤ ‖P χ₁ χ₂ 1‖ := by
  set Q2 : ℝ := ((N₁ : ℝ) * N₂) ^ 2 with hQ2
  have hQ1 : 1 ≤ Q2 := by
    have h1 : (1 : ℝ) ≤ N₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N₁)
    have h2 : (1 : ℝ) ≤ N₂ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N₂)
    rw [hQ2]; exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le h1 h2)
  set T : ℝ := 32000 * Q2 with hT
  have hex : ∃ M : ℕ, T ≤ (4 / 3 : ℝ) ^ M := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt T (by norm_num : (1 : ℝ) < 4 / 3)
    exact ⟨n, hn.le⟩
  classical
  set M := Nat.find hex with hMdef
  have hM : T ≤ (4 / 3 : ℝ) ^ M := Nat.find_spec hex
  have hM1 : 1 ≤ M := by
    by_contra h
    have h0 : M = 0 := by omega
    rw [h0, pow_zero] at hM
    linarith only [hM, hQ1]
  have hMmin : (4 / 3 : ℝ) ^ (M - 1) < T := by
    have := Nat.find_min hex (show M - 1 < M by omega)
    exact lt_of_not_ge this
  have hMup : (4 / 3 : ℝ) ^ M ≤ 50000 * Q2 := by
    have : (4 / 3 : ℝ) ^ M = 4 / 3 * (4 / 3) ^ (M - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]
    linarith only [hMmin, hQ1]
  have hpow_pos : (0 : ℝ) < (4 / 3) ^ M := by positivity
  have htail : 16000 * Q2 * (3 / 4 : ℝ) ^ M ≤ 1 / 2 := by
    have : (3 / 4 : ℝ) ^ M = 1 / (4 / 3) ^ M := by
      rw [one_div, ← inv_pow]; norm_num
    rw [this, mul_one_div, div_le_iff₀ hpow_pos]
    linarith only [hM]
  have hmain := re_F_ge hχ₁ hχ₂ hψ h₁ h₂ hβ1 hβ2 hM1
  rw [← hQ2] at hmain
  set u : ℝ := 1 - β with hu
  have hu0 : 0 < u := sub_pos.mpr hβ2
  set x : ℝ := 2 - β with hx
  have hxu : x = 1 + u := by rw [hx, hu]; ring
  have hlamx : u / 2 ≤ ‖P χ₁ χ₂ 1‖ * x ^ M := by
    have h1 : 1 - ‖P χ₁ χ₂ 1‖ * x ^ M / u - 1 / 2 ≤ 0 := by
      linarith only [hmain, hF, htail]
    have h2 : 1 / 2 ≤ ‖P χ₁ χ₂ 1‖ * x ^ M / u := by linarith only [h1]
    rw [le_div_iff₀ hu0] at h2
    linarith only [h2]
  -- `x^M ≤ (50000 Q²)^{4u}`
  have hxM : x ^ M ≤ (50000 * Q2) ^ (4 * u) := by
    have h1 : x ≤ (4 / 3 : ℝ) ^ (4 * u) := by rw [hxu]; exact le_four_thirds_rpow hu0.le
    have h2 : x ^ M ≤ ((4 / 3 : ℝ) ^ (4 * u)) ^ M :=
      pow_le_pow_left₀ (by linarith only [hβ2]) h1 M
    have h3 : ((4 / 3 : ℝ) ^ (4 * u)) ^ M = ((4 / 3 : ℝ) ^ M) ^ (4 * u) := by
      rw [← Real.rpow_natCast ((4 / 3 : ℝ) ^ (4 * u)) M, ← Real.rpow_mul (by norm_num),
        mul_comm (4 * u) (M : ℝ), Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have h4 : ((4 / 3 : ℝ) ^ M) ^ (4 * u) ≤ (50000 * Q2) ^ (4 * u) :=
      Real.rpow_le_rpow hpow_pos.le hMup (mul_nonneg (by norm_num) hu0.le)
    exact h2.trans (h3.le.trans h4)
  have hY : (0 : ℝ) < (50000 * Q2) ^ (4 * u) :=
    Real.rpow_pos_of_pos (by linarith only [hQ1]) _
  rw [Real.rpow_neg (by linarith only [hQ1])]
  calc u / 2 * ((50000 * Q2) ^ (4 * u))⁻¹ ≤ ‖P χ₁ χ₂ 1‖ * x ^ M * ((50000 * Q2) ^ (4 * u))⁻¹ :=
        mul_le_mul_of_nonneg_right hlamx (inv_nonneg.mpr hY.le)
    _ ≤ ‖P χ₁ χ₂ 1‖ * (50000 * Q2) ^ (4 * u) * ((50000 * Q2) ^ (4 * u))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxM (norm_nonneg _))
          (inv_nonneg.mpr hY.le)
    _ = ‖P χ₁ χ₂ 1‖ := by rw [mul_assoc, mul_inv_cancel₀ hY.ne', mul_one]

end SiegelThmLib
