/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepEnvelope

/-!
# HomStepOneArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 1: the `γ`-smallness web of the parameter
# selection

This module contains ONLY the elementary real arithmetic that discharges the
binders of the anchor `Algsuperdiff.Frozen.Section4.bounds_mathcal_E_aL`
at the §4.5 parameter selection `s = |log γ|⁻¹`, `k = ⌈10|log γ|⌉`,
`n = m - k`.  It is kept separate from the anchor-consumption module so that
the consumption itself reads as the source's own four-line instantiation.

Everything is stated in the `γ`-quartic-root gauge `t:= √(√γ)` (so `γ = t⁴`),
which is the smallest gauge in which BOTH the source's `|log γ| √γ → 0` and its
`|log γ| ≤ γ⁻¹` demands are elementary.  The correction is honoured: every
`γ`-dependence stays visible and no `|log γ|`-power is absorbed into a
constant.
-/

open Algsuperdiff.Section3
open HCPolySupport

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The quartic-root gauge -/

/-- `t:= √(√γ)`, the quartic root: `t⁴ = γ`. -/
theorem quarticRoot_pow_four {gamma : ℝ} (h : 0 ≤ gamma) :
    Real.sqrt (Real.sqrt gamma) ^ (4 : ℕ) = gamma := by
  have h1 : Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) = Real.sqrt gamma :=
    Real.sq_sqrt (Real.sqrt_nonneg gamma)
  have h2 : Real.sqrt gamma ^ (2 : ℕ) = gamma := Real.sq_sqrt h
  calc Real.sqrt (Real.sqrt gamma) ^ (4 : ℕ)
      = (Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ = Real.sqrt gamma ^ (2 : ℕ) := by rw [h1]
    _ = gamma := h2

theorem quarticRoot_pos {gamma : ℝ} (h : 0 < gamma) :
    0 < Real.sqrt (Real.sqrt gamma) :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr h)

theorem quarticRoot_sq (gamma : ℝ) :
    Real.sqrt (Real.sqrt gamma) ^ (2 : ℕ) = Real.sqrt gamma :=
  Real.sq_sqrt (Real.sqrt_nonneg gamma)

/-- The gauge transfer: `γ ≤ b⁴` with `b ≥ 0` is `t ≤ b`. -/
theorem quarticRoot_le {gamma b : ℝ} (hg : 0 ≤ gamma) (hb : 0 ≤ b)
    (h : gamma ≤ b ^ (4 : ℕ)) : Real.sqrt (Real.sqrt gamma) ≤ b := by
  have h4 : Real.sqrt (Real.sqrt gamma) ^ (4 : ℕ) ≤ b ^ (4 : ℕ) := by
    rw [quarticRoot_pow_four hg]; exact h
  exact le_of_pow_le_pow_left₀ (by norm_num) hb h4

/-! ## 2. `|log γ|` in the quartic gauge -/

/-- `|log γ| ≤ 4 t⁻¹` for `0 < γ < 1`: the elementary bound
`log x ≤ x - 1` applied to `t⁻¹`.  This is the only place a logarithm is
compared with a power of `γ`. -/
theorem absLog_le_four_div_quarticRoot {gamma : ℝ} (hg : 0 < gamma) (hg1 : gamma < 1) :
    |Real.log gamma| ≤ 4 * (Real.sqrt (Real.sqrt gamma))⁻¹ := by
  set t := Real.sqrt (Real.sqrt gamma) with ht
  have htpos : 0 < t := quarticRoot_pos hg
  have ht4 : t ^ (4 : ℕ) = gamma := quarticRoot_pow_four hg.le
  have hlogt : Real.log gamma = 4 * Real.log t := by
    rw [← ht4, Real.log_pow]
    norm_num
  have hneg : Real.log gamma < 0 := Real.log_neg hg hg1
  have hinv : Real.log t⁻¹ ≤ t⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr htpos)
  have hlt : Real.log t⁻¹ = -Real.log t := Real.log_inv t
  have habs : |Real.log gamma| = -Real.log gamma := abs_of_neg hneg
  have hstep : -Real.log t ≤ t⁻¹ - 1 := by rw [← hlt]; exact hinv
  have hpos : (0 : ℝ) < t⁻¹ := inv_pos.mpr htpos
  rw [habs, hlogt]
  linarith only [hstep, hpos]

/-- `|log γ| √γ ≤ 4 t`: the vanishing that the anchor's lower `s`-endpoint
`C² √γ ≤ s` needs. -/
theorem absLog_mul_sqrt_le {gamma : ℝ} (hg : 0 < gamma) (hg1 : gamma < 1) :
    |Real.log gamma| * Real.sqrt gamma ≤ 4 * Real.sqrt (Real.sqrt gamma) := by
  set t := Real.sqrt (Real.sqrt gamma) with ht
  have htpos : 0 < t := quarticRoot_pos hg
  have htsq : t ^ (2 : ℕ) = Real.sqrt gamma := quarticRoot_sq gamma
  have hbound : |Real.log gamma| ≤ 4 * t⁻¹ := absLog_le_four_div_quarticRoot hg hg1
  have hsq : (0 : ℝ) ≤ Real.sqrt gamma := Real.sqrt_nonneg gamma
  calc |Real.log gamma| * Real.sqrt gamma ≤ (4 * t⁻¹) * Real.sqrt gamma :=
        mul_le_mul_of_nonneg_right hbound hsq
    _ = (4 * t⁻¹) * (t * t) := by rw [← htsq]; ring
    _ = 4 * t := by field_simp

/-! ## 3. The two smallness gates in explicit numeric form -/

section Gates

/-- `exp 4 ≤ 81`: the crude form of `e ≤ 3`, all that the `|log γ| ≥ 4` gate
needs. -/
theorem exp_four_le : Real.exp 4 ≤ 81 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ≤ 3 := by linarith only [h1]
  have h0 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hpow : Real.exp 1 ^ (4 : ℕ) ≤ 3 ^ (4 : ℕ) := pow_le_pow_left₀ h0 h3 4
  have heq : Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [heq]
  calc Real.exp 1 ^ (4 : ℕ) ≤ 3 ^ (4 : ℕ) := hpow
    _ = 81 := by norm_num

/-- The gate in numeric form: `γ ≤ 1/81` forces `4 ≤ |log γ|`, hence
`s = |log γ|⁻¹ ≤ 1/4`. -/
theorem four_le_absLog {gamma : ℝ} (hg : 0 < gamma) (hsmall : gamma ≤ 1 / 81) :
    4 ≤ |Real.log gamma| := by
  have hexp : Real.exp 4 ≤ 81 := exp_four_le
  have hepos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  have hle : gamma ≤ Real.exp (-4) := by
    rw [Real.exp_neg]
    have h81 : (1 : ℝ) / 81 ≤ (Real.exp 4)⁻¹ := by
      have hdiv := one_div_le_one_div_of_le hepos hexp
      rwa [one_div (Real.exp 4)] at hdiv
    exact le_trans hsmall h81
  have hlog : Real.log gamma ≤ -4 := by
    have := Real.log_le_log hg hle
    rwa [Real.log_exp] at this
  have hneg : Real.log gamma < 0 := by linarith only [hlog]
  rw [abs_of_neg hneg]
  linarith only [hlog]

end Gates

/-! ## 4. The §4.5 parameter facts under the two gates -/

section Web

variable (M : ABKModel d)

/-- `s = |log γ|⁻¹` is positive under the `|log γ| ≥ 4` gate. -/
theorem homS_pos_of_four (h : 4 ≤ |Real.log M.gamma|) : 0 < homS M :=
  homS_pos (by linarith only [h])

/-- `√k ≤ 2|log γ|` under the `|log γ| ≥ 4` gate. -/
theorem sqrt_homK_le (h : 4 ≤ |Real.log M.gamma|) :
    Real.sqrt ((homK M : ℝ)) ≤ 2 * |Real.log M.gamma| := by
  have hk := homK_le M
  have hL : (0 : ℝ) < |Real.log M.gamma| := by linarith only [h]
  have hsq : (homK M : ℝ) ≤ (2 * |Real.log M.gamma|) ^ (2 : ℕ) := by
    have hgrow : 10 * |Real.log M.gamma| + 1 ≤ 4 * |Real.log M.gamma| ^ (2 : ℕ) := by
      have hstep : 16 * |Real.log M.gamma| ≤ 4 * |Real.log M.gamma| ^ (2 : ℕ) := by
        have := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 4 * |Real.log M.gamma|)
        calc 16 * |Real.log M.gamma| = (4 * |Real.log M.gamma|) * 4 := by ring
          _ ≤ (4 * |Real.log M.gamma|) * |Real.log M.gamma| := this
          _ = 4 * |Real.log M.gamma| ^ (2 : ℕ) := by ring
      linarith only [hstep, h]
    calc (homK M : ℝ) ≤ 10 * |Real.log M.gamma| + 1 := hk
      _ ≤ 4 * |Real.log M.gamma| ^ (2 : ℕ) := hgrow
      _ = (2 * |Real.log M.gamma|) ^ (2 : ℕ) := by ring
  have hnn : (0 : ℝ) ≤ 2 * |Real.log M.gamma| := by positivity
  calc Real.sqrt ((homK M : ℝ)) ≤ Real.sqrt ((2 * |Real.log M.gamma|) ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hsq
    _ = 2 * |Real.log M.gamma| := Real.sqrt_sq hnn

/-- The mesoscale-gap binder `m ≤ n + γ⁻¹` of the anchor, in the form
`k ≤ γ⁻¹`, under `t ≤ 1/16`. -/
theorem homK_le_inv_gamma (hg : 0 < M.gamma) (hg1 : M.gamma < 1)
    (ht : Real.sqrt (Real.sqrt M.gamma) ≤ 1 / 16) :
    (homK M : ℝ) ≤ M.gamma⁻¹ := by
  set t := Real.sqrt (Real.sqrt M.gamma) with htdef
  have htpos : 0 < t := quarticRoot_pos hg
  have htne : t ≠ 0 := ne_of_gt htpos
  have ht4 : t ^ (4 : ℕ) = M.gamma := quarticRoot_pow_four hg.le
  have hpow : (0 : ℝ) < t ^ (4 : ℕ) := pow_pos htpos 4
  have hL : |Real.log M.gamma| ≤ 4 * t⁻¹ := absLog_le_four_div_quarticRoot hg hg1
  have hk : (homK M : ℝ) ≤ 10 * |Real.log M.gamma| + 1 := homK_le M
  have hkt : (homK M : ℝ) ≤ 40 * t⁻¹ + 1 := by
    have h10 : 10 * |Real.log M.gamma| ≤ 10 * (4 * t⁻¹) :=
      mul_le_mul_of_nonneg_left hL (by norm_num)
    linarith only [hk, h10]
  /- `40 t³ + t⁴ ≤ 1` for `t ≤ 1/16` -/
  have ht3 : t ^ (3 : ℕ) ≤ (1 / 16 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ htpos.le ht 3
  have ht4' : t ^ (4 : ℕ) ≤ (1 / 16 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ htpos.le ht 4
  have hkey : 40 * t ^ (3 : ℕ) + t ^ (4 : ℕ) ≤ 1 := by
    have h1 : (40 : ℝ) * t ^ (3 : ℕ) ≤ 40 * (1 / 16 : ℝ) ^ (3 : ℕ) := by
      linarith only [ht3]
    have h2 : (1 / 16 : ℝ) ^ (3 : ℕ) = 1 / 4096 := by norm_num
    have h3 : (1 / 16 : ℝ) ^ (4 : ℕ) = 1 / 65536 := by norm_num
    rw [h2] at h1
    rw [h3] at ht4'
    linarith only [h1, ht4']
  have hexpand : (40 * t⁻¹ + 1) * t ^ (4 : ℕ) = 40 * t ^ (3 : ℕ) + t ^ (4 : ℕ) := by
    field_simp
  have hmul : (homK M : ℝ) * t ^ (4 : ℕ) ≤ (40 * t⁻¹ + 1) * t ^ (4 : ℕ) :=
    mul_le_mul_of_nonneg_right hkt hpow.le
  have hfinal : (homK M : ℝ) * t ^ (4 : ℕ) ≤ 1 := by
    rw [hexpand] at hmul
    linarith only [hmul, hkey]
  have hres : (homK M : ℝ) ≤ 1 / t ^ (4 : ℕ) := (le_div_iff₀ hpow).mpr hfinal
  rw [ht4, one_div] at hres
  exact hres

end Web

end

end Algsuperdiff.Section4.Provider.Homogenization
