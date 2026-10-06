/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ScaleSelection.ConsumedBodies

/-!
# High-contrast homogenization: Entry.Multiscale.ScaleSelection.ParameterArithmetic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Real arithmetic of the parameter choice

Group A of the printed proof (`p.scale.selection`): the elementary exponential and logarithm
inequalities behind the service
reduction, the membership and comparison facts for the bridge tolerance `√ε σ` and the
transport ratio `σ^{(1-γ)/8}`, the two length conditions satisfied by `selectionLength`,
the old-grid smallness that fixes `ε₁`, the scale separation, the choice of `ε₀`, and the
exhaustiveness of the five guarded alternatives.

Part of the proof of `p.scale.selection`.  Conventions of the group: `q = 𝒬(𝔪)` is
`Geometry.explicitRoundedGrid jStar m`; the printed data are `h = 2Q`, `c = c₀`,
`L(ε,σ) = selectionLength L₀ σ` and
`B₀(ε,σ) = max 1 (max (B₀^bridge (√ε σ) L) (2 C_tr (L+1)))`; `√ε` is the printed
`ε^{1/2}`; the source lower scale `e.source.lower.scale` is carried wherever
`j_*` appears with the law, and no integrability, finiteness or
measurability premise is added anywhere.  Unused hypothesis binders of a statement are
underscore-prefixed.

The declaration text of this file is the closed skeleton's, copied unchanged; only this
header, the imports and the namespace frame are new.
-/

open HCPolySupport.HighContrast (aspectRatio aspectRatio_nonneg)
open HCPolySupport.HighContrast (aspectRatio_nonneg)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ### Group A — real arithmetic of the parameter choice (`p.scale.selection`) -/

theorem exp_sub_one_le_two_mul (x : ℝ) (h0 : 0 ≤ x) (hx : x ≤ Real.log 2) :
    Real.exp x - 1 ≤ 2 * x := by
  have h_log_lt_one : Real.log 2 < 1 := by
    calc Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    _ < 1 := by norm_num
  have h_abs_x_le_one : |x| ≤ 1 := abs_le.mpr ⟨by linarith only [h0], by linarith only [hx, h_log_lt_one]⟩
  have h_abs_exp := Real.abs_exp_sub_one_le h_abs_x_le_one
  have h_exp_nonneg : 0 ≤ Real.exp x - 1 := by linarith only [h0, Real.add_one_le_exp x]
  rw [abs_of_nonneg h0, abs_of_nonneg h_exp_nonneg] at h_abs_exp
  exact h_abs_exp

/-- `p.scale.selection`: the service reduction `⅛e^x b + C(e^x−1) ≤ ¼b + 2Cx` for `0 ≤ x ≤ log 2`.
-/
theorem service_reduction (a b x C : ℝ) (hb : 0 ≤ b) (hC : 0 ≤ C) (h0 : 0 ≤ x)
    (hx : x ≤ Real.log 2) (h : a ≤ 1 / 8 * Real.exp x * b + C * (Real.exp x - 1)) :
    a ≤ 1 / 4 * b + 2 * C * x := by
  have h1 : Real.exp x ≤ 2 := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
    exact Real.exp_le_exp.mpr hx
  have h2 : Real.exp x - 1 ≤ 2 * x := by
    have hlog_le_one : Real.log 2 ≤ (1 : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at this ⊢
      exact this
    have hx1 : x ≤ 1 := le_trans hx hlog_le_one
    have habs : |x| ≤ 1 := abs_le.mpr ⟨by linarith only [h0], hx1⟩
    have hbnd := Real.exp_bound (x := x) habs (n := 2) (by norm_num)
    norm_num [Finset.sum_range_succ, h0] at hbnd
    have hupper : Real.exp x - (1 + x) ≤ x ^ 2 * (3 / 4 : ℝ) :=
      le_trans (le_abs_self _) hbnd
    have hx_sq : x ^ 2 ≤ x := by
      nlinarith only [mul_le_mul_of_nonneg_left hx1 h0]
    nlinarith only [hupper, hx_sq, h0]
  nlinarith only [h, mul_le_mul_of_nonneg_right h1 hb, mul_le_mul_of_nonneg_left h2 hC]

theorem ceil_mul_le_ceil_mul (B₀ B x : ℝ) (hB : B₀ ≤ B) (hx : 0 ≤ x) :
    ⌈B₀ * x⌉ ≤ ⌈B * x⌉ := by exact Int.ceil_le_ceil (mul_le_mul_of_nonneg_right hB hx)

theorem logb_two_add_aspectRatio_nonneg {d : ℕ} (E : BlockMat d) :
    0 ≤ Real.logb 3 (2 + aspectRatio E) := by exact Real.logb_nonneg (by norm_num : (1:ℝ) < 3) (by linarith only [aspectRatio_nonneg E])

theorem half_le_logb_two_add (Pi : ℝ) (hPi : 0 ≤ Pi) : 1 / 2 ≤ Real.logb 3 (2 + Pi) := by
  have h1 : 1 < (3 : ℝ) := by norm_num
  have h2 : 0 < 2 + Pi := by linarith only [hPi]
  rw [Real.le_logb_iff_rpow_le h1 h2]
  have : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← Real.sqrt_eq_rpow 3]
  linarith only [this, hPi]

theorem logb_two_mul_nonneg (K : ℝ) (hK : 1 < K) : 0 ≤ Real.logb 3 (2 * K) := by
  apply Real.logb_nonneg
  norm_num
  linarith only [hK]

theorem bridge_tolerance_mem (ε σ : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) :
    Real.sqrt ε * σ ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact mul_pos (Real.sqrt_pos.2 hε.1) hσ.1
  · exact (mul_le_of_le_one_left (le_of_lt hσ.1) (Real.sqrt_le_one.mpr hε.2)).trans (hσ.2.trans hε.2)

theorem bridge_tolerance_le_quarter (ε σ : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) (1 / 4))
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) : Real.sqrt ε * σ ∈ Set.Icc (0 : ℝ) (1 / 4) := by
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg ε) hσ.1.le
  · have h_sqrt : Real.sqrt ε ≤ 1 := by
      rw [Real.sqrt_le_one]
      linarith only [hε.2]
    have h_sigma : σ ≤ 1 / 4 := by
      linarith only [hσ.2, hε.2]
    have h_calc : Real.sqrt ε * σ ≤ 1 * (1 / 4) :=
      mul_le_mul h_sqrt h_sigma hσ.1.le zero_le_one
    linarith only [h_calc]

theorem transport_rho_mem (σ γ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    σ ^ ((1 - γ) / 8) ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact Real.rpow_pos_of_pos hσ.1 _
  · apply Real.rpow_le_one hσ.1.le hσ.2
    apply div_nonneg
    · exact sub_nonneg.mpr hγ.2.le
    · norm_num

/-- `p.scale.selection` defines `δ = ε^{1/2}σ` and `ρ = σ^{(1−γ)/8}`; `p.scale.selection` gives the
comparison `δ ≤ ρ`, for which `δ ≤ σ ≤ ρ` is the elementary justification. -/
theorem bridge_tolerance_le_rho (ε σ γ : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    Real.sqrt ε * σ ≤ σ ^ ((1 - γ) / 8) := by
  have h1 : √ε ≤ 1 := by rw [Real.sqrt_le_one]; exact hε.2
  have h2 : √ε * σ ≤ σ := mul_le_of_le_one_left hσ.1.le h1
  have h4 : σ ^ (1 : ℝ) ≤ σ ^ ((1 - γ) / 8) :=
    Real.rpow_le_rpow_of_exponent_ge hσ.1 (hσ.2.trans hε.2) (by linarith only [hγ.1])
  rw [Real.rpow_one] at h4
  exact le_trans h2 h4

theorem one_le_selectionLength (L₀ : ℕ) (hL₀ : 1 ≤ L₀) (σ : ℝ) : 1 ≤ selectionLength L₀ σ := by unfold selectionLength; omega

/-- `p.scale.selection`: the chosen length satisfies the short-bridge length condition at the
smaller tolerance `ε^{1/2}σ`. -/
theorem selectionLength_bridge_condition (L₀ : ℕ) (ε σ : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) :
    (L₀ : ℤ) + ⌈Real.logb 3 (Real.sqrt ε * σ)⁻¹⌉ ≤ (selectionLength L₀ σ : ℤ) := by
  have hεpos : 0 < ε := hε.1
  have hσpos : 0 < σ := hσ.1
  have hσε : σ ≤ ε := hσ.2
  have hsqrtpos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hεpos
  have h1 : (Real.sqrt ε * σ)⁻¹ = (Real.sqrt ε)⁻¹ * σ⁻¹ := mul_inv (Real.sqrt ε) σ
  have h2 : Real.logb 3 (Real.sqrt ε * σ)⁻¹
      = Real.logb 3 (Real.sqrt ε)⁻¹ + Real.logb 3 σ⁻¹ := by
    rw [h1, Real.logb_mul (inv_ne_zero hsqrtpos.ne') (inv_ne_zero hσpos.ne')]
  have h3 : Real.logb 3 (Real.sqrt ε)⁻¹ = - Real.logb 3 (Real.sqrt ε) :=
    Real.logb_inv 3 (Real.sqrt ε)
  have h4 : Real.logb 3 (Real.sqrt ε) = (1/2 : ℝ) * Real.logb 3 ε := by
    unfold Real.logb
    rw [Real.sqrt_eq_rpow, Real.log_rpow hεpos]
    ring
  have h5 : Real.logb 3 σ⁻¹ = - Real.logb 3 σ := Real.logb_inv 3 σ
  have hmono : Real.logb 3 σ ≤ Real.logb 3 ε :=
    (Real.logb_le_logb (by norm_num) hσpos hεpos).mpr hσε
  have hab : Real.logb 3 (Real.sqrt ε * σ)⁻¹ ≤ (3/2 : ℝ) * Real.logb 3 σ⁻¹ := by
    rw [h2, h3, h4, h5]
    linarith only [hmono]
  have hceil : ⌈Real.logb 3 (Real.sqrt ε * σ)⁻¹⌉
      ≤ ((⌈(3/2 : ℝ) * Real.logb 3 σ⁻¹⌉₊ : ℕ) : ℤ) := by
    rw [Int.ceil_le]
    push_cast
    exact le_trans hab (Nat.le_ceil _)
  unfold selectionLength
  push_cast
  linarith only [hceil]

/-- `p.scale.selection`: with `L₀ ≥ C`, the chosen length satisfies `L ≥ C + log₃(ρ⁻¹)` at
`ρ = σ^{(1−γ)/8}`. -/
theorem selectionLength_transport_condition (C : ℝ) (L₀ : ℕ) (hC : C ≤ L₀) (σ γ : ℝ)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    C + Real.logb 3 (σ ^ ((1 - γ) / 8))⁻¹ ≤ (selectionLength L₀ σ : ℝ) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  obtain ⟨hγ0, _hγ1⟩ := hγ
  have hinv : 1 ≤ σ⁻¹ := by
    have h1 : σ * σ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hσ0)
    have h2 : (0:ℝ) ≤ (1 - σ) * σ⁻¹ := mul_nonneg (by linarith only [hσ1]) (le_of_lt (inv_pos.mpr hσ0))
    nlinarith only [h1, h2]
  have hlog0 : 0 ≤ Real.logb 3 σ⁻¹ := Real.logb_nonneg (by norm_num) hinv
  have hα : (1 - γ) / 8 ≤ 3 / 2 := by linarith only [hγ0]
  have hlog : Real.logb 3 (σ ^ ((1 - γ) / 8))⁻¹ = (1 - γ) / 8 * Real.logb 3 σ⁻¹ := by
    rw [Real.logb_inv, Real.logb_rpow_eq_mul_logb_of_pos hσ0, Real.logb_inv]
    ring
  have hmul : (1 - γ) / 8 * Real.logb 3 σ⁻¹ ≤ 3 / 2 * Real.logb 3 σ⁻¹ :=
    mul_le_mul_of_nonneg_right hα hlog0
  have hceil : (3:ℝ) / 2 * Real.logb 3 σ⁻¹ ≤ (⌈(3:ℝ) / 2 * Real.logb 3 σ⁻¹⌉₊ : ℝ) :=
    Nat.le_ceil _
  rw [hlog]
  push_cast [selectionLength]
  linarith only [hC, hmul, hceil]

theorem selectionLength_le (L₀ : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) :
    (selectionLength L₀ σ : ℝ) ≤ (L₀ : ℝ) + 1 + 3 / 2 * Real.logb 3 σ⁻¹ := by
  obtain ⟨hσ_pos, hσ_le⟩ := hσ
  have h_one_le_inv : 1 ≤ σ⁻¹ := one_le_inv_iff₀.mpr ⟨hσ_pos, hσ_le⟩
  have h_logb_nonneg : 0 ≤ Real.logb 3 σ⁻¹ := Real.logb_nonneg (by norm_num : (1 : ℝ) < 3) h_one_le_inv
  have h_x_nonneg : 0 ≤ (3 : ℝ) / 2 * Real.logb 3 σ⁻¹ := mul_nonneg (by norm_num) h_logb_nonneg
  have h_ceil : (⌈(3 : ℝ) / 2 * Real.logb 3 σ⁻¹⌉₊ : ℝ) < (3 : ℝ) / 2 * Real.logb 3 σ⁻¹ + 1 :=
    Nat.ceil_lt_add_one h_x_nonneg
  have h_eq : (selectionLength L₀ σ : ℝ) = (L₀ : ℝ) + (⌈(3 : ℝ) / 2 * Real.logb 3 σ⁻¹⌉₊ : ℝ) := by
    unfold selectionLength; push_cast; ring
  rw [h_eq]
  linarith only [h_ceil]

/-- `p.scale.selection`: `σ^α log₃(σ⁻¹)` is bounded on `(0,1]` for `α > 0`. -/
theorem rpow_mul_logb_le (α σ : ℝ) (hα : 0 < α) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) :
    σ ^ α * Real.logb 3 σ⁻¹ ≤ 1 / (α * Real.log 3) := by
  obtain ⟨hσ0, _hσ1⟩ := hσ
  have hσpos : (0:ℝ) ≤ σ := hσ0.le
  have hσinv : (0:ℝ) ≤ σ⁻¹ := inv_nonneg.mpr hσpos
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hσα : 0 < σ ^ α := Real.rpow_pos_of_pos hσ0 α
  have h1 : Real.log σ⁻¹ ≤ (σ⁻¹) ^ α / α := Real.log_le_rpow_div hσinv hα
  rw [Real.inv_rpow hσpos] at h1
  have key : σ ^ α * Real.log σ⁻¹ ≤ 1 / α := by
    calc σ ^ α * Real.log σ⁻¹
        ≤ σ ^ α * ((σ ^ α)⁻¹ / α) := mul_le_mul_of_nonneg_left h1 hσα.le
      _ = 1 / α := by rw [← mul_div_assoc, mul_inv_cancel₀ hσα.ne']
  have final : σ ^ α * Real.log σ⁻¹ / Real.log 3 ≤ 1 / α / Real.log 3 := by
    have hh := mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hlog3.le)
    simpa [div_eq_mul_inv] using hh
  rw [div_div] at final
  show σ ^ α * (Real.log σ⁻¹ / Real.log 3) ≤ 1 / (α * Real.log 3)
  rw [← mul_div_assoc]
  exact final

/-- `p.scale.selection`: `3^{½(1−γ)L} ≤ 3^{½(1−γ)(L₀+1)} σ^{−¾(1−γ)}` for the chosen `L`. -/
theorem three_rpow_selectionLength_le (L₀ : ℕ) (σ γ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    (3 : ℝ) ^ (1 / 2 * (1 - γ) * (selectionLength L₀ σ : ℝ)) ≤
      (3 : ℝ) ^ (1 / 2 * (1 - γ) * ((L₀ : ℝ) + 1)) * σ ^ (-(3 / 4) * (1 - γ)) := by
  have hσ0 : 0 < σ := hσ.1
  have hγ1 : (0:ℝ) ≤ 1 - γ := by linarith only [hγ.2]
  have hL := selectionLength_le L₀ σ hσ
  have hexp : 1 / 2 * (1 - γ) * (selectionLength L₀ σ : ℝ) ≤
      1 / 2 * (1 - γ) * ((L₀ : ℝ) + 1) + 3 / 4 * (1 - γ) * Real.logb 3 σ⁻¹ := by
    nlinarith only [mul_le_mul_of_nonneg_left hL hγ1]
  have hstep : (3:ℝ) ^ (1 / 2 * (1 - γ) * (selectionLength L₀ σ : ℝ)) ≤
      (3:ℝ) ^ (1 / 2 * (1 - γ) * ((L₀ : ℝ) + 1) + 3 / 4 * (1 - γ) * Real.logb 3 σ⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hsplit : (3:ℝ) ^ (1 / 2 * (1 - γ) * ((L₀ : ℝ) + 1) + 3 / 4 * (1 - γ) * Real.logb 3 σ⁻¹) =
      (3:ℝ) ^ (1 / 2 * (1 - γ) * ((L₀ : ℝ) + 1)) * (3:ℝ) ^ (3 / 4 * (1 - γ) * Real.logb 3 σ⁻¹) :=
    Real.rpow_add (by norm_num) _ _
  have hkey : (3:ℝ) ^ (3 / 4 * (1 - γ) * Real.logb 3 σ⁻¹) = σ ^ (-(3 / 4) * (1 - γ)) := by
    rw [mul_comm (3 / 4 * (1 - γ)) (Real.logb 3 σ⁻¹),
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
        Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.mpr hσ0),
        Real.inv_rpow hσ0.le,
        show (-(3 / 4) * (1 - γ) : ℝ) = -(3 / 4 * (1 - γ)) from by ring,
        Real.rpow_neg hσ0.le]
  calc (3:ℝ) ^ (1 / 2 * (1 - γ) * (selectionLength L₀ σ : ℝ))
      ≤ (3:ℝ) ^ (1 / 2 * (1 - γ) * ((L₀ : ℝ) + 1) + 3 / 4 * (1 - γ) * Real.logb 3 σ⁻¹) := hstep
    _ = (3:ℝ) ^ (1 / 2 * (1 - γ) * ((L₀ : ℝ) + 1)) * (3:ℝ) ^ (3 / 4 * (1 - γ) * Real.logb 3 σ⁻¹) := hsplit
    _ = (3:ℝ) ^ (1 / 2 * (1 - γ) * ((L₀ : ℝ) + 1)) * σ ^ (-(3 / 4) * (1 - γ)) := by rw [hkey]

/-- `p.scale.selection`: the old-grid smallness is a smallness of `ε₀` alone. -/
theorem old_grid_smallness_arith (C' : ℝ) (hC' : 0 < C') (L₀ : ℕ) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧
      ∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) ε₁ → σ ∈ Set.Ioc (0 : ℝ) ε →
        C' * (1 + (selectionLength L₀ σ : ℝ)) * ε * σ ≤
          (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * (selectionLength L₀ σ : ℝ)) * σ ^ ((1 - γ) / 8) := by
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨β, hβpos, hβ⟩ : ∃ β : ℝ, 0 < β ∧ β = (1 + 7 * γ) / 8 := ⟨_, by linarith only [hγ0], rfl⟩
  obtain ⟨A, hApos, hA⟩ : ∃ A : ℝ, 0 < A ∧ A = (3 : ℝ) ^ (1 / 2 * (1 - γ) * ((L₀ : ℝ) + 1)) :=
    ⟨_, Real.rpow_pos_of_pos (by norm_num) _, rfl⟩
  obtain ⟨D, hDpos, hD⟩ : ∃ D : ℝ, 0 < D ∧ D = 1 / (β * Real.log 3) :=
    ⟨_, div_pos one_pos (mul_pos hβpos hlog3), rfl⟩
  have hL₀nn : (0 : ℝ) ≤ (L₀ : ℝ) := Nat.cast_nonneg _
  obtain ⟨M, hMpos, hM⟩ : ∃ M : ℝ, 0 < M ∧ M = C' * A * (((L₀ : ℝ) + 2) + 3 / 2 * D) :=
    ⟨_, mul_pos (mul_pos hC' hApos) (by linarith only [hL₀nn, hDpos]), rfl⟩
  have core : ∀ X Y T U V A' S : ℝ, 0 ≤ X * Y → 0 ≤ V → T * U ≤ A' → X * Y * A' ≤ 1 →
      S = Y * (U * V) → X * S * T ≤ V := by
    rintro X Y T U V A' S hXY hV hTU hkey rfl
    calc X * (Y * (U * V)) * T = X * Y * (T * U) * V := by ring
      _ ≤ X * Y * A' * V := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTU hXY) hV
      _ ≤ 1 * V := mul_le_mul_of_nonneg_right hkey hV
      _ = V := one_mul V
  refine ⟨min 1 (1 / M), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  rintro ε σ ⟨hε0, hεle⟩ ⟨hσ0, hσε⟩
  have hε1 : ε ≤ 1 := hεle.trans (min_le_left _ _)
  have hεM : ε ≤ 1 / M := hεle.trans (min_le_right _ _)
  have hσ1 : σ ≤ 1 := hσε.trans hε1
  have hβσpos : (0 : ℝ) < σ ^ β := Real.rpow_pos_of_pos hσ0 _
  have hUpos : (0 : ℝ) < σ ^ (3 / 4 * (1 - γ)) := Real.rpow_pos_of_pos hσ0 _
  have hVnn : (0 : ℝ) ≤ σ ^ ((1 - γ) / 8) := (Real.rpow_pos_of_pos hσ0 _).le
  have hTpos : (0 : ℝ) < (3 : ℝ) ^ (1 / 2 * (1 - γ) * (selectionLength L₀ σ : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  -- the σ-power bookkeeping
  have hdec : σ ^ β * (σ ^ (3 / 4 * (1 - γ)) * σ ^ ((1 - γ) / 8)) = σ := by
    rw [← Real.rpow_add hσ0, ← Real.rpow_add hσ0,
      show β + (3 / 4 * (1 - γ) + (1 - γ) / 8) = 1 from by rw [hβ]; ring, Real.rpow_one]
  -- `T · σ^{¾(1−γ)} ≤ A` from the sibling bound on `3^{½(1−γ)L}`
  have hA3 := three_rpow_selectionLength_le L₀ σ γ ⟨hσ0, hσ1⟩ ⟨hγ0, hγ1⟩
  rw [show (-(3 / 4) * (1 - γ) : ℝ) = -(3 / 4 * (1 - γ)) from by ring,
    Real.rpow_neg hσ0.le, ← hA] at hA3
  have hTU : (3 : ℝ) ^ (1 / 2 * (1 - γ) * (selectionLength L₀ σ : ℝ)) *
      σ ^ (3 / 4 * (1 - γ)) ≤ A := by
    have h := mul_le_mul_of_nonneg_right hA3 hUpos.le
    rwa [inv_mul_cancel_right₀ hUpos.ne'] at h
  -- `(1+L) σ^β` is bounded by a constant
  have hlogbnn : 0 ≤ Real.logb 3 σ⁻¹ :=
    Real.logb_nonneg (by norm_num) (one_le_inv_iff₀.mpr ⟨hσ0, hσ1⟩)
  have hLle : (selectionLength L₀ σ : ℝ) ≤ (L₀ : ℝ) + 1 + 3 / 2 * Real.logb 3 σ⁻¹ :=
    selectionLength_le L₀ σ ⟨hσ0, hσ1⟩
  have hmix : σ ^ β * Real.logb 3 σ⁻¹ ≤ D := by
    rw [hD]; exact rpow_mul_logb_le β σ hβpos ⟨hσ0, hσ1⟩
  have hσβ1 : σ ^ β ≤ 1 := Real.rpow_le_one hσ0.le hσ1 hβpos.le
  have key1 : (1 + (selectionLength L₀ σ : ℝ)) * σ ^ β ≤ ((L₀ : ℝ) + 2) + 3 / 2 * D := by
    have h1 : (1 + (selectionLength L₀ σ : ℝ)) * σ ^ β ≤
        ((L₀ : ℝ) + 2 + 3 / 2 * Real.logb 3 σ⁻¹) * σ ^ β :=
      mul_le_mul_of_nonneg_right (by linarith only [hLle]) hβσpos.le
    have h2 : ((L₀ : ℝ) + 2) * σ ^ β ≤ (L₀ : ℝ) + 2 :=
      mul_le_of_le_one_right (by linarith only [hL₀nn]) hσβ1
    nlinarith only [h1, h2, hmix]
  have hMε : M * ε ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hεM hMpos.le
    rwa [mul_one_div, div_self hMpos.ne'] at h
  have hkey : C' * (1 + (selectionLength L₀ σ : ℝ)) * ε * σ ^ β * A ≤ 1 := by
    have h1 : C' * A * ((1 + (selectionLength L₀ σ : ℝ)) * σ ^ β) ≤ M := by
      rw [hM]; exact mul_le_mul_of_nonneg_left key1 (mul_pos hC' hApos).le
    have h2 := mul_le_mul_of_nonneg_right h1 hε0.le
    calc C' * (1 + (selectionLength L₀ σ : ℝ)) * ε * σ ^ β * A
        = C' * A * ((1 + (selectionLength L₀ σ : ℝ)) * σ ^ β) * ε := by ring
      _ ≤ M * ε := h2
      _ ≤ 1 := hMε
  have hXY : 0 ≤ C' * (1 + (selectionLength L₀ σ : ℝ)) * ε * σ ^ β := by
    have hpos : (0 : ℝ) ≤ 1 + (selectionLength L₀ σ : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hC'.le hpos) hε0.le) hβσpos.le
  rw [show (-(1 / 2) * (1 - γ) * (selectionLength L₀ σ : ℝ))
      = -(1 / 2 * (1 - γ) * (selectionLength L₀ σ : ℝ)) from by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), inv_mul_eq_div, le_div_iff₀ hTpos]
  exact core (C' * (1 + (selectionLength L₀ σ : ℝ)) * ε) (σ ^ β)
    ((3 : ℝ) ^ (1 / 2 * (1 - γ) * (selectionLength L₀ σ : ℝ))) (σ ^ (3 / 4 * (1 - γ)))
    (σ ^ ((1 - γ) / 8)) A σ hXY hVnn hTU hkey hdec.symm

/-- `p.scale.selection`: the transport scale separation from the eccentricity input, `B ≥ 2C(L+1)`
and `L log 3 ≥ 2Cε`. -/
theorem scale_separation_arith (C ε L X Pi k n j B : ℝ) (hC : 0 < C) (hε : 0 < ε) (hL : 1 ≤ L)
    (hX : 1 ≤ X) (hPi : 0 ≤ Pi) (hkn : k ≤ n) (hB : 2 * C * (L + 1) ≤ B)
    (hLε : 2 * C * ε ≤ L * Real.log 3)
    (hecc : 1 / 2 * Real.log X ≤ ε / L * (k - j - (⌈B * Real.logb 3 (2 + Pi)⌉ : ℤ))) :
    C * (L + Real.logb 3 ((2 + Pi) * X)) ≤ n - j := by
  have hlog3pos : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hLpos : (0:ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have h2Pi_pos : (0:ℝ) < 2 + Pi := by linarith only [hPi]
  have hX_pos : (0:ℝ) < X := by linarith only [hX]
  have hmuleq : Real.logb 3 ((2 + Pi) * X) = Real.logb 3 (2 + Pi) + Real.logb 3 X :=
    Real.logb_mul h2Pi_pos.ne' hX_pos.ne'
  have hapos : (1:ℝ) / 2 ≤ Real.logb 3 (2 + Pi) :=
    half_le_logb_two_add (Pi := Pi) (hPi := hPi)
  set m : ℝ := (⌈B * Real.logb 3 (2 + Pi)⌉ : ℝ) with hm_def
  have hceil : B * Real.logb 3 (2 + Pi) ≤ m := by
    rw [hm_def]; exact Int.le_ceil _
  have ha_nn : (0:ℝ) ≤ Real.logb 3 (2 + Pi) := by linarith only [hapos]
  have hp1 : (0:ℝ) ≤ (B - 2 * C * (L + 1)) * Real.logb 3 (2 + Pi) :=
    mul_nonneg (by linarith only [hB]) ha_nn
  have hp2 : (0:ℝ) ≤ (C * L) * (2 * Real.logb 3 (2 + Pi) - 1) :=
    mul_nonneg (mul_nonneg hC.le (by linarith only [hL])) (by linarith only [hapos])
  have hp3 : (0:ℝ) ≤ C * Real.logb 3 (2 + Pi) := mul_nonneg hC.le ha_nn
  have hii : C * L + C * Real.logb 3 (2 + Pi) ≤ B * Real.logb 3 (2 + Pi) := by
    nlinarith only [hp1, hp2, hp3]
  have hlogXnn : (0:ℝ) ≤ Real.log X := Real.log_nonneg hX
  have hlogbXdef : Real.logb 3 X = Real.log X / Real.log 3 := rfl
  have hy_nn : (0:ℝ) ≤ Real.logb 3 X := by
    rw [hlogbXdef]; exact div_nonneg hlogXnn hlog3pos.le
  have hCL : C * (2 * ε) ≤ L * Real.log 3 := by nlinarith only [hLε]
  have hCdiv : C ≤ L * Real.log 3 / (2 * ε) :=
    (le_div_iff₀ (by positivity : (0:ℝ) < 2 * ε)).mpr hCL
  have hi0 : C * Real.logb 3 X ≤ (L * Real.log 3 / (2 * ε)) * Real.logb 3 X :=
    mul_le_mul_of_nonneg_right hCdiv hy_nn
  have hlogbmul : Real.logb 3 X * Real.log 3 = Real.log X := by
    rw [hlogbXdef]; field_simp [hlog3pos.ne']
  have heq2 : (L * Real.log 3 / (2 * ε)) * Real.logb 3 X = L / (2 * ε) * Real.log X := by
    rw [show (L * Real.log 3 / (2 * ε)) * Real.logb 3 X
        = L / (2 * ε) * (Real.logb 3 X * Real.log 3) by ring, hlogbmul]
  have hi : C * Real.logb 3 X ≤ L / (2 * ε) * Real.log X := by
    linarith only [hi0, heq2]
  have hmul : L / ε * (1 / 2 * Real.log X) ≤ L / ε * (ε / L * (k - j - m)) :=
    mul_le_mul_of_nonneg_left hecc (div_pos hLpos hε).le
  have hcancel : L / ε * (ε / L * (k - j - m)) = k - j - m := by
    field_simp [hLpos.ne', hε.ne']
  have heq3 : L / ε * (1 / 2 * Real.log X) = L / (2 * ε) * Real.log X := by ring
  have hstep : L / (2 * ε) * Real.log X ≤ k - j - m := by
    linarith only [hmul, hcancel, heq3]
  calc C * (L + Real.logb 3 ((2 + Pi) * X))
      = C * L + C * Real.logb 3 (2 + Pi) + C * Real.logb 3 X := by rw [hmuleq]; ring
    _ ≤ B * Real.logb 3 (2 + Pi) + L / (2 * ε) * Real.log X := by linarith only [hii, hi]
    _ ≤ m + (k - j - m) := by linarith only [hceil, hstep]
    _ = k - j := by ring
    _ ≤ n - j := by linarith only [hkn]

/-- `p.scale.selection`: the outer `ε₀(d,γ)`, chosen after `C`, `C_tr`, `c₀`, `L₀`
and the smallness threshold `ε₁`. -/
theorem exists_eps0 (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (C Ctr c₀ ε₁ : ℝ) (L₀ : ℕ) (hC : 0 < C) (hCtr : 0 < Ctr) (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hε₁ : 0 < ε₁) (hL₀ : 1 ≤ L₀) :
    ∃ ε₀ : ℝ, ε₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ ε₀ ≤ 1 / 4 ∧ ε₀ ≤ (c₀ / ((d : ℝ) + 1)) ^ 2 ∧
      (bigQ d γ : ℝ) * (d : ℝ) * ε₀ ≤ Real.log 2 ∧ C * ε₀ ^ ((1 - γ) / 8) ≤ 1 ∧ ε₀ ≤ ε₁ ∧
      2 * Ctr * ε₀ ≤ (L₀ : ℝ) * Real.log 3 := by
  have hQpos : 0 < (bigQ d γ : ℝ) := bigQ_real_pos d γ hγ
  have hdpos : 0 < (d : ℝ) := by
    have h : 0 < d := by omega
    exact_mod_cast h
  have hQd : 0 < (bigQ d γ : ℝ) * (d : ℝ) := mul_pos hQpos hdpos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1γ : 0 < 1 - γ := by linarith only [hγ.2]
  have h1γne : (1 - γ) ≠ 0 := ne_of_gt h1γ
  have hCne : C ≠ 0 := ne_of_gt hC
  have hCtr2 : 0 < 2 * Ctr := by linarith only [hCtr]
  have hCtr2ne : (2 * Ctr) ≠ 0 := ne_of_gt hCtr2
  have hd1pos : 0 < (d : ℝ) + 1 := by positivity
  have hcd : 0 < c₀ / ((d : ℝ) + 1) := div_pos hc₀.1 hd1pos
  have hCinv : 0 < 1 / C := div_pos (by norm_num) hC
  have hL₀pos : (0 : ℝ) < (L₀ : ℝ) := by
    have h : 0 < L₀ := by omega
    exact_mod_cast h
  have hApos : (0 : ℝ) < 1 / 4 := by norm_num
  have hBpos : (0 : ℝ) < (c₀ / ((d : ℝ) + 1)) ^ 2 := pow_pos hcd 2
  have hCcpos : (0 : ℝ) < Real.log 2 / ((bigQ d γ : ℝ) * (d : ℝ)) := div_pos hlog2 hQd
  have hDpos : (0 : ℝ) < (1 / C) ^ (8 / (1 - γ)) := Real.rpow_pos_of_pos hCinv _
  have hEpos : (0 : ℝ) < ε₁ := hε₁
  have hFpos : (0 : ℝ) < (L₀ : ℝ) * Real.log 3 / (2 * Ctr) := div_pos (mul_pos hL₀pos hlog3) hCtr2
  set e0 : ℝ :=
    min (min (min (1 / 4 : ℝ) ((c₀ / ((d : ℝ) + 1)) ^ 2))
        (min (Real.log 2 / ((bigQ d γ : ℝ) * (d : ℝ))) ((1 / C) ^ (8 / (1 - γ)))))
      (min ε₁ ((L₀ : ℝ) * Real.log 3 / (2 * Ctr))) with he0_def
  have he0pos : 0 < e0 := by
    rw [he0_def]
    exact lt_min (lt_min (lt_min hApos hBpos) (lt_min hCcpos hDpos)) (lt_min hEpos hFpos)
  have hleA : e0 ≤ 1 / 4 :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hleB : e0 ≤ (c₀ / ((d : ℝ) + 1)) ^ 2 :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hleCc : e0 ≤ Real.log 2 / ((bigQ d γ : ℝ) * (d : ℝ)) :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hleD : e0 ≤ (1 / C) ^ (8 / (1 - γ)) :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hleE : e0 ≤ ε₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hleF : e0 ≤ (L₀ : ℝ) * Real.log 3 / (2 * Ctr) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have he0lt1 : e0 < 1 := lt_of_le_of_lt hleA (by norm_num)
  have hCcEq : (bigQ d γ : ℝ) * (d : ℝ) * (Real.log 2 / ((bigQ d γ : ℝ) * (d : ℝ))) = Real.log 2 := by
    field_simp [hQd.ne']
  have h4 : (bigQ d γ : ℝ) * (d : ℝ) * e0 ≤ Real.log 2 := by
    have hstep := mul_le_mul_of_nonneg_left hleCc hQd.le
    rw [hCcEq] at hstep
    exact hstep
  have hexp : (8 / (1 - γ)) * ((1 - γ) / 8) = 1 := by
    rw [div_mul_div_comm, mul_comm (8 : ℝ) (1 - γ),
      div_self (mul_ne_zero h1γne (by norm_num : (8 : ℝ) ≠ 0))]
  have hDrpow : ((1 / C) ^ (8 / (1 - γ))) ^ ((1 - γ) / 8) = 1 / C := by
    rw [← Real.rpow_mul hCinv.le, hexp, Real.rpow_one]
  have h5rpow : e0 ^ ((1 - γ) / 8) ≤ 1 / C := by
    calc e0 ^ ((1 - γ) / 8) ≤ ((1 / C) ^ (8 / (1 - γ))) ^ ((1 - γ) / 8) :=
          Real.rpow_le_rpow he0pos.le hleD (div_nonneg h1γ.le (by norm_num))
      _ = 1 / C := hDrpow
  have h5 : C * e0 ^ ((1 - γ) / 8) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left h5rpow hC.le
    rw [mul_one_div, div_self hCne] at hh
    exact hh
  have hFeq : 2 * Ctr * ((L₀ : ℝ) * Real.log 3 / (2 * Ctr)) = (L₀ : ℝ) * Real.log 3 := by
    field_simp [hCtr2ne]
  have h7 : 2 * Ctr * e0 ≤ (L₀ : ℝ) * Real.log 3 := by
    have hh := mul_le_mul_of_nonneg_left hleF hCtr2.le
    rw [hFeq] at hh
    exact hh
  exact ⟨e0, ⟨he0pos, he0lt1⟩, hleA, hleB, h4, h5, hleE, h7⟩

/-- `p.scale.selection`: `𝒫+D+Δ ≤ (c+d)εσ ≤ c₀ ε^{1/2} σ` once `ε ≤ (c₀/(d+1))²`. -/
theorem bridge_smallness_arith (d : ℕ) (_hd : 2 ≤ d) (c c₀ ε σ a D Δ : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 < ε)
    (hεc : ε ≤ (c₀ / ((d : ℝ) + 1)) ^ 2) (hσ : 0 < σ) (hD : a + D ≤ c * ε * σ)
    (hΔ : (d : ℝ)⁻¹ * Δ ≤ ε * σ) : a + D + Δ ≤ c₀ * (Real.sqrt ε * σ) := by
  have hd_pos : (0:ℝ) < (d:ℝ) := by
    have h2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast _hd
    linarith only [h2]
  have hΔ' : Δ ≤ (d:ℝ) * (ε * σ) := (inv_mul_le_iff₀ hd_pos).mp hΔ
  have hc0_pos : (0:ℝ) < c₀ := hc₀.1
  have hc0d : (0:ℝ) < (d:ℝ) + 1 := by linarith only [hd_pos]
  have hsqrt_le : Real.sqrt ε ≤ c₀ / ((d:ℝ) + 1) :=
    (Real.sqrt_le_left (div_nonneg hc0_pos.le hc0d.le)).mpr hεc
  have hc0d_ne : ((d:ℝ) + 1) ≠ 0 := ne_of_gt hc0d
  have heq : (c₀ / ((d:ℝ) + 1)) * ((d:ℝ) + 1) = c₀ := by
    field_simp [hc0d_ne]
  have hstep : Real.sqrt ε * ((d:ℝ) + 1) ≤ c₀ := by
    have h := mul_le_mul_of_nonneg_right hsqrt_le hc0d.le
    linarith only [h, heq]
  have hkey : ((d:ℝ) + 1) * ε ≤ c₀ * Real.sqrt ε := by
    have heps : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
    nlinarith only [hstep, Real.sqrt_nonneg ε, heps]
  have hfact : (0:ℝ) ≤ (1 - c) * (ε * σ) :=
    mul_nonneg (by linarith only [hc.2]) (le_of_lt (mul_pos hε hσ))
  have hfinal : ((d:ℝ) + 1) * ε * σ ≤ c₀ * (Real.sqrt ε * σ) := by
    have h := mul_le_mul_of_nonneg_right hkey hσ.le
    nlinarith only [h, hσ.le]
  nlinarith only [hD, hΔ', hfact, hfinal]

/-- `p.scale.selection`: the bridge eccentricity from the input eccentricity, `2ε ≤ c₀`, `B ≥ B₀`.
-/
theorem bridge_eccentricity_arith (y ε c₀ L k j a B₀ B : ℝ) (hy : 0 ≤ y) (hε : 0 < ε)
    (h2ε : 2 * ε ≤ c₀) (hL : 0 < L) (ha : 0 ≤ a) (hB : B₀ ≤ B)
    (hecc : 1 / 2 * y ≤ ε / L * (k - j - (⌈B * a⌉ : ℤ))) :
    y ≤ c₀ / L * (k - j - (⌈B₀ * a⌉ : ℤ)) := by
  have hεL : 0 < ε / L := div_pos hε hL
  have hy2 : 0 ≤ 1 / 2 * y := by linarith only [hy]
  have hnonneg : 0 ≤ ε / L * (k - j - (⌈B * a⌉ : ℝ)) := le_trans hy2 hecc
  have hX' : 0 ≤ k - j - (⌈B * a⌉ : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hneg : ε / L * (k - j - (⌈B * a⌉ : ℝ)) < 0 := mul_neg_of_pos_of_neg hεL hcon
    linarith only [hnonneg, hneg]
  have hmul : B₀ * a ≤ B * a := mul_le_mul_of_nonneg_right hB ha
  have hceil : (⌈B₀ * a⌉ : ℤ) ≤ ⌈B * a⌉ :=
    Int.ceil_le.mpr (le_trans hmul (Int.le_ceil (B * a)))
  have hceil' : (⌈B₀ * a⌉ : ℝ) ≤ (⌈B * a⌉ : ℝ) := by exact_mod_cast hceil
  have hle : k - j - (⌈B * a⌉ : ℝ) ≤ k - j - (⌈B₀ * a⌉ : ℝ) := by linarith only [hceil']
  have hc0 : 0 ≤ c₀ / L := div_nonneg (by linarith only [hε, h2ε]) hL.le
  have step1 : y ≤ 2 * (ε / L * (k - j - (⌈B * a⌉ : ℝ))) := by linarith only [hecc]
  have step2 : 2 * (ε / L * (k - j - (⌈B * a⌉ : ℝ))) = (2 * ε) / L * (k - j - (⌈B * a⌉ : ℝ)) := by
    ring
  have step3 : (2 * ε) / L ≤ c₀ / L := div_le_div_of_nonneg_right h2ε hL.le
  have step4 : (2 * ε) / L * (k - j - (⌈B * a⌉ : ℝ)) ≤ c₀ / L * (k - j - (⌈B * a⌉ : ℝ)) :=
    mul_le_mul_of_nonneg_right step3 hX'
  have step5 : c₀ / L * (k - j - (⌈B * a⌉ : ℝ)) ≤ c₀ / L * (k - j - (⌈B₀ * a⌉ : ℝ)) :=
    mul_le_mul_of_nonneg_left hle hc0
  linarith only [step1, step2, step4, step5]

/-- `p.scale.selection`: the output eccentricity after a change of geometry. -/
theorem geometry_eccentricity_output_arith (y y' ε L k n j b : ℝ) (hy' : y' ≤ y + ε) (hε : 0 < ε)
    (hL : 1 ≤ L) (hkn : k ≤ n) (hecc : y ≤ ε / L * (k - j - b)) :
    y' ≤ ε / L * (n + L - j - b) := by
  have hεL : ε / L * L = ε := div_mul_cancel₀ ε (ne_of_gt (lt_of_lt_of_le zero_lt_one hL))
  have : 0 ≤ ε / L * (n - k) := mul_nonneg (by positivity) (by linarith only [hkn])
  nlinarith only [hy', hecc, this, hεL]

/-- `p.scale.selection`: the five guarded alternatives are exhaustive under `k ≤ n`. -/
theorem alternatives_exhaustive (k n : ℤ) (hkn : k ≤ n) (a η x σ y t : ℝ) :
    k = n ∨ (k < n ∧ a > η ∧ x ≤ σ) ∨ (k < n ∧ a ≤ η ∧ y ≤ t) ∨
      (k < n ∧ a > η ∧ x > σ) ∨ (k < n ∧ a ≤ η ∧ y > t) := by
  rcases Int.lt_or_eq_of_le hkn with hlt | heq
  · rcases le_or_gt a η with ha_le | ha_gt
    · rcases le_or_gt y t with hy_le | hy_gt
      · exact Or.inr (Or.inr (Or.inl ⟨hlt, ha_le, hy_le⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hlt, ha_le, hy_gt⟩)))
    · rcases le_or_gt x σ with hx_le | hx_gt
      · exact Or.inr (Or.inl ⟨hlt, ha_gt, hx_le⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hlt, ha_gt, hx_gt⟩)))
  · exact Or.inl heq

/-- `p.scale.selection`, in the combined form stated by `Selects`:
`𝒫+D+Δ ≤ (c+d)εσ ≤ c₀ ε^{1/2} σ` once `ε ≤ (c₀/(d+1))²`. -/
theorem bridge_smallness_arith_combined (d : ℕ) (hd : 2 ≤ d) (c c₀ ε σ A : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 < ε)
    (hεc : ε ≤ (c₀ / ((d : ℝ) + 1)) ^ 2) (hσ : 0 < σ)
    (hA : A ≤ (c + (d : ℝ)) * ε * σ) : A ≤ c₀ * (Real.sqrt ε * σ) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hc0d : (0 : ℝ) < (d : ℝ) + 1 := by linarith only [hdR]
  have hsqrt_le : Real.sqrt ε ≤ c₀ / ((d : ℝ) + 1) :=
    (Real.sqrt_le_left (div_nonneg hc₀.1.le hc0d.le)).mpr hεc
  have heq : c₀ / ((d : ℝ) + 1) * ((d : ℝ) + 1) = c₀ := by
    field_simp
  have hstep : Real.sqrt ε * ((d : ℝ) + 1) ≤ c₀ := by
    have h := mul_le_mul_of_nonneg_right hsqrt_le hc0d.le
    linarith only [h, heq]
  have hsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
  have hs0 : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have h1 : (c + (d : ℝ)) * Real.sqrt ε ≤ c₀ := by nlinarith only [hstep, hs0, hc.2]
  have hd0 : (0 : ℝ) ≤ Real.sqrt ε * σ := mul_nonneg hs0 hσ.le
  have h2 := mul_le_mul_of_nonneg_right h1 hd0
  have h3 : (c + (d : ℝ)) * Real.sqrt ε * (Real.sqrt ε * σ) = (c + (d : ℝ)) * ε * σ := by
    have hre : (c + (d : ℝ)) * Real.sqrt ε * (Real.sqrt ε * σ)
        = (c + (d : ℝ)) * (Real.sqrt ε * Real.sqrt ε) * σ := by ring
    rw [hre, hsq]
  linarith only [hA, h2, h3.le, h3.ge]

end

end HCPolySupport.HighContrast.Multiscale
