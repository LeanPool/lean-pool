/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.GeoMeanBlocks

/-!
# High-contrast homogenization: Entry.Multiscale.Global.ScalarLemmas

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scalar lemmas of the selection run

The real-arithmetic layer of the global selection argument `p.global.selection`: the
scaled-logarithm growth, contraction and span bounds (`e.global.selection.scalar.span`), the
comparison tolerance `ε` and comparison choice (`e.global.selection.comparison.choice`), the
weight choice, the eccentricity arithmetic (`e.global.selection.eccentricity`), and the scale
and containment arithmetic (`e.global.selection.lower.scale`) that fixes the outer constants
in the required order.
-/

open HCPolySupport.HighContrast (aspectRatio aspectRatio_nonneg bigLambdaRef lambdaRef specBound)
open HCPolySupport.HighContrast (aspectRatio_nonneg)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## §A Scalar lemmas (`p.global.selection`) -/

/-- `p.global.selection`, integrated: the scaled logarithm grows at most linearly in `y`. Proof
idea: with
`u = x/(8η)`, `w = exp (Q y)`, Bernoulli gives `1 + u w + (C/η)(w-1) ≤ (1+u) w^(1+C/η)`. -/
theorem scalar_growth_bound (η Q C x y : ℝ) (hη : η ∈ Set.Ioc (0 : ℝ) 1) (hC : 1 ≤ C)
    (hQ : 0 ≤ Q) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    η * Real.log (1 + η⁻¹ * (Real.exp (Q * y) * x / 8 + C * (Real.exp (Q * y) - 1))) ≤
      η * Real.log (1 + x / (8 * η)) + Q * (1 + C) * y := by
  obtain ⟨hη0, hη1⟩ := hη
  have hη_ne : η ≠ 0 := ne_of_gt hη0
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hQy : 0 ≤ Q * y := mul_nonneg hQ hy
  set w := Real.exp (Q * y) with hw_def
  have hw1 : 1 ≤ w := Real.one_le_exp hQy
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw1
  set u := x / (8 * η) with hu_def
  have hu0 : 0 ≤ u := by
    rw [hu_def]
    exact div_nonneg hx (mul_nonneg (by norm_num) hη0.le)
  have hCη : 1 ≤ C / η := by
    rw [div_eq_mul_inv]
    calc (1:ℝ) = η * η⁻¹ := (mul_inv_cancel₀ hη_ne).symm
      _ ≤ C * η⁻¹ := mul_le_mul_of_nonneg_right (by linarith only [hη1, hC]) (inv_nonneg.mpr hη0.le)
  have hCη0 : (0:ℝ) ≤ C / η := le_trans zero_le_one hCη
  have h1 : (0:ℝ) ≤ w - 1 := by linarith only [hw1]
  have hbern0 : 1 + (C / η) * (w - 1) ≤ (1 + (w - 1)) ^ (C / η) :=
    one_add_mul_self_le_rpow_one_add (by linarith only [h1]) hCη
  have heqw : (1:ℝ) + (w - 1) = w := by ring
  rw [heqw] at hbern0
  have hstep1 : (1 + u) * w * (1 + (C / η) * (w - 1)) ≤ (1 + u) * w * w ^ (C / η) :=
    mul_le_mul_of_nonneg_left hbern0 (mul_nonneg (by linarith only [hu0] : (0:ℝ) ≤ 1 + u) hw0.le)
  have hkey0 : 1 + (u * w + (C / η) * (w - 1)) ≤ (1 + u) * (w * w ^ (C / η)) := by
    nlinarith only [hstep1, h1, hCη0, hu0, hw1, hw0,
      mul_nonneg (mul_nonneg hCη0 h1) h1,
      mul_nonneg (mul_nonneg hCη0 h1) (mul_nonneg hu0 hw0.le)]
  have hpow : w ^ ((1:ℝ) + C / η) = w * w ^ (C / η) := by
    rw [Real.rpow_add hw0, Real.rpow_one]
  have hexpand : η⁻¹ * (w * x / 8 + C * (w - 1)) = u * w + (C / η) * (w - 1) := by
    rw [hu_def]
    ring
  have hterm1 : (0:ℝ) ≤ w * x / 8 := by
    apply div_nonneg (mul_nonneg hw0.le hx)
    norm_num
  have hterm2 : (0:ℝ) ≤ C * (w - 1) := mul_nonneg hC0 h1
  have hA_nonneg : (0:ℝ) ≤ η⁻¹ * (w * x / 8 + C * (w - 1)) :=
    mul_nonneg (inv_nonneg.mpr hη0.le) (by linarith only [hterm1, hterm2])
  have hA_pos : (0:ℝ) < 1 + η⁻¹ * (w * x / 8 + C * (w - 1)) := by linarith only [hA_nonneg]
  have h1u_pos : (0:ℝ) < 1 + u := by linarith only [hu0]
  have hwp_pos : (0:ℝ) < w ^ ((1:ℝ) + C / η) := Real.rpow_pos_of_pos hw0 _
  have hkey : 1 + η⁻¹ * (w * x / 8 + C * (w - 1)) ≤ (1 + u) * w ^ ((1:ℝ) + C / η) := by
    rw [hpow, hexpand]
    exact hkey0
  have hlogAB : Real.log (1 + η⁻¹ * (w * x / 8 + C * (w - 1))) ≤
      Real.log ((1 + u) * w ^ ((1:ℝ) + C / η)) := Real.log_le_log hA_pos hkey
  have hlogw : Real.log w = Q * y := by
    rw [hw_def]
    exact Real.log_exp (Q * y)
  have hlogRHS : Real.log ((1 + u) * w ^ ((1:ℝ) + C / η)) =
      Real.log (1 + u) + (1 + C / η) * (Q * y) := by
    rw [Real.log_mul (ne_of_gt h1u_pos) (ne_of_gt hwp_pos), Real.log_rpow hw0, hlogw]
  have h1' : η * Real.log (1 + η⁻¹ * (w * x / 8 + C * (w - 1))) ≤
      η * Real.log ((1 + u) * w ^ ((1:ℝ) + C / η)) :=
    mul_le_mul_of_nonneg_left hlogAB hη0.le
  rw [hlogRHS] at h1'
  have hηC : η * (C / η) = C := by
    rw [div_eq_mul_inv, ← mul_assoc, mul_comm η C, mul_assoc, mul_inv_cancel₀ hη_ne, mul_one]
  have hη1C : η * (1 + C / η) = η + C := by
    rw [mul_add, mul_one, hηC]
  have hexpand2 : η * (Real.log (1 + u) + (1 + C / η) * (Q * y)) =
      η * Real.log (1 + u) + (η + C) * (Q * y) := by
    rw [mul_add, ← mul_assoc, hη1C]
  rw [hexpand2] at h1'
  have hfin2 : (η + C) * (Q * y) ≤ Q * (1 + C) * y := by
    have heq : Q * (1 + C) * y = (1 + C) * (Q * y) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (by linarith only [hη1]) hQy
  linarith only [h1', hfin2]

/-- `p.global.selection`: for `x > η`, `η log(1 + x/(8η)) ≤ η log(1 + x/η) - η log(16/9)`. -/
theorem scalar_contraction (η x : ℝ) (hη : 0 < η) (hx : η < x) :
    η * Real.log (1 + x / (8 * η)) ≤ η * Real.log (1 + x / η) - η * Real.log (16 / 9) := by
  have hη' : η ≠ 0 := ne_of_gt hη
  have hx0 : 0 < x := lt_trans hη hx
  have h1 : (0:ℝ) < 1 + x / (8 * η) := by positivity
  have hxa : x / (8 * η) = (x / η) / 8 := by
    rw [div_div, mul_comm η 8]
  have h2 : (1:ℝ) + x / (8 * η) ≤ (1 + x / η) * (9 / 16) := by
    rw [hxa]
    have hxη : 1 < x / η := by
      rw [lt_div_iff₀ hη]
      linarith only [hx]
    nlinarith only [hxη]
  have h3 : Real.log (1 + x / (8 * η)) ≤ Real.log ((1 + x / η) * (9 / 16)) :=
    Real.log_le_log h1 h2
  have h4 : Real.log ((1 + x / η) * (9 / 16)) = Real.log (1 + x / η) - Real.log (16 / 9) := by
    have hpos : (1 + x / η : ℝ) ≠ 0 := by positivity
    rw [Real.log_mul hpos (by norm_num : (9 / 16 : ℝ) ≠ 0)]
    have hlog916 : Real.log (9 / 16 : ℝ) = -Real.log (16 / 9 : ℝ) := by
      rw [show (9 / 16 : ℝ) = (16 / 9 : ℝ)⁻¹ from by norm_num, Real.log_inv]
    rw [hlog916]
    ring
  calc η * Real.log (1 + x / (8 * η))
      ≤ η * Real.log ((1 + x / η) * (9 / 16)) := mul_le_mul_of_nonneg_left h3 hη.le
    _ = η * (Real.log (1 + x / η) - Real.log (16 / 9)) := by rw [h4]
    _ = η * Real.log (1 + x / η) - η * Real.log (16 / 9) := by ring

/-- `e.global.selection.scalar.span`. Proof idea: `x' ≤ C ℓ exp (Q y)`, then
`(1 + Cℓ/η)^η ≤ 1 + Cℓ` by Bernoulli with exponent `η ≤ 1`. -/
theorem scalar_span (η Q C ℓ x x' y : ℝ) (hη : η ∈ Set.Ioc (0 : ℝ) 1) (hC : 0 ≤ C) (hℓ : 1 ≤ ℓ)
    (hQ : 0 ≤ Q) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hx'0 : 0 ≤ x')
    (hx' : x' ≤ C * ℓ * (x + (Real.exp (Q * y) - 1))) :
    η * Real.log (1 + x' / η) ≤ Real.log (1 + C * ℓ) + Q * y := by
  obtain ⟨hη0, hη1⟩ := hη
  have hℓ0 : (0:ℝ) ≤ ℓ := le_trans zero_le_one hℓ
  have hCℓ0 : 0 ≤ C * ℓ := mul_nonneg hC hℓ0
  have hηne : η ≠ 0 := hη0.ne'
  have hx_mem : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx0, hx1⟩
  have hx1' : x ≤ 1 := hx_mem.2
  have h1 : x' ≤ C * ℓ * Real.exp (Q * y) := by
    calc x' ≤ C * ℓ * (x + (Real.exp (Q * y) - 1)) := hx'
      _ ≤ C * ℓ * (1 + (Real.exp (Q * y) - 1)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hx1']) hCℓ0
      _ = C * ℓ * Real.exp (Q * y) := by ring
  have h2 : x' / η ≤ C * ℓ / η * Real.exp (Q * y) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hu0 : (0:ℝ) ≤ η⁻¹ := inv_nonneg.mpr hη0.le
    calc x' * η⁻¹ ≤ (C * ℓ * Real.exp (Q * y)) * η⁻¹ :=
          mul_le_mul_of_nonneg_right h1 hu0
      _ = C * ℓ * η⁻¹ * Real.exp (Q * y) := by ring
  have hexp1 : (1:ℝ) ≤ Real.exp (Q * y) := by
    have hQy : 0 ≤ Q * y := mul_nonneg hQ hy
    calc (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (Q * y) := Real.exp_le_exp.mpr hQy
  have h3 : 1 + x' / η ≤ (1 + C * ℓ / η) * Real.exp (Q * y) := by
    have expand : (1 + C * ℓ / η) * Real.exp (Q * y)
        = Real.exp (Q * y) + C * ℓ / η * Real.exp (Q * y) := by ring
    rw [expand]
    linarith only [h2, hexp1]
  have hpos1 : (0:ℝ) < 1 + x' / η := by
    have hdiv : 0 ≤ x' / η := div_nonneg hx'0 hη0.le
    linarith only [hdiv]
  have hCℓη0 : (0:ℝ) ≤ C * ℓ / η := div_nonneg hCℓ0 hη0.le
  have hpos2 : (0:ℝ) < 1 + C * ℓ / η := by linarith only [hCℓη0]
  have h4 : Real.log (1 + x' / η) ≤ Real.log ((1 + C * ℓ / η) * Real.exp (Q * y)) :=
    Real.log_le_log hpos1 h3
  have hlogmul : Real.log ((1 + C * ℓ / η) * Real.exp (Q * y))
      = Real.log (1 + C * ℓ / η) + Q * y := by
    rw [Real.log_mul hpos2.ne' (Real.exp_ne_zero _), Real.log_exp]
  rw [hlogmul] at h4
  have h5 : η * Real.log (1 + x' / η) ≤ η * (Real.log (1 + C * ℓ / η) + Q * y) :=
    mul_le_mul_of_nonneg_left h4 hη0.le
  have hs : (-1:ℝ) ≤ C * ℓ / η := by linarith only [hCℓη0]
  have hbernoulli : (1 + C * ℓ / η) ^ η ≤ 1 + η * (C * ℓ / η) :=
    rpow_one_add_le_one_add_mul_self hs hη0.le hη1
  have heq : η * (C * ℓ / η) = C * ℓ := by field_simp
  rw [heq] at hbernoulli
  have h6 : Real.log ((1 + C * ℓ / η) ^ η) ≤ Real.log (1 + C * ℓ) :=
    Real.log_le_log (Real.rpow_pos_of_pos hpos2 η) hbernoulli
  have hrpowlog : Real.log ((1 + C * ℓ / η) ^ η) = η * Real.log (1 + C * ℓ / η) :=
    Real.log_rpow hpos2 η
  rw [hrpowlog] at h6
  have h7 : η * (Q * y) ≤ Q * y := by
    have hQy0 : 0 ≤ Q * y := mul_nonneg hQ hy
    nlinarith only [hQy0, hη1]
  have hexpand5 : η * (Real.log (1 + C * ℓ / η) + Q * y)
      = η * Real.log (1 + C * ℓ / η) + η * (Q * y) := by ring
  rw [hexpand5] at h5
  linarith only [h5, h6, h7]

/-- `e.global.selection.comparison.choice`: `ε ∈ (0, ε₀]` depending only on `C, h`
such that, with `δ = √ε σ`, the comparison terms are below `min {ε/2, Cσ/4}` for every
`σ ∈ (0, ε]`. Proof idea: `δ ≤ ε^(3/2) ≤ 1/2`, `½ log((1+δ)/(1-δ)) ≤ 2δ`, `log(1+δ) ≤ δ`. -/
theorem comparison_choice (C : ℝ) (hC : 1 ≤ C) (h : ℕ) (ε₀ : ℝ) (hε₀ : ε₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) ε₀ ∧ ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
      1 / 2 * Real.log ((1 + Real.sqrt ε * σ) / (1 - Real.sqrt ε * σ)) +
          2 * C * ((h : ℝ) + 2) * Real.log (1 + Real.sqrt ε * σ) ≤
        min (ε / 2) (C * σ / 4) := by
  obtain ⟨hε₀0, hε₀1⟩ := hε₀
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  set Mc : ℝ := 2 + 2 * C * ((h : ℝ) + 2) with hMc
  have hMc2 : (2 : ℝ) ≤ Mc := by
    rw [hMc]
    nlinarith only [hMc, mul_nonneg hC0.le (by linarith only [hh0] : (0 : ℝ) ≤ (h : ℝ) + 2)]
  have hMc0 : (0 : ℝ) < Mc := by linarith only [hMc2]
  set ec : ℝ := min ε₀ ((1 / (4 * Mc)) ^ 2) with hec
  have hecpos : 0 < ec := lt_min hε₀0 (by positivity)
  have hecle : ec ≤ ε₀ := min_le_left _ _
  have hecsq : ec ≤ (1 / (4 * Mc)) ^ 2 := min_le_right _ _
  have hsqrt : Real.sqrt ec ≤ 1 / (4 * Mc) := by
    have h1 : Real.sqrt ec ≤ Real.sqrt ((1 / (4 * Mc)) ^ 2) := Real.sqrt_le_sqrt hecsq
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hsqrt0 : 0 < Real.sqrt ec := Real.sqrt_pos.mpr hecpos
  have hMs : Mc * Real.sqrt ec ≤ 1 / 4 := by
    have h2 : Real.sqrt ec * (4 * Mc) ≤ 1 / (4 * Mc) * (4 * Mc) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    have h3 : 1 / (4 * Mc) * (4 * Mc) = 1 := by field_simp
    rw [h3] at h2
    linarith only [h2]
  refine ⟨ec, ⟨hecpos, hecle⟩, ?_⟩
  rintro σ ⟨hσ0, hσe⟩
  set dl : ℝ := Real.sqrt ec * σ with hdl
  have hdl0 : 0 < dl := by rw [hdl]; exact mul_pos hsqrt0 hσ0
  have hb1 : Mc * dl ≤ σ / 4 := by
    rw [hdl, ← mul_assoc]
    linarith only [mul_le_mul_of_nonneg_right hMs hσ0.le]
  have hb2 : Mc * dl ≤ ec / 4 := by linarith only [hb1, hσe]
  have h2dl : 2 * dl ≤ Mc * dl := by
    nlinarith only [mul_nonneg (by linarith only [hMc2] : (0 : ℝ) ≤ Mc - 2) hdl0.le]
  have hdlhalf : dl ≤ 1 / 2 := by linarith only [h2dl, hb2, hecle, hε₀1]
  have h1p : (0 : ℝ) < 1 + dl := by linarith only [hdl0]
  have h1m : (0 : ℝ) < 1 - dl := by linarith only [hdlhalf]
  have hlog1 : Real.log (1 + dl) ≤ dl := by
    have h4 := Real.log_le_sub_one_of_pos h1p
    linarith only [h4]
  have hprod : (1 : ℝ) ≤ (1 - dl) * (1 + 2 * dl) := by
    nlinarith only [mul_nonneg hdl0.le (by linarith only [hdlhalf] : (0 : ℝ) ≤ 1 - 2 * dl)]
  have hkey : (1 - dl)⁻¹ ≤ 1 + 2 * dl := by
    have hinv0 : (0 : ℝ) ≤ (1 - dl)⁻¹ := le_of_lt (inv_pos.mpr h1m)
    have h5 := mul_le_mul_of_nonneg_left hprod hinv0
    rw [show (1 - dl)⁻¹ * ((1 - dl) * (1 + 2 * dl)) = 1 + 2 * dl by
      field_simp] at h5
    simpa using h5
  have hlog2 : -Real.log (1 - dl) ≤ 2 * dl := by
    have h6 : Real.log ((1 - dl)⁻¹) ≤ (1 - dl)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr h1m)
    rw [Real.log_inv] at h6
    linarith only [h6, hkey]
  have hcoef : (0 : ℝ) ≤ 2 * C * ((h : ℝ) + 2) := by positivity
  have hterm2 : 2 * C * ((h : ℝ) + 2) * Real.log (1 + dl) ≤ 2 * C * ((h : ℝ) + 2) * dl :=
    mul_le_mul_of_nonneg_left hlog1 hcoef
  have hLHS : 1 / 2 * Real.log ((1 + dl) / (1 - dl)) +
      2 * C * ((h : ℝ) + 2) * Real.log (1 + dl) ≤ Mc * dl := by
    rw [Real.log_div h1p.ne' h1m.ne', hMc]
    linarith only [hlog1, hlog2, hterm2, hdl0]
  apply le_min
  · linarith only [hdl, hLHS, hb2, hecpos.le]
  · nlinarith only [hdl, hLHS, hb1, mul_nonneg (by linarith only [hC] : (0 : ℝ) ≤ C - 1) hσ0.le]

/-- `e.global.selection.weight.choice`: the weight `a ≥ 1` exists (Archimedean). -/
theorem weight_choice (d : ℕ) (hd : 0 < d) (C Q ε σ c L H h : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (hσ : 0 < σ) :
    ∃ a : ℝ, 1 ≤ a ∧ 4 * Q * max 1 C ≤ a * C / d ∧
      Real.log (1 + C * h) + c ≤ a * ε / 2 ∧
      4 * (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) ≤ a * C * ε * σ := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h_cεσ : 0 < C * ε * σ := by positivity
  let a := max 1 (max (4 * Q * max 1 C * d / C)
    (max (2 * (Real.log (1 + C * h) + c) / ε)
      (4 * (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) / (C * ε * σ))))
  use a
  refine ⟨le_max_left 1 _, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hd']
    have ha1 : 4 * Q * max 1 C * d / C ≤ a := by
      calc 4 * Q * max 1 C * d / C
          ≤ max (4 * Q * max 1 C * d / C) (max (2 * (Real.log (1 + C * h) + c) / ε) (4 *
            (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) / (C * ε * σ))) := le_max_left _ _
        _ ≤ a := le_max_right 1 _
    calc 4 * Q * max 1 C * d
        = (4 * Q * max 1 C * d / C) * C := by field_simp [ne_of_gt hC]
      _ ≤ a * C := mul_le_mul_of_nonneg_right ha1 (le_of_lt hC)
  · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have ha2 : 2 * (Real.log (1 + C * h) + c) / ε ≤ a := by
      calc 2 * (Real.log (1 + C * h) + c) / ε
          ≤ max (2 * (Real.log (1 + C * h) + c) / ε) (4 * (Real.log (1 + 2 * C * L) + Real.log
            (1 + C * H) + c) / (C * ε * σ)) := le_max_left _ _
        _ ≤ max (4 * Q * max 1 C * d / C) (max (2 * (Real.log (1 + C * h) + c) / ε) (4 *
          (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) / (C * ε * σ))) := le_max_right _ _
        _ ≤ a := le_max_right 1 _
    calc (Real.log (1 + C * h) + c) * 2
        = 2 * (Real.log (1 + C * h) + c) := by ring
      _ = (2 * (Real.log (1 + C * h) + c) / ε) * ε := by field_simp [ne_of_gt hε]
      _ ≤ a * ε := mul_le_mul_of_nonneg_right ha2 (le_of_lt hε)
  · have ha3 : 4 * (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) / (C * ε * σ) ≤ a := by
      calc 4 * (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) / (C * ε * σ)
          ≤ max (2 * (Real.log (1 + C * h) + c) / ε) (4 * (Real.log (1 + 2 * C * L) + Real.log
            (1 + C * H) + c) / (C * ε * σ)) := le_max_right _ _
        _ ≤ max (4 * Q * max 1 C * d / C) (max (2 * (Real.log (1 + C * h) + c) / ε) (4 *
          (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) / (C * ε * σ))) := le_max_right _ _
        _ ≤ a := le_max_right 1 _
    calc 4 * (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c)
        = (4 * (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) / (C * ε * σ)) * (C * ε *
          σ) := by field_simp [ne_of_gt hC, ne_of_gt hε, ne_of_gt hσ]
      _ ≤ a * (C * ε * σ) := mul_le_mul_of_nonneg_right ha3 (le_of_lt h_cεσ)
      _ = a * C * ε * σ := by ring

/-- `p.global.selection`: `exp(Q d σ) - 1 ≤ Q d exp(Q d) σ^((1-γ)/8)` for `σ ∈ (0,1]`, the
constant free of
`σ`. Proof idea: `exp t - 1 ≤ t exp t` for `t ≥ 0`, and `σ ≤ σ^((1-γ)/8)` since `σ ≤ 1`. -/
theorem exp_sub_one_le_rpow (Q d σ γ : ℝ) (hQ : 0 ≤ Q) (hd : 0 ≤ d) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    Real.exp (Q * d * σ) - 1 ≤ Q * d * Real.exp (Q * d) * σ ^ ((1 - γ) / 8) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hQd0 : 0 ≤ Q * d := mul_nonneg hQ hd
  have ht0 : 0 ≤ Q * d * σ := mul_nonneg hQd0 hσ0.le
  have hexp_le : Real.exp (Q * d * σ) - 1 ≤ (Q * d * σ) * Real.exp (Q * d * σ) := by
    have h1 : -(Q * d * σ) + 1 ≤ Real.exp (-(Q * d * σ)) := Real.add_one_le_exp (-(Q * d * σ))
    have h2 : Real.exp (-(Q * d * σ)) * Real.exp (Q * d * σ) = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 : (-(Q * d * σ) + 1) * Real.exp (Q * d * σ) ≤ 1 := by
      calc (-(Q * d * σ) + 1) * Real.exp (Q * d * σ)
          ≤ Real.exp (-(Q * d * σ)) * Real.exp (Q * d * σ) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos (Q * d * σ)).le
        _ = 1 := h2
    nlinarith only [h3]
  have hexp_mono : Real.exp (Q * d * σ) ≤ Real.exp (Q * d) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hσ1 hQd0
    simpa using h
  have hσ_rpow : σ ≤ σ ^ ((1 - γ) / 8) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (show (1 - γ) / 8 ≤ 1 by linarith only [hγ0])
    rwa [Real.rpow_one] at h
  have hfactor_nonneg : 0 ≤ Q * d * Real.exp (Q * d) := by positivity
  calc Real.exp (Q * d * σ) - 1
      ≤ (Q * d * σ) * Real.exp (Q * d * σ) := hexp_le
    _ ≤ (Q * d * σ) * Real.exp (Q * d) := mul_le_mul_of_nonneg_left hexp_mono ht0
    _ = Q * d * Real.exp (Q * d) * σ := by ring
    _ ≤ Q * d * Real.exp (Q * d) * σ ^ ((1 - γ) / 8) :=
        mul_le_mul_of_nonneg_left hσ_rpow hfactor_nonneg

/-- The bundled lower bound `e.global.selection.lower.scale` implies every weaker source
threshold. -/
theorem source_threshold_mono (x y C C' : ℝ) (j : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hCC : C' ≤ C)
    (hj : ⌈y + C * x⌉ ≤ j) : ⌈C' * x⌉ ≤ j := by
  have h1 : C' * x ≤ C * x := mul_le_mul_of_nonneg_right hCC hx
  have h2 : C' * x ≤ y + C * x := by linarith only [h1, hy]
  exact le_trans (Int.ceil_le_ceil h2) hj

/-- `p.global.selection` arithmetic of `e.global.selection.eccentricity`: after at most `⌈C₁
log₃(2+Π)⌉ + 1`
projective steps of size `ε`, `exp (ε (J+1)) ≤ (2+Π)^C` with `C = C(ε, C₁)` free of `Π`. -/
theorem eccentricity_arith (ε C₁ : ℝ) (hε : 0 < ε) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ AR : ℝ, 0 ≤ AR →
      Real.exp (ε * ((⌈C₁ * Real.logb 3 (2 + AR)⌉ : ℤ) + 1)) ≤ (2 + AR) ^ C := by
  refine ⟨ε * (C₁ / Real.log 3 + 2 / Real.log 2), ?_, ?_⟩
  · have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : 0 ≤ C₁ / Real.log 3 := div_nonneg hC₁ hl3.le
    have h2 : 0 < 2 / Real.log 2 := div_pos (by norm_num) hl2
    have hsum : 0 < C₁ / Real.log 3 + 2 / Real.log 2 := by linarith only [h1, h2]
    exact mul_pos hε hsum
  · intro AR hAR
    have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2AR : (0:ℝ) < 2 + AR := by linarith only [hAR]
    have hlog2le : Real.log 2 ≤ Real.log (2 + AR) := Real.log_le_log (by norm_num) (by linarith
      only [hAR])
    have hxl2 : (2:ℝ) ≤ 2 * Real.log (2 + AR) / Real.log 2 := by
      rw [le_div_iff₀ hl2]
      linarith only [hlog2le]
    have hkey : (↑⌈C₁ * Real.logb 3 (2 + AR)⌉ : ℝ) + 1 ≤
        Real.log (2 + AR) * (C₁ / Real.log 3 + 2 / Real.log 2) := by
      have hceil := Int.ceil_lt_add_one (C₁ * Real.logb 3 (2 + AR))
      have ha : C₁ * Real.logb 3 (2 + AR) = C₁ * (Real.log (2 + AR) / Real.log 3) := by
        rw [Real.log_div_log]
      have expand : Real.log (2 + AR) * (C₁ / Real.log 3 + 2 / Real.log 2)
          = C₁ * (Real.log (2 + AR) / Real.log 3) + 2 * Real.log (2 + AR) / Real.log 2 := by
        ring
      rw [expand]
      linarith only [hceil, ha, hxl2]
    have hmul := mul_le_mul_of_nonneg_left hkey hε.le
    rw [Real.rpow_def_of_pos h2AR, Real.exp_le_exp]
    calc ε * ((↑⌈C₁ * Real.logb 3 (2 + AR)⌉ : ℝ) + 1)
        ≤ ε * (Real.log (2 + AR) * (C₁ / Real.log 3 + 2 / Real.log 2)) := hmul
      _ = Real.log (2 + AR) * (ε * (C₁ / Real.log 3 + 2 / Real.log 2)) := by ring

/-- `p.global.selection`-`p.global.selection` arithmetic of `e.global.selection.scales`: the entry
generation plus
`J + 2` steps of length `≤ 2L + H + h` plus the final `L + H` fit under `⌈(B + C) log₃(2+Π)⌉`. -/
theorem scales_arith (Cinit C₁ L H h : ℝ) (hCi : 0 ≤ Cinit) (hC₁ : 0 ≤ C₁) (hL : 0 ≤ L)
    (hH : 0 ≤ H) (hh : 0 ≤ h) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 / 2 ≤ x → ∀ B : ℝ,
      ((⌈B * x⌉ : ℤ) : ℝ) + ((⌈Cinit * x⌉ : ℤ) : ℝ) +
          (2 * L + H + h) * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 2) + L + H ≤
        ((⌈(B + C) * x⌉ : ℤ) : ℝ) := by
  refine ⟨Cinit + (2*L+H+h)*(C₁+6) + 2*(L+H) + 4, ?_, ?_⟩
  · nlinarith only [hCi, hL, hH, mul_nonneg (by linarith only [hL, hH, hh] : (0:ℝ) ≤ 2*L+H+h)
      (by linarith only [hC₁] : (0:ℝ) ≤ C₁+6)]
  · intro x hx B
    have e1 := Int.ceil_lt_add_one (B * x)
    have e2 := Int.ceil_lt_add_one (Cinit * x)
    have e3 := Int.ceil_lt_add_one (C₁ * x)
    have e4 := Int.le_ceil ((B + (Cinit + (2*L+H+h)*(C₁+6) + 2*(L+H) + 4)) * x)
    have hnn : (0:ℝ) ≤ 2*L+H+h := by linarith only [hL, hH, hh]
    have e3' := mul_le_mul_of_nonneg_left (le_of_lt e3) hnn
    have hD : (0:ℝ) ≤ 6*(2*L+H+h) + 2*(L+H) + 4 := by linarith only [hL, hH, hh]
    have hx' : (0:ℝ) ≤ x - 1/2 := by linarith only [hx]
    nlinarith only [e1, e2, e3', e4, hnn, mul_nonneg hD hx']

/-- `p.global.selection` arithmetic of the containment budget: `n₀ + (2L+H+h)(J+2) + ⌈log₃(2√d) +
ε(J+1)/log 3⌉
≤ 2 jStar` follows from the entry bound and the lower scale `e.global.selection.lower.scale` once
`C` is large. -/
theorem containment_arith (Cinit C₁ L H h ε d : ℝ) (hCi : 0 ≤ Cinit) (hC₁ : 0 ≤ C₁) (hL : 0 ≤ L)
    (hH : 0 ≤ H) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 / 2 ≤ x → ∀ B : ℝ, 0 ≤ B → ∀ jStar : ℤ,
      ⌈C * (B + 1) * x⌉ ≤ jStar →
      (jStar : ℝ) + ((⌈B * x⌉ : ℤ) : ℝ) + ((⌈Cinit * x⌉ : ℤ) : ℝ) +
          (2 * L + H + h) * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 2) +
          ((⌈Real.logb 3 (2 * Real.sqrt d) + ε * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 1) / Real.log 3⌉ : ℤ) :
            ℝ) ≤
        2 * jStar := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hsqrtd : (1 : ℝ) ≤ Real.sqrt d := by
    have h := Real.sqrt_le_sqrt hd
    rwa [Real.sqrt_one] at h
  have h2sqrtd : (1 : ℝ) ≤ 2 * Real.sqrt d := by linarith only [hsqrtd]
  have hL0 : 0 ≤ Real.logb 3 (2 * Real.sqrt d) :=
    Real.logb_nonneg (by norm_num) h2sqrtd
  set A : ℝ := Cinit + (2 * L + H + h) * C₁ + ε * C₁ / Real.log 3 with hAdef
  set K : ℝ := 3 + 3 * (2 * L + H + h) + 2 * ε / Real.log 3 +
      Real.logb 3 (2 * Real.sqrt d) with hKdef
  have hApos : 0 ≤ A := by
    have h1 : 0 ≤ (2 * L + H + h) * C₁ := mul_nonneg (by linarith only [hL, hH, hh]) hC₁
    have h2 : 0 ≤ ε * C₁ / Real.log 3 := div_nonneg (mul_nonneg hε hC₁) hlog3.le
    rw [hAdef]; linarith only [hCi, h1, h2]
  have hKpos : 0 ≤ K := by
    have h1 : 0 ≤ 2 * ε / Real.log 3 := div_nonneg (by linarith only [hε]) hlog3.le
    rw [hKdef]; linarith only [h1, hL0, hL, hH, hh]
  refine ⟨1 + A + 2 * K, by linarith only [hApos, hKpos], ?_⟩
  intro x hx B hB jStar hjStar
  have hxpos : 0 < x := by linarith only [hx]
  have hC11 : ((⌈C₁ * x⌉ : ℤ) : ℝ) ≤ C₁ * x + 1 := (Int.ceil_lt_add_one (C₁ * x)).le
  have hB1 : ((⌈B * x⌉ : ℤ) : ℝ) ≤ B * x + 1 := (Int.ceil_lt_add_one (B * x)).le
  have hCi1 : ((⌈Cinit * x⌉ : ℤ) : ℝ) ≤ Cinit * x + 1 := (Int.ceil_lt_add_one (Cinit * x)).le
  have hMbound : (2 * L + H + h) * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 2) ≤ (2 * L + H + h) * (C₁ * x + 3) :=
    mul_le_mul_of_nonneg_left (by linarith only [hC11]) (by linarith only [hL, hH, hh])
  have hεterm : ε * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 1) ≤ ε * (C₁ * x + 2) :=
    mul_le_mul_of_nonneg_left (by linarith only [hC11]) hε
  have hinv : 0 ≤ (Real.log 3)⁻¹ := inv_nonneg.mpr hlog3.le
  have hεdiv : ε * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 1) / Real.log 3 ≤ ε * (C₁ * x + 2) / Real.log 3 := by
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hεterm hinv
  have hlogceil : ((⌈Real.logb 3 (2 * Real.sqrt d) +
        ε * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 1) / Real.log 3⌉ : ℤ) : ℝ)
      ≤ Real.logb 3 (2 * Real.sqrt d) + ε * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 1) / Real.log 3 + 1 :=
    (Int.ceil_lt_add_one _).le
  have hQbound : ((⌈Real.logb 3 (2 * Real.sqrt d) +
        ε * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 1) / Real.log 3⌉ : ℤ) : ℝ)
      ≤ Real.logb 3 (2 * Real.sqrt d) + ε * (C₁ * x + 2) / Real.log 3 + 1 := by
    linarith only [hlogceil, hεdiv]
  have hTsum : ((⌈B * x⌉ : ℤ) : ℝ) + ((⌈Cinit * x⌉ : ℤ) : ℝ) +
      (2 * L + H + h) * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 2) +
      ((⌈Real.logb 3 (2 * Real.sqrt d) +
          ε * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 1) / Real.log 3⌉ : ℤ) : ℝ)
      ≤ (B * x + 1) + (Cinit * x + 1) + (2 * L + H + h) * (C₁ * x + 3) +
          (Real.logb 3 (2 * Real.sqrt d) + ε * (C₁ * x + 2) / Real.log 3 + 1) := by
    linarith only [hB1, hCi1, hMbound, hQbound]
  have hRHSeq : (B * x + 1) + (Cinit * x + 1) + (2 * L + H + h) * (C₁ * x + 3) +
      (Real.logb 3 (2 * Real.sqrt d) + ε * (C₁ * x + 2) / Real.log 3 + 1) =
      (B + A) * x + K := by
    rw [hAdef, hKdef]; ring
  have hTsum2 : ((⌈B * x⌉ : ℤ) : ℝ) + ((⌈Cinit * x⌉ : ℤ) : ℝ) +
      (2 * L + H + h) * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 2) +
      ((⌈Real.logb 3 (2 * Real.sqrt d) +
          ε * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 1) / Real.log 3⌉ : ℤ) : ℝ)
      ≤ (B + A) * x + K := by
    rw [← hRHSeq]; exact hTsum
  have hxconst : K ≤ 2 * K * x := by
    have heq3 : 2 * K * x - K = K * (2 * x - 1) := by ring
    have h1 : 0 ≤ K * (2 * x - 1) := mul_nonneg hKpos (by linarith only [hx])
    linarith only [heq3, h1]
  have hsum2 : (B + A) * x + K ≤ (B + A + 2 * K) * x := by
    have heq : (B + A + 2 * K) * x - ((B + A) * x + K) = 2 * K * x - K := by ring
    linarith only [hxconst, heq]
  have hnonneg : 0 ≤ 1 + (A + 2 * K) * B := by
    have hprod : 0 ≤ (A + 2 * K) * B := mul_nonneg (by linarith only [hApos, hKpos]) hB
    linarith only [hprod]
  have hCB : (B + A + 2 * K) * x ≤ (1 + A + 2 * K) * (B + 1) * x := by
    have heq2 : (1 + A + 2 * K) * (B + 1) * x - (B + A + 2 * K) * x =
        (1 + (A + 2 * K) * B) * x := by ring
    have hnonneg2 : 0 ≤ (1 + (A + 2 * K) * B) * x := mul_nonneg hnonneg hxpos.le
    linarith only [heq2, hnonneg2]
  have hjStarR : (1 + A + 2 * K) * (B + 1) * x ≤ (jStar : ℝ) := by
    have h1 : ((⌈(1 + A + 2 * K) * (B + 1) * x⌉ : ℤ) : ℝ) ≤ (jStar : ℝ) := by
      exact_mod_cast hjStar
    have h2 : (1 + A + 2 * K) * (B + 1) * x ≤ ((⌈(1 + A + 2 * K) * (B + 1) * x⌉ : ℤ) : ℝ) :=
      Int.le_ceil _
    linarith only [h1, h2]
  have hfinal : ((⌈B * x⌉ : ℤ) : ℝ) + ((⌈Cinit * x⌉ : ℤ) : ℝ) +
      (2 * L + H + h) * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 2) +
      ((⌈Real.logb 3 (2 * Real.sqrt d) +
          ε * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 1) / Real.log 3⌉ : ℤ) : ℝ)
      ≤ (jStar : ℝ) := by
    calc ((⌈B * x⌉ : ℤ) : ℝ) + ((⌈Cinit * x⌉ : ℤ) : ℝ) +
        (2 * L + H + h) * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 2) +
        ((⌈Real.logb 3 (2 * Real.sqrt d) +
            ε * (((⌈C₁ * x⌉ : ℤ) : ℝ) + 1) / Real.log 3⌉ : ℤ) : ℝ)
        ≤ (B + A) * x + K := hTsum2
      _ ≤ (B + A + 2 * K) * x := hsum2
      _ ≤ (1 + A + 2 * K) * (B + 1) * x := hCB
      _ ≤ (jStar : ℝ) := hjStarR
  linarith only [hfinal]

end

end HCPolySupport.HighContrast.Multiscale
