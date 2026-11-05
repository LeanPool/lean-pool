/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSixHolderExponent

/-!
# StepBoundaryAbsorption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

noncomputable section

/-! ## 1. The print's `t e^t ≤ e^{2t}` -/

/-- **`t e^t ≤ e^{2t}`** for `t ≥ 0` -- the print's absorption of a polynomial
prefactor into its own exponential.  The only input is `x ≤ x + 1 ≤ e^x`. -/
theorem mul_exp_le_exp_two_mul {a : ℝ} (ha : 0 ≤ a) :
    a * Real.exp a ≤ Real.exp (2 * a) := by
  have h1 : a ≤ Real.exp a :=
    le_trans (by linarith only [ha] : a ≤ a + 1) (Real.add_one_le_exp a)
  have h2 : a * Real.exp a ≤ Real.exp a * Real.exp a :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos a).le
  have h3 : Real.exp a * Real.exp a = Real.exp (2 * a) := by
    rw [← Real.exp_add]; ring_nf
  have h4 : 0 ≤ a * Real.exp a := mul_nonneg ha (Real.exp_pos a).le
  linarith only [h2, h3, h4]

/-- `3^x = exp((log 3) x)`; the single place `rpow` and `exp` meet in this module. -/
theorem rpow_three_eq_exp (x : ℝ) : Real.rpow (3 : ℝ) x = Real.exp (Real.log 3 * x) :=
  Real.rpow_def_of_pos (by norm_num) x

/-- **The absorption in `3`-powers**: for every `t ≥ 0`,

```text
   t · 3^{(1/4) t}  ≤  (4 / log 3) · 3^{(1/2) t} .
``` -/
theorem mul_rpow_three_quarter_le (t : ℝ) (ht : 0 ≤ t) :
    t * Real.rpow (3 : ℝ) (1 / 4 * t) ≤ 4 / Real.log 3 * Real.rpow (3 : ℝ) (1 / 2 * t) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha : 0 ≤ Real.log 3 / 4 * t := mul_nonneg (by linarith only [hlog]) ht
  have hq : Real.rpow (3 : ℝ) (1 / 4 * t) = Real.exp (Real.log 3 / 4 * t) := by
    rw [rpow_three_eq_exp]
    congr 1
    ring
  have hh : Real.rpow (3 : ℝ) (1 / 2 * t) = Real.exp (2 * (Real.log 3 / 4 * t)) := by
    rw [rpow_three_eq_exp]
    congr 1
    ring
  have ht' : t = 4 / Real.log 3 * (Real.log 3 / 4 * t) := by
    field_simp
  have habs := mul_exp_le_exp_two_mul ha
  have hpos : (0 : ℝ) ≤ 4 / Real.log 3 := div_nonneg (by norm_num) hlog.le
  have hmul := mul_le_mul_of_nonneg_left habs hpos
  rw [hq, hh]
  nth_rewrite 1 [ht']
  calc 4 / Real.log 3 * (Real.log 3 / 4 * t) * Real.exp (Real.log 3 / 4 * t)
      = 4 / Real.log 3 * ((Real.log 3 / 4 * t) * Real.exp (Real.log 3 / 4 * t)) := by ring
    _ ≤ 4 / Real.log 3 * Real.exp (2 * (Real.log 3 / 4 * t)) := hmul

/-! ## 2. The `ε`-funded flat leg: the print's absorption, `α`-free -/

/-- **The printed absorption**, at the abstract reals.

If the flat `∇h` leg enters the `δ`-budget multiplied by the `ε`-sum -- i.e. with
the coefficient `S ≤ 2 C₁^{-1} t`, which `e.sum.eps.j.bound` supplies with `t =
(1-α)(m-n)` -- then

```text
   exp( C₁^{-1} C_iter t ) · S · H  ≤  (8 / (C₁ log 3)) · 3^{(1/2) t} · H .
```

The constant carries NO `α`, NO `γ` and NO `δ`: the coefficient IS the
exponent's own argument, which is precisely why the print's `t e^t ≤ e^{2t}`
step is free. -/
theorem stepSixFlat_epsFunded_absorb {C1 Citer t S H : ℝ} {k : ℕ} (hC1 : 0 < C1)
    (hCiter : 0 ≤ Citer) (ht : 0 ≤ t) (hS0 : 0 ≤ S) (hH : 0 ≤ H)
    (hfloor : 4 * Citer * ((k : ℝ) + 1) / Real.log 3 ≤ C1)
    (hS : S ≤ 2 * (C1⁻¹ * t)) :
    Real.exp (C1⁻¹ * Citer * t) * (S * H) ≤
      8 / (C1 * Real.log 3) * Real.rpow (3 : ℝ) (1 / 2 * t) * H := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hexp : Real.exp (C1⁻¹ * Citer * t) ≤ Real.rpow (3 : ℝ) (1 / 4 * t) :=
    exp_le_rpow_three_quarter_of_step6_floor (k := k) hC1 hCiter ht hfloor
  have hqnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 4 * t) := Real.rpow_nonneg (by norm_num) _
  have h1 : Real.exp (C1⁻¹ * Citer * t) * S ≤ Real.rpow (3 : ℝ) (1 / 4 * t) * (2 * (C1⁻¹ * t)) := by
    have ha := mul_le_mul_of_nonneg_right hexp hS0
    have hb := mul_le_mul_of_nonneg_left hS hqnn
    linarith only [ha, hb]
  have h2 : Real.rpow (3 : ℝ) (1 / 4 * t) * (2 * (C1⁻¹ * t)) =
      2 * C1⁻¹ * (t * Real.rpow (3 : ℝ) (1 / 4 * t)) := by ring
  have h3 : (0 : ℝ) ≤ 2 * C1⁻¹ := by
    have : (0 : ℝ) ≤ C1⁻¹ := (inv_pos.mpr hC1).le
    linarith only [this]
  have h4 := mul_le_mul_of_nonneg_left (mul_rpow_three_quarter_le t ht) h3
  have h5 : 2 * C1⁻¹ * (4 / Real.log 3 * Real.rpow (3 : ℝ) (1 / 2 * t)) =
      8 / (C1 * Real.log 3) * Real.rpow (3 : ℝ) (1 / 2 * t) := by
    field_simp
    ring
  have h6 : Real.exp (C1⁻¹ * Citer * t) * S ≤
      8 / (C1 * Real.log 3) * Real.rpow (3 : ℝ) (1 / 2 * t) := by
    linarith only [h1, h2, h4, h5]
  have h7 := mul_le_mul_of_nonneg_right h6 hH
  calc Real.exp (C1⁻¹ * Citer * t) * (S * H)
      = Real.exp (C1⁻¹ * Citer * t) * S * H := by ring
    _ ≤ 8 / (C1 * Real.log 3) * Real.rpow (3 : ℝ) (1 / 2 * t) * H := h7

end

end Algsuperdiff.Section4.Provider.Regularity
