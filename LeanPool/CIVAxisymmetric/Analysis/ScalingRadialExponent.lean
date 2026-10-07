/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scaling Radial Exponent

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Real

noncomputable section
namespace CIV

/-- The radial anisotropic residual exponent `2*h*b` is nonnegative when `h ≥ 0` and `b` is a
natural
number. -/
theorem radialAnisoResidualExponent_nonneg {h : ℝ} (hh : 0 ≤ h) (b : ℕ) :
    0 ≤ 2 * h * (b : ℝ) := by
  have h2 : 0 ≤ 2 * h := by nlinarith only [hh]
  have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  nlinarith only [h2, hb]

/-- When `0 < R ≤ 1` and `h ≥ 0`, the radial anisotropic residual exponent is nonnegative, so
`R^(2*h*b) ≤ 1`. -/
theorem rpow_radialAnisoResidualExponent_le_one {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1)
    {h : ℝ} (hh : 0 ≤ h) (b : ℕ) :
    R ^ (2 * h * (b : ℝ)) ≤ 1 := by
  have h_exp_nonneg : 0 ≤ 2 * h * (b : ℝ) :=
    radialAnisoResidualExponent_nonneg hh b
  exact Real.rpow_le_one hR0.le hR1 h_exp_nonneg

/-- Under the parabolic rescaling `u → R u(R·, R²·)` with `0 < R ≤ 1`, the radial anisotropic bound
`C * (-t)^(-1/2 - a/2 - (1/2-h)*b)` is rescaled to `R^(1+a+b) * C * (-(R²*t))^(-1/2 - a/2 -
(1/2-h)*b)`.
The rescaling introduces a factor `R^(2*h*b)` that is ≤ 1, so the original constant `C` still
works. -/
theorem rpow_scaled_le_of_radialAnisoBound {C h t R : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (ht : t < 0) (hR0 : 0 < R) (hR1 : R ≤ 1) (a b : ℕ) :
    (R : ℝ) ^ (1 + a + b) * C * (-(R ^ 2 * t)) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * b)
      ≤ C * (-t) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * b) := by
  set e := -(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ) with he
  have h_nonneg_neg_t : 0 ≤ -t := by linarith only [ht]
  have h_nonneg_neg_R2t : 0 ≤ -(R ^ 2 * t) := by
    nlinarith only [hR0.le, h_nonneg_neg_t]
  have hR2pos : 0 < R ^ 2 := pow_pos hR0 2
  have hR2_nonneg : 0 ≤ R ^ 2 := hR2pos.le
  have hexp_eq : ((1 + a + b : ℕ) : ℝ) + 2 * e = 2 * h * (b : ℝ) := by
    dsimp [e]
    push_cast
    ring
  have h_main : (R : ℝ) ^ (1 + a + b) * C * (-(R ^ 2 * t)) ^ e
      = ((R : ℝ) ^ (2 * h * (b : ℝ))) * C * (-t) ^ e := by
    -- Step 1: convert monoid power to rpow
    rw [show (R : ℝ) ^ (1 + a + b) = (R : ℝ) ^ ((1 + a + b : ℕ) : ℝ) from by
      simpa using (Real.rpow_natCast (R : ℝ) (1 + a + b)).symm]
    -- Step 2: -(R^2 * t) = R^2 * (-t)
    rw [show -(R ^ 2 * t) = (R ^ 2) * (-t) from by ring]
    -- Step 3: split (R^2 * (-t))^e = (R^2)^e * (-t)^e
    rw [Real.mul_rpow hR2_nonneg h_nonneg_neg_t]
    -- Step 4: reassociate: bring R^((1+a+b):ℝ) and (R^2)^e together
    -- Goal: R^((1+a+b):ℝ) * C * ((R^2)^e * (-t)^e) = R^(2*h*b) * C * (-t)^e
    -- First, combine R^((1+a+b):ℝ) * (R^2)^e = R^(((1+a+b):ℝ) + 2*e) using rpow_add
    -- But we need (R^2)^e = R^(2*e) first
    have hR2e : (R ^ 2) ^ e = (R : ℝ) ^ (2 * e) := by
      calc
        (R ^ 2) ^ e = ((R : ℝ) ^ (2 : ℝ)) ^ e := by norm_num [Real.rpow_natCast]
        _ = (R : ℝ) ^ ((2 : ℝ) * e) := by rw [Real.rpow_mul hR0.le (2 : ℝ) e]
        _ = (R : ℝ) ^ (2 * e) := by ring
    rw [hR2e]
    -- Now: R^((1+a+b):ℝ) * C * (R^(2*e) * (-t)^e) = R^(2*h*b) * C * (-t)^e
    -- Reassociate LHS: (R^((1+a+b):ℝ) * R^(2*e)) * C * (-t)^e
    have h_reassoc : (R : ℝ) ^ ((1 + a + b : ℕ) : ℝ) * C * ((R : ℝ) ^ (2 * e) * (-t) ^ e)
        = ((R : ℝ) ^ ((1 + a + b : ℕ) : ℝ) * (R : ℝ) ^ (2 * e)) * C * (-t) ^ e := by
      ring
    rw [h_reassoc]
    -- Now: (R^((1+a+b):ℝ) * R^(2*e)) * C * (-t)^e = R^(2*h*b) * C * (-t)^e
    rw [← Real.rpow_add hR0 ((1 + a + b : ℕ) : ℝ) (2 * e)]
    -- Now: R^(((1+a+b):ℝ) + 2*e) * C * (-t)^e = R^(2*h*b) * C * (-t)^e
    rw [hexp_eq]
  rw [h_main]
  -- Now: R^(2*h*b) * C * (-t)^e ≤ C * (-t)^e
  calc
    ((R : ℝ) ^ (2 * h * (b : ℝ))) * C * (-t) ^ e
        ≤ 1 * C * (-t) ^ e := by
      refine mul_le_mul_of_nonneg_right ?_ (by
        have h_nonneg : 0 ≤ (-t) ^ e := Real.rpow_nonneg h_nonneg_neg_t _
        nlinarith only [hC, h_nonneg])
      refine mul_le_mul_of_nonneg_right ?_ hC
      exact rpow_radialAnisoResidualExponent_le_one hR0 hR1 hh0 b
    _ = C * (-t) ^ e := by ring
    _ = C * (-t) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * b) := by rfl

/-- For any `C ≥ 0`, `0 ≤ h`, and `0 < R ≤ 1`, there exists a constant `C' ≥ 0` (namely `C`
itself) such that the rescaled radial anisotropic bound holds for all `t < 0` and all `a, b : ℕ`. -/
theorem exists_radialAnisoBound_rescaled {C h : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t : ℝ, t < 0 → ∀ a b : ℕ,
      (R : ℝ) ^ (1 + a + b) * C * (-(R ^ 2 * t)) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * b)
        ≤ C' * (-t) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * b) := by
  refine ⟨C, hC, fun t ht a b => ?_⟩
  exact rpow_scaled_le_of_radialAnisoBound hC hh0 ht hR0 hR1 a b

end CIV
