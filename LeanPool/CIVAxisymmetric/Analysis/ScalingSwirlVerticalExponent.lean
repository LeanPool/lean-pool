/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scaling Swirl Vertical Exponent

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Real

noncomputable section
namespace CIV

/-- The swirl/vertical anisotropic residual exponent `2*h*(b-1)` is bounded below by `-(2*h)` when
`h ≥ 0` and `b` is a natural number, with equality exactly at `b = 0`. -/
theorem swirlVerticalAnisoResidualExponent_ge {h : ℝ} (hh : 0 ≤ h) (b : ℕ) :
    -(2 * h) ≤ 2 * h * ((b : ℝ) - 1) := by
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
  nlinarith only [hh, hb]

/-- When `0 < R ≤ 1` and `h ≥ 0`, the swirl/vertical anisotropic residual exponent is at least
`-(2*h)`, so `R^(2*h*(b-1)) ≤ R^(-(2*h))`. -/
theorem rpow_swirlVerticalAnisoResidualExponent_le {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1)
    {h : ℝ} (hh : 0 ≤ h) (b : ℕ) :
    R ^ (2 * h * ((b : ℝ) - 1)) ≤ R ^ (-(2 * h)) :=
  Real.rpow_le_rpow_of_exponent_ge hR0 hR1 (swirlVerticalAnisoResidualExponent_ge hh b)

/-- Under the parabolic rescaling `u → R u(R·, R²·)`, the swirl/vertical anisotropic bound
of `eq:aniso:bounds` (the angular-mean form is `eq:interior:mean:bounds`),
`C * (-t)^(-1/2 - h - a/2 - (1/2-h)*b)`, is rescaled to
`R^(1+a+b) * C * (-(R²*t))^(-1/2 - h - a/2 - (1/2-h)*b)`, and the residual power of `R` is exactly
`(1+a+b) + 2*(-1/2 - h - a/2 - (1/2-h)*b) = 2*h*(b-1)`. -/
theorem rpow_scaled_eq_swirlVerticalAnisoResidual {C h t R : ℝ} (ht : t < 0) (hR0 : 0 < R)
    (a b : ℕ) :
    (R : ℝ) ^ (1 + a + b) * C * (-(R ^ 2 * t)) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * b)
      = R ^ (2 * h * ((b : ℝ) - 1)) * C
          * (-t) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * b) := by
  set e := -(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ) with he
  have h_nonneg_neg_t : 0 ≤ -t := by linarith only [ht]
  have hR2_nonneg : (0 : ℝ) ≤ R ^ 2 := (pow_pos hR0 2).le
  have hexp_eq : ((1 + a + b : ℕ) : ℝ) + 2 * e = 2 * h * ((b : ℝ) - 1) := by
    dsimp [e]
    push_cast
    ring
  rw [show (R : ℝ) ^ (1 + a + b) = (R : ℝ) ^ ((1 + a + b : ℕ) : ℝ) from by
    simpa using (Real.rpow_natCast (R : ℝ) (1 + a + b)).symm]
  rw [show -(R ^ 2 * t) = (R ^ 2) * (-t) from by ring]
  rw [Real.mul_rpow hR2_nonneg h_nonneg_neg_t]
  have hR2e : ((R : ℝ) ^ 2) ^ e = (R : ℝ) ^ (2 * e) := by
    calc
      ((R : ℝ) ^ 2) ^ e = ((R : ℝ) ^ (2 : ℝ)) ^ e := by norm_num [Real.rpow_natCast]
      _ = (R : ℝ) ^ ((2 : ℝ) * e) := by rw [Real.rpow_mul hR0.le (2 : ℝ) e]
      _ = (R : ℝ) ^ (2 * e) := by ring
  rw [hR2e]
  have h_reassoc : (R : ℝ) ^ ((1 + a + b : ℕ) : ℝ) * C * ((R : ℝ) ^ (2 * e) * (-t) ^ e)
      = ((R : ℝ) ^ ((1 + a + b : ℕ) : ℝ) * (R : ℝ) ^ (2 * e)) * C * (-t) ^ e := by
    ring
  rw [h_reassoc, ← Real.rpow_add hR0 ((1 + a + b : ℕ) : ℝ) (2 * e), hexp_eq]

/-- Under the parabolic rescaling `u → R u(R·, R²·)` with `0 < R ≤ 1`, the swirl/vertical
conjunct of `eq:aniso:bounds` survives only with the enlarged constant `R^(-(2*h)) * C`: the
residual power of `R` is `2*h*(b-1) ≥ -(2*h)`, so the rescaling factor is at most `R^(-(2*h))`,
which is `≥ 1`. Contrast the radial conjunct, whose residual power `2*h*b` is nonnegative and whose
constant is therefore unchanged. -/
theorem rpow_scaled_le_of_swirlVerticalAnisoBound {C h t R : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (ht : t < 0) (hR0 : 0 < R) (hR1 : R ≤ 1) (a b : ℕ) :
    (R : ℝ) ^ (1 + a + b) * C * (-(R ^ 2 * t)) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * b)
      ≤ R ^ (-(2 * h)) * C
          * (-t) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * b) := by
  have h_nonneg_neg_t : 0 ≤ -t := by linarith only [ht]
  rw [rpow_scaled_eq_swirlVerticalAnisoResidual ht hR0 a b]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg h_nonneg_neg_t _)
  exact mul_le_mul_of_nonneg_right (rpow_swirlVerticalAnisoResidualExponent_le hR0 hR1 hh0 b) hC

/-- The constant `R^(-(2*h))` is attained: at `b = 0` the rescaled swirl/vertical bound equals
`R^(-(2*h)) * C * (-t)^(-1/2 - h - a/2)` exactly, so no smaller constant works. This is the
asymmetry with the radial conjunct, whose constant is unchanged. -/
theorem rpow_scaled_eq_of_swirlVerticalAnisoBound_of_b_eq_zero {C h t R : ℝ} (ht : t < 0)
    (hR0 : 0 < R) (a : ℕ) :
    (R : ℝ) ^ (1 + a) * C * (-(R ^ 2 * t)) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2)
      = R ^ (-(2 * h)) * C * (-t) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2) := by
  have key := rpow_scaled_eq_swirlVerticalAnisoResidual (C := C) (h := h) (t := t) (R := R) ht hR0
    a 0
  have hz : 2 * h * (((0 : ℕ) : ℝ) - 1) = -(2 * h) := by
    push_cast
    ring
  rw [hz] at key
  have hexp : -(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * ((0 : ℕ) : ℝ)
      = -(1 / 2 : ℝ) - h - (a : ℝ) / 2 := by
    push_cast
    ring
  rw [hexp] at key
  simpa using key

/-- For any `C ≥ 0`, `0 ≤ h`, and `0 < R ≤ 1`, the rescaled swirl/vertical anisotropic bound
holds with the constant `C' = R^(-(2*h)) * C`, for all `t < 0` and all `a, b : ℕ`. Unlike the radial
conjunct, the constant is genuinely enlarged. -/
theorem exists_swirlVerticalAnisoBound_rescaled {C h : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) :
    ∃ C' : ℝ, 0 ≤ C' ∧ C' = R ^ (-(2 * h)) * C ∧ ∀ t : ℝ, t < 0 → ∀ a b : ℕ,
      (R : ℝ) ^ (1 + a + b) * C
          * (-(R ^ 2 * t)) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * b)
        ≤ C' * (-t) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * b) := by
  refine ⟨R ^ (-(2 * h)) * C, mul_nonneg (Real.rpow_nonneg hR0.le _) hC, rfl,
    fun t ht a b => ?_⟩
  exact rpow_scaled_le_of_swirlVerticalAnisoBound hC hh0 ht hR0 hR1 a b

end CIV
