/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! C3: an explicit, uniform threshold absorbs t log t and t errors into eta t². -/

@[expose] public section

namespace GapExtremal.R417

/-- The coefficient bounding the logarithmic remainder after parameter selection. -/
noncomputable def remainderCoefficient (c a b C A₀ : ℝ) : ℝ :=
  (a / c) * A₀ + 2 * a * C + 12 * a + C + C * A₀ + 12 * b + Real.log 48

theorem scalar_loss_envelope (c a b C A₀ t E : ℝ) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hA₀ : 0 ≤ A₀) (ht : 1 ≤ t)
    (hE : E ≤ (c / a) * t ^ 2 + (a / c * t + C) *
      (2 * a * t + Real.log t + A₀) + 12 * a * t + 12 * b + Real.log 48) :
    E ≤ (c / a + 2 * a ^ 2 / c) * t ^ 2 +
      (a / c) * t * Real.log t + remainderCoefficient c a b C A₀ * t := by
  have hlog : Real.log t ≤ t := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t by linarith)
    linarith
  let R := C * A₀ + 12 * b + Real.log 48
  have hR : 0 ≤ R := by
    dsimp [R]
    exact add_nonneg (add_nonneg (mul_nonneg hC hA₀) (by positivity))
      (Real.log_nonneg (by norm_num))
  have hnon : 0 ≤ C * (t - Real.log t) + R * (t - 1) :=
    add_nonneg (mul_nonneg hC (sub_nonneg.mpr hlog))
      (mul_nonneg hR (by linarith))
  have hid : ((c / a + 2 * a ^ 2 / c) * t ^ 2 +
      (a / c) * t * Real.log t + remainderCoefficient c a b C A₀ * t) -
      ((c / a) * t ^ 2 + (a / c * t + C) *
      (2 * a * t + Real.log t + A₀) + 12 * a * t + 12 * b + Real.log 48) =
        C * (t - Real.log t) + R * (t - 1) := by
    dsimp [remainderCoefficient, R]
    ring
  linarith

theorem log_le_two_sqrt {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ 2 * Real.sqrt t := by
  have ht0 : 0 ≤ t := by linarith
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
  have hh := Real.log_le_sub_one_of_pos hs
  calc
    Real.log t = Real.log (Real.sqrt t ^ 2) := congrArg Real.log (Real.sq_sqrt ht0).symm
    _ = 2 * Real.log (Real.sqrt t) := by rw [Real.log_pow]; norm_num
    _ ≤ 2 * Real.sqrt t := by linarith

theorem log_error_absorption (A B η : ℝ) (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      A * t * Real.log t + B * t ≤ η * t ^ 2 := by
  let T := max 1 (max ((4 * A / η) ^ 2) (2 * B / η))
  refine ⟨T, le_max_left _ _, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := by linarith
  have hAt : (4 * A / η) ^ 2 ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hBt : 2 * B / η ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hroot : 4 * A / η ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hAt
  have hroot' : 4 * A ≤ Real.sqrt t * η := (div_le_iff₀ hη).mp hroot
  have hB' : 2 * B ≤ t * η := (div_le_iff₀ hη).mp hBt
  have hprod := mul_le_mul_of_nonneg_right hroot' (Real.sqrt_nonneg t)
  have hprod' : 4 * A * Real.sqrt t ≤ η * t := by
    calc
      4 * A * Real.sqrt t ≤ (Real.sqrt t * η) * Real.sqrt t := hprod
      _ = η * t := by
        rw [show (Real.sqrt t * η) * Real.sqrt t = η * Real.sqrt t ^ 2 by ring,
          Real.sq_sqrt ht0]
  have hlog := mul_le_mul_of_nonneg_left (log_le_two_sqrt ht1) hA
  have hcoef : A * Real.log t + B ≤ η * t := by nlinarith
  calc
    A * t * Real.log t + B * t = t * (A * Real.log t + B) := by ring
    _ ≤ t * (η * t) := mul_le_mul_of_nonneg_left hcoef ht0
    _ = η * t ^ 2 := by ring

theorem coefficient_absorption (C A B η : ℝ) (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ (t E : ℝ), T ≤ t →
      E ≤ C * t ^ 2 + A * t * Real.log t + B * t → E ≤ (C + η) * t ^ 2 := by
  obtain ⟨T, hT, hbound⟩ := log_error_absorption A B η hA hη
  refine ⟨T, hT, fun t E ht hE => ?_⟩
  have hh := hbound t ht
  nlinarith

end GapExtremal.R417
