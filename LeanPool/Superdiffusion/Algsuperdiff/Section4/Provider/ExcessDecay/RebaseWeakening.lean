/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepConsumerLegBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EnnrealShell

/-!
# RebaseWeakening

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

/-! ## 1. The scalar move -/

/-- **The two leg moves, as one scalar inequality.**

`rpow_neg_nine_halves_le_rpow_neg_six` is exactly this fact; it is re-exported
here under a re-base name so that the harmonic lane reads it from its own module
rather than through the excess-decay consumer check. -/
theorem rpow_legMove_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow s (-(9 / 2 : ℝ)) ≤ Real.rpow s (-(6 : ℝ)) :=
  rpow_neg_nine_halves_le_rpow_neg_six hs hs1

/-! ## 2. The real-valued leg -/

/-- One leg of a real-valued clause, moved.  The leg's shape is the one every
proved transcription uses: the `s`-power, then a nonnegative `3`-power, then
the `toReal` of an `ℝ≥0∞` seminorm. -/
theorem rpow_legMove_mul_le {s a T : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 ≤ a)
    (hT : 0 ≤ T) :
    Real.rpow s (-(9 / 2 : ℝ)) * a * T ≤ Real.rpow s (-(6 : ℝ)) * a * T := by
  have hmove := rpow_legMove_le hs hs1
  have hstep : Real.rpow s (-(9 / 2 : ℝ)) * a ≤ Real.rpow s (-(6 : ℝ)) * a :=
    mul_le_mul_of_nonneg_right hmove ha
  exact mul_le_mul_of_nonneg_right hstep hT

/-- **The real-valued display, with both `∇h` legs moved to `s^{-6}`.**

`H` carries the two untouched summands (the flux bracket and the `σ` force leg);
the two `∇h` legs move.  Abstract in every carrier, so this one lemma re-cuts
each `…Real` clause of the lane. -/
theorem realBracket_legMove_le {C s a₄ a₅ T₄ T₅ H : ℝ} (hC : 0 ≤ C)
    (hs : 0 < s) (hs1 : s ≤ 1) (h₄ : 0 ≤ a₄) (h₅ : 0 ≤ a₅) (hT₄ : 0 ≤ T₄)
    (hT₅ : 0 ≤ T₅) :
    C * (H + Real.rpow s (-(9 / 2 : ℝ)) * a₄ * T₄ +
        Real.rpow s (-(9 / 2 : ℝ)) * a₅ * T₅) ≤
      C * (H + Real.rpow s (-(6 : ℝ)) * a₄ * T₄ +
        Real.rpow s (-(6 : ℝ)) * a₅ * T₅) := by
  have e₄ := rpow_legMove_mul_le hs hs1 h₄ hT₄
  have e₅ := rpow_legMove_mul_le hs hs1 h₅ hT₅
  refine mul_le_mul_of_nonneg_left ?_ hC
  linarith only [e₄, e₅]

/-! ## 3. The `ℝ≥0∞` prefactor product -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
