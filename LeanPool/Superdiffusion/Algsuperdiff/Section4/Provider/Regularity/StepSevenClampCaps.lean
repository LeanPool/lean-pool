/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaSlots
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringSlot

/-!
# StepSevenClampCaps

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The two off-grid constants at the §4.4 pin -/

/-- **The off-grid stability constant at the upper ratio index.** `36 d (1/8) /
((1/8 − 1/32)(1 − 1/16)) = 51.2 d ≤ 96 d`. -/
theorem offGridStabilityConst_stepSevenUpper_le (d : ℕ) :
    offGridStabilityConst d (1 / 8) (1 / 32) ≤ 96 * (d : ℝ) := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hden : (0 : ℝ) < ((1 : ℝ) / 8 - 1 / 32) * (1 - 2 * (1 / 32)) := by norm_num
  rw [offGridStabilityConst, div_le_iff₀ hden]
  linarith only [hd]

/-! ## 2. The pin's index identities -/

/-- The Caccioppoli's first exponent, halved, is the upper ratio index `1/8`. -/
theorem stepSevenCaccS_half_eq : stepSevenCaccS / 2 = 1 / 8 := by
  rw [stepSevenCaccS_eq]; norm_num

/-- The `hlambda` slot's index is the upper ratio index: `s₀/2 = 1/8`. -/
theorem stepSevenCgS_half_eq : stepSevenCgS / 2 = 1 / 8 := by
  rw [stepSevenCgS_eq]; norm_num

/-- The good-event slot, in numerals. -/
theorem stepOneS_div_eight_eq : stepOneS / 8 = 1 / 32 := by
  rw [stepOneS_eq]; norm_num

end

end Algsuperdiff.Section4.Provider.Regularity
