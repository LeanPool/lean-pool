/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Function.L2Space

/-! # Integral formulas for real L² representatives -/

public section

namespace CutoffRigidity

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {π : Measure Ω}

/-- The real L² inner product is the integral of the product of representatives. -/
theorem real_inner_toLp {X Y : Ω → ℝ} (hX : MemLp X 2 π) (hY : MemLp Y 2 π) :
    inner ℝ (hX.toLp X) (hY.toLp Y) = ∫ ω, X ω * Y ω ∂π := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

/-- The squared L² norm is the actual second moment. -/
theorem norm_toLp_sq {X : Ω → ℝ} (hX : MemLp X 2 π) :
    ‖hX.toLp X‖ ^ 2 = ∫ ω, X ω ^ 2 ∂π := by
  rw [← real_inner_self_eq_norm_sq, real_inner_toLp]
  simp only [pow_two]

end CutoffRigidity
