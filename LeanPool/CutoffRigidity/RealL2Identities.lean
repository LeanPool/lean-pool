/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Function.L2Space

/-! # Integral formulas for L² classes in real Hilbert spaces -/

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

/-- Compute the squared `L²` norm from any almost-everywhere representative. -/
theorem lp_norm_sq_eq_integral {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u : Ω →₂[π] F} {f : Ω → F} (hf : (u : Ω → F) =ᵐ[π] f) :
    ‖u‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂π := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  rw [hω, real_inner_self_eq_norm_sq]

/-- Compute the squared `L²` norm of the class of a square-integrable function. -/
theorem norm_toLp_norm_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : Ω → F} (hf : MemLp f 2 π) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂π :=
  lp_norm_sq_eq_integral hf.coeFn_toLp

/-- The squared `L²` norm is the integral of the square of a real representative. -/
theorem lp_real_norm_sq_eq_integral {u : Ω →₂[π] ℝ} {f : Ω → ℝ}
    (hf : (u : Ω → ℝ) =ᵐ[π] f) : ‖u‖ ^ 2 = ∫ ω, f ω ^ 2 ∂π := by
  simpa only [Real.norm_eq_abs, sq_abs] using lp_norm_sq_eq_integral hf

/-- The squared `L²` norm of a real function is its second moment. -/
theorem norm_toLp_sq {X : Ω → ℝ} (hX : MemLp X 2 π) :
    ‖hX.toLp X‖ ^ 2 = ∫ ω, X ω ^ 2 ∂π :=
  lp_real_norm_sq_eq_integral hX.coeFn_toLp

end CutoffRigidity
