/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Normalized logarithmic moment-generating functions -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace EhrhardGaussian

/-- `Φ_F(q) = q⁻¹ log E e^{qF}` for `q ≠ 0` and `E F` for `q = 0` (§3.1). -/
def logMGFRatio {E : Type*} [MeasurableSpace E] (μ : Measure E) (F : E → ℝ) (q : ℝ) : ℝ :=
  if q = 0 then ∫ x, F x ∂μ else q⁻¹ * Real.log (∫ x, Real.exp (q * F x) ∂μ)

end EhrhardGaussian

end

end
