/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Factored from the upstream L² identities during the Lean Pool port.
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The integral formula for the real L² norm

The general-measure identity is shared by compactness and bilinear-form estimates.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace EllipticPdes.Sobolev

/-- The squared `L²` norm of any class is the integral of its square. -/
lemma norm_sq_L2_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  simp_rw [pow_two]

end EllipticPdes.Sobolev
