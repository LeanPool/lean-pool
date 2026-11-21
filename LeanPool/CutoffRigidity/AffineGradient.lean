/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Gradients of affine functions on real Hilbert spaces -/

public section

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The pointwise gradient of an affine function is its coefficient vector. -/
theorem gradient_inner_add_const (a : E) (b : ℝ) (x : E) :
    gradient (fun y : E => inner ℝ a y + b) x = a := by
  have h : HasFDerivAt (fun y : E => inner ℝ a y + b) (innerSL ℝ a) x := by
    simpa only [innerSL_apply_apply] using (innerSL ℝ a).hasFDerivAt.add_const b
  have hlin : innerSL ℝ a = InnerProductSpace.toDual ℝ E a := by
    ext y
    rfl
  rw [hlin] at h
  exact (hasGradientAt_iff_hasFDerivAt.mpr h).gradient

end CutoffRigidity
