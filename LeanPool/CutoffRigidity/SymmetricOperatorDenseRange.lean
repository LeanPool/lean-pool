/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # Dense range of symmetric Hilbert-space operators -/

public section

namespace CutoffRigidity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An injective symmetric bounded operator on a real Hilbert space has dense range. -/
theorem denseRange_of_injective_symmetric (R : H →L[ℝ] H) (hR : Function.Injective R)
    (hsym : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) : DenseRange R := by
  change Dense (R.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hzero : R x = 0 := by
    apply ext_inner_right ℝ
    intro y
    rw [hsym]
    have hxy := ((R.range.mem_orthogonal x).mp hx) (R y) ⟨y, rfl⟩
    simpa only [inner_zero_left, real_inner_comm] using hxy
  exact hR (by simpa only [map_zero] using hzero)

end CutoffRigidity
