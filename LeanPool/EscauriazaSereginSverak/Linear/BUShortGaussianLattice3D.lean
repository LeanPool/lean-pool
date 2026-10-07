/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Three-dimensional Gaussian lattice

The product of three half-integer lattice Gaussians is summable.
-/

public section


noncomputable section

namespace ESS

/-- The three spatial grid coordinates as an integer triple. -/
@[expose] def buShortIntTripleEquiv : (Fin 3 → ℤ) ≃ (ℤ × ℤ × ℤ) where
  toFun m := (m 0, m 1, m 2)
  invFun p i := if i = 0 then p.1 else if i = 1 then p.2.1 else p.2.2
  left_inv m := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    rcases p with ⟨a, b, c⟩
    simp


end ESS
