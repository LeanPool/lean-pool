/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Topology.Order.Basic
public import Mathlib.Logic.Function.Iterate

/-! # Local stable and unstable sets of an iterated map -/

@[expose] public section

open Filter Topology

namespace Function

variable {X : Type*} [TopologicalSpace X]

/-- The **local stable set** of `f|_U` at `p`: the points `x` whose forward orbit `fⁿ(x)` stays in
`U` and tends to `p`. (For the iterates of `f|_U` to be defined the orbit must stay in `U`.) -/
def localStableSet (f : X → X) (p : X) (U : Set X) : Set X :=
  {x | (∀ n : ℕ, f^[n] x ∈ U) ∧ Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)}

/-- The **local unstable set** of `f|_U` at `p`: the points `x` having a backward orbit `y`
(`y 0 = x`, `f (y (n + 1)) = y n`) in `U` that tends to `p`. For an `f` invertible on `U` it is the
local stable set of `f⁻¹|_U`. -/
def localUnstableSet (f : X → X) (p : X) (U : Set X) : Set X :=
  {x | ∃ y : ℕ → X, y 0 = x ∧ (∀ n, y n ∈ U ∧ f (y (n + 1)) = y n) ∧ Tendsto y atTop (𝓝 p)}

end Function
