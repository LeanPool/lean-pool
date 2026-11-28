/-
Copyright (c) 2025 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Formal Conjectures' closed invariant subspaces

Formal Conjectures' structure `ClosedInvariantSubspace`, copied verbatim from
`FormalConjectures/Wikipedia/InvariantSubspaceProblem.lean` at commit
`40a8592cb6f7e96cb9a8275d96bb3e013feeb1dc`. The imports and file header were adapted for Lean Pool.
-/

@[expose] public section

namespace InvariantSubspaceProblem

variable {H : Type*} [NormedAddCommGroup H]

/-- `ClosedInvariantSubspace T` is the type of non-trivial (different from `H` and `{0}`) closed
subspaces of a complex vector space `H` that are invariant under the action of linear map `T`. -/
structure ClosedInvariantSubspace [Module ℂ H] (T : H →L[ℂ] H) where
  /-- The closed, nontrivial subspace carried by this witness. -/
  toSubspace : Submodule ℂ H
  ne_bot : toSubspace ≠ ⊥
  ne_top : toSubspace ≠ ⊤
  is_closed : IsClosed (toSubspace : Set H)
  is_fixed : toSubspace.map T.toLinearMap ≤ toSubspace

end InvariantSubspaceProblem
