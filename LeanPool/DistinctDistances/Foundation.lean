/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import LeanPool.DistinctDistances.PlanarGeneralPosition

/-!
# Foundation — proof-local indexed primitives.

Defines `Point`, `Config`, `Config.toFinset`, and the proof-local minimum
`hIndexed`. The energy decomposition is naturally stated over function-indexed
configurations `Fin n → ℝ²`. The canonical Problem 98 function is
`Erdos98.h` in the `LeanFormalizations` dependency and is stated over finite
sets. This repository does not yet contain the adapter identifying `hIndexed`
with `Erdos98.h`; that adapter is an explicit remaining formalization task.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

/-- Alias for the ambient plane in this problem. -/
abbrev Point : Type := ℝ²

/-- An indexed configuration of `n` points in the plane. -/
abbrev Config (n : ℕ) : Type := Fin n → Point

/-- Image-finset of an indexed configuration: the set of points that appear in `p`. -/
noncomputable def Config.toFinset {n : ℕ} (p : Config n) : Finset Point :=
  Finset.image p Finset.univ

/-- Proof-local indexed minimum distinct-distance count over general-position configurations.

The comparison with the canonical `Erdos98.h` is not yet formalized. -/
noncomputable def hIndexed (n : ℕ) : ℕ := sInf {k : ℕ | ∃ p : Config n, Function.Injective p ∧
    InGeneralPosition (Config.toFinset p) ∧
    k = distinctDistances (Config.toFinset p)}

end Esgk
