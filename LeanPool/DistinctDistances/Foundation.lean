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
configurations `Fin n → ℝ²`. Formal Conjectures defines the corresponding
finite-set minimum `Erdos98.h` in its
[formalization of Erdős Problem 98](https://github.com/google-deepmind/formal-conjectures/blob/7db2ea3b91bfbd0ab620215163e6c488bbb916d5/FormalConjectures/ErdosProblems/98.lean#L55-L62).
The comparison with `hIndexed` remains a separate formalization task.
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

The comparison with `Erdos98.h` from Formal Conjectures is not yet formalized. -/
noncomputable def hIndexed (n : ℕ) : ℕ := sInf {k : ℕ | ∃ p : Config n, Function.Injective p ∧
    InGeneralPosition (Config.toFinset p) ∧
    k = distinctDistances (Config.toFinset p)}

end Esgk
