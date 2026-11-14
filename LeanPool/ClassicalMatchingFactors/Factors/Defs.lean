/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
/-!

Imported from [jtraverso/tutte-f-factor](https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorDefs.lean), registered as PALOMAR-2026-10-18-000005. The original proof is retained; module paths and imports are adapted for this collection.

# The odd-component count in Tutte's f-factor criterion

The necessity and sufficiency proofs use this same definition as the final criterion.
-/

@[expose] public section

open Finset SimpleGraph

namespace FFactor

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- Number of components of `G - (S ∪ T)` for which the degree sum plus the edges to `T` is odd. -/
noncomputable def oddCount (G : SimpleGraph V) (f : V → ℕ) (S T : Finset V) : ℕ :=
  Nat.card {c : (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).ConnectedComponent //
    Odd (∑ w ∈ univ.filter (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) =>
        (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ T | G.Adj w t}))}

end FFactor
