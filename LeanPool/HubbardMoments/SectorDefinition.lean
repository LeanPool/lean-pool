/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Defs

/-! # Occupation sectors at fixed spin and doublon counts -/

@[expose] public section

namespace HubbardMoments

open Finset

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- The basis states with `a` up electrons, `b` down electrons and exactly `k` doubly
occupied sites, as pairs (up-occupied sites, down-occupied sites). A pair `(u, d)` of
subsets of the sites labels exactly one Fock basis state, so these pairs count the
states. -/
def sector (a b k : ℕ) : Finset (Finset V × Finset V) :=
  (powersetCard a univ ×ˢ powersetCard b univ).filter (fun p => (p.1 ∩ p.2).card = k)

end HubbardMoments
