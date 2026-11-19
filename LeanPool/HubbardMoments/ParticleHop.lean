/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # Hops of labelled hard-core particles -/

@[expose] public section

namespace HubbardMoments

/-- **One hop of labelled hard-core particles.** `pos p` is the site of particle `p`. One
particle `p` moves to a site `w` adjacent to its own that no particle occupies. A closed walk
of `h` hops is a sequence `walk 0, …, walk h` of positions, consecutive ones related by
`IsParticleHop`, whose final sites are a permutation `σ` of the initial ones:
`walk h p = walk 0 (σ p)`. -/
def IsParticleHop {P V : Type*} [DecidableEq P] (G : SimpleGraph V) (pos pos' : P → V) : Prop :=
  ∃ p w, G.Adj (pos p) w ∧ w ∉ Set.range pos ∧ pos' = Function.update pos p w

end HubbardMoments
