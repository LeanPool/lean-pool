/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import LeanPool.AaronsonAmbainis.Row.Markov
public import LeanPool.AaronsonAmbainis.Row.Block

/-!
# The block inequality

`blockInequality : BlockInequality` is the block inequality (Lemma 6.4 of the paper). It follows
from `blockInequality_of_markov` (`Row/Block.lean`) and `markovEndpoint` (`Row/Markov.lean`).
-/

@[expose] public section

namespace AaronsonAmbainis

/-- The block inequality (`BlockInequality` of `RowDefs.lean`). -/
theorem blockInequality : BlockInequality := blockInequality_of_markov markovEndpoint

end AaronsonAmbainis
