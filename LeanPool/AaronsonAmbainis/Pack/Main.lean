/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import LeanPool.AaronsonAmbainis.Pack.Packing

/-!
# From the block inequality to the packing bound

* `AaronsonAmbainis.packingBound_of_block : BlockInequality → PackingBound`
  (Lemma 6.5 of the paper from Lemma 6.4; the proof is in `Pack/Packing.lean`)
-/

@[expose] public section
