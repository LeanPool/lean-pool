/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import LeanPool.AaronsonAmbainis.Dual.RowAux
public import LeanPool.AaronsonAmbainis.Dual.Cover

/-!
# The row bound from the packing bound

`rowBoundPM_of_packing : PackingBound → RowBoundPM` (Theorem 6.8 of the paper from Lemma 6.5), by
`Dual.rowBoundPM_of_packing_of_cover` and `coverDuality`.
-/

@[expose] public section

namespace AaronsonAmbainis

theorem rowBoundPM_of_packing : PackingBound → RowBoundPM :=
  fun hPB => Dual.rowBoundPM_of_packing_of_cover hPB coverDuality

end AaronsonAmbainis
