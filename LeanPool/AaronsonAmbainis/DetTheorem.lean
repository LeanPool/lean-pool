/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import LeanPool.AaronsonAmbainis.DetLow.Main
public import LeanPool.AaronsonAmbainis.DetBij.Main

/-!
# The determinant inequality, assembled

The determinant inequality (Corollary 3.2 of the paper), from the two halves of its proof:

* `AaronsonAmbainis.DetLow.lowestUnit`, `AaronsonAmbainis.DetLow.lowestBound`
  (directory `DetLow`),
* `AaronsonAmbainis.DetBij.detInequality_of_lowest` (directory `DetBij`).
-/

@[expose] public section

namespace AaronsonAmbainis

/-- The determinant inequality (Corollary 3.2 of the paper), with no hypothesis. -/
theorem detInequality : DetInequality :=
  DetBij.detInequality_of_lowest DetLow.lowestUnit DetLow.lowestBound

end AaronsonAmbainis
