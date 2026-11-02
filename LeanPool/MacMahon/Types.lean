/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod

/-!
# Finite domains for coloured cubes
-/

@[expose] public section
namespace MacMahon

/-- Conway tableau labels, distinct from the six face colours. -/
abbrev Label := Fin 6
/-- Ordered coordinates in Conway's tableau; diagonal entries are reserved. -/
abbrev Pair := Label × Label
/-- The forty oriented corner types formed from the six distinct face colours. -/
abbrev Corner := Fin 40
/-- The eight positions in a two-by-two-by-two assembly. -/
abbrev Slot := Fin 8
/-- Natural-number multiplicities of the tableau entries. -/
abbrev Inventory := Pair → ℕ

end MacMahon
