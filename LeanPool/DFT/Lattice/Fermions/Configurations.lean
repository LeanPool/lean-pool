/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Basic.GroundState

/-!
# Spinless lattice fermions: configurations and occupations

`Conf M N`: `N`-element subsets of the sites `Fin M`; `occF i s`: occupation of site `i`.
-/

@[expose] public section

namespace DFT

section

open Matrix

variable {M N : ℕ}

/-- Configurations of `N` spinless fermions on `M` sites. -/
abbrev Conf (M N : ℕ) := {s : Finset (Fin M) // s.card = N}

/-- Occupation numbers. -/
def occF (i : Fin M) (s : Conf M N) : ℝ := if i ∈ s.1 then 1 else 0

end

end DFT
