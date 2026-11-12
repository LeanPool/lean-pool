/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: UnitTriangularStep]

/-!
# UnitTriangularStep

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
There are two positive triangular completions of the unit-square lattice.
For an orientation $\epsilon\in\{\mathsf{standard},\mathsf{rotated}\}$,
write $\operatorname{UnitStep}_{\epsilon}(v)$ when
$$
 v\in
 \begin{cases}
   \{\pm1,\pm i,\pm(1+i)\},&
      \epsilon=\mathsf{standard},\\
   \{\pm1,\pm i,\pm(-1+i)\},&
      \epsilon=\mathsf{rotated}.
 \end{cases}
$$
Thus each orientation selects exactly one six-neighbor triangular graph;
the union of the two graphs is not used as a tile-string adjacency graph.
-/
def UnitTriangularStep (orientation : Bool) (v : GaussianInt) : Prop :=
-- BODY
  v ∈ if orientation then
    ({1, -1, ⟨0, 1⟩, -⟨0, 1⟩,
      1 + ⟨0, 1⟩, -(1 + ⟨0, 1⟩)} : Finset GaussianInt)
  else
    ({1, -1, ⟨0, 1⟩, -⟨0, 1⟩,
      -1 + ⟨0, 1⟩, -(-1 + ⟨0, 1⟩)} : Finset GaussianInt)

end ApollonianSuperharmonic

end
