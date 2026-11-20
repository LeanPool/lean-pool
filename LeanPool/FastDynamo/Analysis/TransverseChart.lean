/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Conventions

/-!
# The quotient map from the Euclidean plane to the transverse two-torus

`TransverseTorus = Torus 2` is the coordinatewise quotient `(ℝ / ℤ)²`.  This module defines the
single canonical projection `transverseTorusPoint : ℝ × ℝ → TransverseTorus` used by the whole
development, together with its two coordinate `simp` lemmas.

The map is needed at two ends of the import graph that have no other module in common: the
velocity-construction layer (`Global/TorusChartEmbedding.lean` and everything downstream of it,
where it transports the Euclidean placement chart into the torus) and the literal-three-torus
dictionary (`Analysis/LiteralThreeTorus.lean`, where it is the quotient map a `ℤ²`-periodic field
descends along).  Keeping the definition here — above both — is what stops the two layers from
each introducing their own copy.

Nothing beyond the conventions of `FastDynamo/Conventions.lean` is used, so this module sits at
the very bottom of the library.
-/

@[expose] public section

namespace FastDynamo

/-- Coordinatewise quotient map from the Euclidean transverse chart to the normalized additive
two-torus. -/
def transverseTorusPoint (x : ℝ × ℝ) : TransverseTorus :=
  fun i => if i = 0 then (x.1 : UnitAddCircle) else (x.2 : UnitAddCircle)

/-- First quotient coordinate of a charted point: `transverseTorusPoint x` has zeroth coordinate
the class of `x.1` in `ℝ / ℤ`. -/
@[simp] theorem transverseTorusPoint_zero (x : ℝ × ℝ) :
    transverseTorusPoint x 0 = (x.1 : UnitAddCircle) := by
  simp [transverseTorusPoint]

/-- Second quotient coordinate of a charted point: `transverseTorusPoint x` has first coordinate
the class of `x.2` in `ℝ / ℤ`. -/
@[simp] theorem transverseTorusPoint_one (x : ℝ × ℝ) :
    transverseTorusPoint x 1 = (x.2 : UnitAddCircle) := by
  simp [transverseTorusPoint]

end FastDynamo
