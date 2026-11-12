/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileTouching

-- [TABLET NODE: TouchingTriple]

/-!
# TouchingTriple

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Three prototiles form a touching triple when every pair touches in the
extended sense of `TileTouching` and their three boundary footprints
have exactly one common vertex.  This includes triples containing an empty
anchored prototile, as required in the curvature-zero parent cases.
-/
def TouchingTriple (T₀ T₁ T₂ : ProtoTile) : Prop :=
-- BODY
  TileTouching T₀ T₁ ∧ TileTouching T₁ T₂ ∧
    TileTouching T₂ T₀ ∧
    ∃! x : GaussianInt,
      x ∈ BoundaryFootprintVertices T₀ ∧
        x ∈ BoundaryFootprintVertices T₁ ∧
        x ∈ BoundaryFootprintVertices T₂

end ApollonianSuperharmonic

end
