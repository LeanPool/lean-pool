/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality

-- [TABLET NODE: ExactTileInterfaceTripleRetargetMiddle]

/-!
# ExactTileInterfaceTripleRetargetMiddle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ExactTileInterfaceTripleRetargetMiddle
    (A B B' C : ProtoTile)
    (hcells : B.cells = B'.cells)
    (hanchor : B.cells = ∅ → B.anchor = B'.anchor)
    (E : ExactTileInterfaceTriple A B C) :
    ∃ E' : ExactTileInterfaceTriple A B' C,
      E'.point = E.point ∧ E'.otherAB = E.otherAB ∧
      E'.otherBC = E.otherBC ∧ E'.otherCA = E.otherCA := by
-- BODY
  have hobs := ProtoTileObservableExtensionality B B' hcells hanchor
  have hedges : FootprintEdges B = FootprintEdges B' := by
    simp only [FootprintEdges]
    rw [hcells]
  let E' : ExactTileInterfaceTriple A B' C :=
    { point := E.point
      otherAB := E.otherAB
      otherBC := E.otherBC
      otherCA := E.otherCA
      pathAB := by simpa [hobs.1, hedges] using E.pathAB
      pathBC := by simpa [hobs.1, hedges] using E.pathBC
      pathCA := E.pathCA
      unique_common := by
        intro y
        simpa [hobs.1] using E.unique_common y }
  exact ⟨E', rfl, rfl, rfl, rfl⟩

end ApollonianSuperharmonic

end
