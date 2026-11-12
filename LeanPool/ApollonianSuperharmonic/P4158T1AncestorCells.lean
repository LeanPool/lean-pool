/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AncestorTile
public import LeanPool.ApollonianSuperharmonic.BandPrototileReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique

-- [TABLET NODE: P4158T1AncestorCells]

/-!
# P4158T1AncestorCells

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4158T1AncestorCells
    (C D : CircleCoordinates) (U T : ProtoTile)
    (h : AncestorTile C D U T) : U.cells ⊆ T.cells := by
-- BODY
  change Relation.ReflTransGen _ (C, U) (D, T) at h
  generalize hCU : (C, U) = X at h
  generalize hDT : (D, T) = Y at h
  have hcells : X.2.cells ⊆ Y.2.cells := by
    clear hCU hDT
    induction h using Relation.ReflTransGen.trans_induction_on with
    | refl X => exact Finset.Subset.refl _
    | @single X Y hstep =>
        obtain ⟨q, i, s, hq, hY, hX, hTY, hUX, _, hcent⟩ := hstep
        obtain ⟨S, hS, hcover⟩ := BandPrototileReindexedDecomposition q hq Y.2
          (by simpa only [hY] using hTY)
        have hinner : BandPrototile (q i.succ) X.2 := by
          simpa only [hX] using hUX
        have hsame : X.2.cells = (S i s).cells :=
          (BandPrototileCentroidUnique (q i.succ) X.2 (S i s) hinner
            (hS i s).1 (by
              have heq := hcent.trans (hS i s).2.2.symm
              simpa only [sub_add_cancel] using
                congrArg (fun p => p + TileCentroid Y.2) heq)).1
        intro z hz
        exact (hcover z).2 ⟨i, s, hsame ▸ hz⟩
    | trans _ _ hfirst hsecond => exact Finset.Subset.trans hfirst hsecond
  simpa only [← hCU, ← hDT] using hcells

end ApollonianSuperharmonic

end
