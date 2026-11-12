/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TileTouching
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import Mathlib.Init


/-!
# Observable tile retargeting

Touching depends on cell sets and, for empty tiles, their anchors.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace ObservableTileRetargeting

/-- Retarget a touching pair along equal observable tile data. -/
theorem tile (A A' B B' : ProtoTile) (hAc : A.cells = A'.cells)
    (hAa : A.cells = ∅ → A.anchor = A'.anchor) (hBc : B.cells = B'.cells)
    (hBa : B.cells = ∅ → B.anchor = B'.anchor) (ht : TileTouching A B) :
    TileTouching A' B' := by
  classical
  have hAo := ProtoTileObservableExtensionality A A' hAc hAa
  have hBo := ProtoTileObservableExtensionality B B' hBc hBa
  rcases ht with ht | ht | ht
  · left
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hAc] using ht.1
    · simpa [hBc] using ht.2.1
    · simpa [hAc, hBc] using ht.2.2.1
    · simpa [hAo.2.1, hAo.2.2.1, hBo.2.1, hBo.2.2.1] using ht.2.2.2
  · right; left
    refine ⟨?_, ?_⟩
    · simpa [hAc] using ht.1
    · rw [← hAa ht.1, ← hBo.2.1]
      exact ht.2
  · right; right
    refine ⟨?_, ?_⟩
    · simpa [hBc] using ht.1
    · rw [← hBa ht.1, ← hAo.2.1]
      exact ht.2

/-- Retarget a touching triple along equal observable tile data. -/
theorem triple (A A' B B' D D' : ProtoTile) (hAc : A.cells = A'.cells)
    (hAa : A.cells = ∅ → A.anchor = A'.anchor) (hBc : B.cells = B'.cells)
    (hBa : B.cells = ∅ → B.anchor = B'.anchor) (hDc : D.cells = D'.cells)
    (hDa : D.cells = ∅ → D.anchor = D'.anchor) (ht : TouchingTriple A B D) :
    TouchingTriple A' B' D' := by
  classical
  have hAo := ProtoTileObservableExtensionality A A' hAc hAa
  have hBo := ProtoTileObservableExtensionality B B' hBc hBa
  have hDo := ProtoTileObservableExtensionality D D' hDc hDa
  rcases ht with ⟨hAB, hBD, hDA, p, hp, hpu⟩
  refine ⟨tile A A' B B' hAc hAa hBc hBa hAB,
    tile B B' D D' hBc hBa hDc hDa hBD,
    tile D D' A A' hDc hDa hAc hAa hDA, p, ?_, ?_⟩
  · simpa [← hAo.2.1, ← hBo.2.1, ← hDo.2.1] using hp
  · intro y hy
    apply hpu y
    simpa [← hAo.2.1, ← hBo.2.1, ← hDo.2.1] using hy

end ObservableTileRetargeting
end ApollonianSuperharmonic

end
