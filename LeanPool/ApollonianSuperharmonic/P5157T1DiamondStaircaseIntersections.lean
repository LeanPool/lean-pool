/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5250T1SeparatedCells
public import LeanPool.ApollonianSuperharmonic.P5250T1CommonVertices
public import LeanPool.ApollonianSuperharmonic.P5250T1ConsecutiveEdges
public import LeanPool.ApollonianSuperharmonic.P5250T1RankedCommonEdges

-- [TABLET NODE: P5157T1DiamondStaircaseIntersections]

/-!
# P5157T1DiamondStaircaseIntersections

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5157T1DiamondStaircaseIntersections (k : Nat) (hk : 1 < k) :
    let D := DiamondTile k
    let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
    let Eplus := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
    let Eminus := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
    let N := 2 * (k - 1)
    let p := P5157T1StaircasePoint 1 false 1
    let q := P5157T1StaircasePoint 1 false (-1)
    let r := P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1)
    (Disjoint D.cells Eplus.cells ∧
      BoundaryFootprintVertices D ∩ BoundaryFootprintVertices Eplus =
        {v | ∃ j ≤ N, v = p j} ∧
      BoundaryFootprintEdges D ∩ BoundaryFootprintEdges Eplus =
        {e | ∃ j < N, e = {p j, p (j + 1)}}) ∧
    (Disjoint L.cells Eplus.cells ∧
      BoundaryFootprintVertices L ∩ BoundaryFootprintVertices Eplus =
        {v | ∃ j ≤ N, v = q j} ∧
      BoundaryFootprintEdges L ∩ BoundaryFootprintEdges Eplus =
        {e | ∃ j < N, e = {q j, q (j + 1)}}) ∧
    (Disjoint D.cells Eminus.cells ∧
      BoundaryFootprintVertices D ∩ BoundaryFootprintVertices Eminus =
        {v | ∃ j ≤ N, v = r j} ∧
      BoundaryFootprintEdges D ∩ BoundaryFootprintEdges Eminus =
        {e | ∃ j < N, e = {r j, r (j + 1)}}) := by
-- BODY
  classical
  have ne (m : Nat) (hm : 0 < m) : (DiamondTile m).cells.Nonempty := by
    refine ⟨0, (P4194T1DiamondCellRows m 0).1.mpr ?_⟩
    norm_num
    omega
  have neTr (m : Nat) (hm : 0 < m) (u : GaussianInt) :
      (TileTranslation (DiamondTile m) u).cells.Nonempty := by
    rw [(TileTranslationFormulas (DiamondTile m) u).1]
    exact (ne m hm).image _
  have edges (X Y : ProtoTile) (hX : X.cells.Nonempty) (hY : Y.cells.Nonempty)
      (f : Nat → GaussianInt) (N : Nat) (s c : Int) (hs : s = 1 ∨ s = -1)
      (hV : BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y =
        {v | ∃ j ≤ N, v = f j})
      (hE : ∀ j < N, ({f j, f (j + 1)} : Finset GaussianInt) ∈
        BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y)
      (hrank : ∀ j ≤ N, (f j).re + s * (f j).im + c = (j : Int)) :
      BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y =
        {e | ∃ j < N, e = {f j, f (j + 1)}} := by
    apply Set.Subset.antisymm
    · exact P5250T1RankedCommonEdges X Y hX hY f N s c hs hV hrank
    · rintro e ⟨j, hj, rfl⟩
      exact hE j hj
  have disj := P5250T1SeparatedCells k hk
  have vertices := P5250T1CommonVertices k hk
  have actual := P5250T1ConsecutiveEdges k hk
  dsimp only at disj vertices actual ⊢
  refine ⟨⟨disj.1, vertices.1, ?_⟩,
    ⟨disj.2.1, vertices.2.1, ?_⟩, ⟨disj.2.2, vertices.2.2, ?_⟩⟩
  · apply edges _ _ (ne k (by omega)) (neTr (k - 1) (by omega) _)
      _ _ 1 (-1) (Or.inl rfl) vertices.1 actual.1
    intro j hj
    simp [P5157T1StaircasePoint]
    omega
  · apply edges _ _ (neTr k (by omega) _) (neTr (k - 1) (by omega) _)
      _ _ (-1) (-1) (Or.inr rfl) vertices.2.1 actual.2.1
    intro j hj
    simp [P5157T1StaircasePoint]
    omega
  · apply edges _ _ (ne k (by omega)) (neTr (k - 1) (by omega) _)
      _ _ (-1) (2 * (k : Int) - 1) (Or.inr rfl) vertices.2.2 actual.2.2
    intro j hj
    simp [P5157T1StaircasePoint]
    omega

end ApollonianSuperharmonic

end
