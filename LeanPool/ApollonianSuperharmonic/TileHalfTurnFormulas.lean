/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileHalfTurn
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: TileHalfTurnFormulas]

/-!
# TileHalfTurnFormulas

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileHalfTurnFormulas : ∀ T : ProtoTile,
    (TileHalfTurn T).cells =
      T.cells.image (fun x => -x - 1 - ⟨0, 1⟩) ∧
    (TileHalfTurn T).anchor =
      (if T.cells.Nonempty then -T.anchor - 1 - ⟨0, 1⟩ else -T.anchor) ∧
    ((TileHalfTurn T).cells = ∅ ↔ T.cells = ∅) ∧
    TileHalfTurn (TileHalfTurn T) = T ∧
    (TileHalfTurn T).cells =
      (TileQuarterTurn (TileQuarterTurn T)).cells ∧
    TileRealization (TileHalfTurn T) =
      (fun p : Real × Real => (-p.1, -p.2)) '' TileRealization T ∧
    FootprintVertices (TileHalfTurn T) =
      (fun x : GaussianInt => -x) '' FootprintVertices T ∧
    TileCentroid (TileHalfTurn T) =
      (-(TileCentroid T).1, -(TileCentroid T).2) ∧
    (T.cells = ∅ →
      TileHalfTurn T = TileQuarterTurn (TileQuarterTurn T)) := by
-- BODY
  intro T
  have gaussian_equal (u v : GaussianInt) (hre : u.re = v.re)
      (him : u.im = v.im) : u = v := by
    rcases u with ⟨u, w⟩
    rcases v with ⟨v, z⟩
    simp_all
  have half_map (x : GaussianInt) : -(-x - 1 - ⟨0, 1⟩) - 1 - ⟨0, 1⟩ = x := by
    apply gaussian_equal <;> simp
  have half_anchor (a : GaussianInt) : -(-a) = a := by
    apply gaussian_equal <;> simp
  have quarter_twice (x : GaussianInt) :
      GaussianQuarterTurn (GaussianQuarterTurn x - 1) - 1 =
        -x - 1 - ⟨0, 1⟩ := by
    apply gaussian_equal <;> simp [GaussianQuarterTurn]
  have quarter_anchor (a : GaussianInt) :
      GaussianQuarterTurn (GaussianQuarterTurn a) = -a := by
    apply gaussian_equal <;> simp [GaussianQuarterTurn]
  have image_empty (s : Finset GaussianInt) :
      s.image (fun x => -x - 1 - ⟨0, 1⟩) = ∅ ↔ s = ∅ := by
    exact Finset.image_eq_empty.trans (by simp [])
  have proto_equal (A B : ProtoTile) (hc : A.cells = B.cells)
      (ha : A.anchor = B.anchor) : A = B := by
    cases A
    cases B
    simp_all
  have cell_half_quarter :
      (TileHalfTurn T).cells = (TileQuarterTurn (TileQuarterTurn T)).cells := by
    simp only [TileHalfTurn, TileQuarterTurn, Finset.image_image]
    apply Finset.image_congr
    intro x hx
    exact (quarter_twice x).symm
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact image_empty T.cells
  constructor
  · apply proto_equal
    · simp only [TileHalfTurn, Int.reduceNeg, Finset.image_nonempty]
      change (T.cells.image (fun x => -x - 1 - ⟨0, 1⟩)).image
        (fun x => -x - 1 - ⟨0, 1⟩) = T.cells
      rw [Finset.image_image]
      rw [show (fun x : GaussianInt => -x - 1 - (⟨0, 1⟩ : GaussianInt)) ∘
          (fun x : GaussianInt => -x - 1 - (⟨0, 1⟩ : GaussianInt)) =
          (fun x : GaussianInt => x) by
        funext x
        simpa [Function.comp_def] using half_map x]
      simp
    · by_cases h : T.cells.Nonempty
      · have hi : (T.cells.image (fun x => -x - 1 - ⟨0, 1⟩)).Nonempty :=
          h.image _
        simpa [TileHalfTurn, h, hi] using half_map T.anchor
      · simp [TileHalfTurn, h, half_anchor]
  constructor
  · exact cell_half_quarter
  constructor
  · rw [show TileRealization (TileHalfTurn T) =
        TileRealization (TileQuarterTurn (TileQuarterTurn T)) by
      simp [TileRealization, cell_half_quarter]]
    rw [(TileQuarterTurnFormulas (TileQuarterTurn T)).2.2.2.1,
      (TileQuarterTurnFormulas T).2.2.2.1]
    ext p
    simp [Set.image_image]
  constructor
  · have hverts : FootprintVertices (TileHalfTurn T) =
        FootprintVertices (TileQuarterTurn (TileQuarterTurn T)) := by
      by_cases h : T.cells.Nonempty
      · have hq : (TileQuarterTurn (TileQuarterTurn T)).cells.Nonempty := by
          rw [← cell_half_quarter]
          simp [TileHalfTurn, h]
        simp [FootprintVertices, hq, cell_half_quarter]
      · have he : T.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        simp [FootprintVertices, he, TileHalfTurn,
          TileQuarterTurn, quarter_anchor]
    rw [hverts, (TileQuarterTurnFormulas (TileQuarterTurn T)).2.2.2.2.2.1,
      (TileQuarterTurnFormulas T).2.2.2.2.2.1]
    ext v
    simp [Set.image_image, quarter_anchor]
  constructor
  · by_cases h : T.cells.Nonempty
    · have hq : (TileQuarterTurn (TileQuarterTurn T)).cells.Nonempty := by
        rw [← cell_half_quarter]
        simp [TileHalfTurn, h]
      have hc : TileCentroid (TileHalfTurn T) =
          TileCentroid (TileQuarterTurn (TileQuarterTurn T)) := by
        simp [TileCentroid, hq, cell_half_quarter]
      change TileCentroid (TileHalfTurn T) =
        (-(TileCentroid T).1, -(TileCentroid T).2)
      rw [hc, (TileQuarterTurnFormulas (TileQuarterTurn T)).2.2.2.2.1,
        (TileQuarterTurnFormulas T).2.2.2.2.1]
    · have he : (TileHalfTurn T).cells = ∅ := by
        have hz : T.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        simp [TileHalfTurn, hz]
      have hz : T.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [TileCentroid, hz, TileHalfTurn]
  · intro h
    apply proto_equal
    · exact cell_half_quarter
    · simp [TileHalfTurn, TileQuarterTurn, h, quarter_anchor]

end ApollonianSuperharmonic

end
