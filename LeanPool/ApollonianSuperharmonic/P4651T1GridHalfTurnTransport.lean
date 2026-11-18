/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CentrallyReflectedAt
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.P3776T1CellCenterMembership

-- [TABLET NODE: P4651T1GridHalfTurnTransport]

/-!
# P4651T1GridHalfTurnTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4651T1GridHalfTurnTransport (c : Real × Real) (w : GaussianInt)
    (hw : GaussianRealPoint w = (2 * c.1, 2 * c.2))
    (S T : ProtoTile) (hS : S.cells.Nonempty) (hT : T.cells.Nonempty)
    (hR : CentrallyReflectedAt c S T) :
    T.cells = S.cells.image (fun t => w - t - 1 - ⟨0, 1⟩) ∧
    BoundaryFootprintEdges T =
      (fun e : Finset GaussianInt => e.image (fun z => w - z)) ''
        BoundaryFootprintEdges S ∧
    BoundaryFootprintVertices T =
      (fun z : GaussianInt => w - z) '' BoundaryFootprintVertices S := by
-- BODY
  classical
  let H : Real × Real → Real × Real := fun p => (2 * c.1 - p.1, 2 * c.2 - p.2)
  let r : GaussianInt → GaussianInt := fun z => w - z
  let f : GaussianInt → GaussianInt := fun t => w - t - 1 - ⟨0, 1⟩
  have hH (p : Real × Real) : H (H p) = p := by
    ext <;> dsimp [H] <;> ring
  have hr : Function.Involutive r := by intro z; dsimp [r]; abel
  have hf : Function.Involutive f := by intro z; dsimp [f]; abel
  have hmem (p : Real × Real) : p ∈ TileRealization S ↔ H p ∈ TileRealization T := by
    change TileRealization T = H '' TileRealization S at hR
    rw [hR]
    constructor
    · intro hp
      exact ⟨p, hp, rfl⟩
    · rintro ⟨q, hq, hqp⟩
      have heq : q = p := by
        have h := congrArg H hqp
        simpa only [hH] using h
      exact heq ▸ hq
  have center (q : GaussianInt) :
      H (GaussianRealPoint q + ((1 / 2, 1 / 2) : Real × Real)) =
        GaussianRealPoint (f q) + ((1 / 2, 1 / 2) : Real × Real) := by
    have hx := congrArg Prod.fst hw
    have hy := congrArg Prod.snd hw
    dsimp [GaussianRealPoint] at hx hy
    change (2 * c.1 - ((q.re : Real) + 1 / 2),
      2 * c.2 - ((q.im : Real) + 1 / 2)) =
      ((((w.re - q.re - 1 - 0 : Int) : Real) + 1 / 2),
        (((w.im - q.im - 0 - 1 : Int) : Real) + 1 / 2))
    push_cast
    exact Prod.ext (by linarith) (by linarith)
  have hcell (q : GaussianInt) : q ∈ S.cells ↔ f q ∈ T.cells := by
    rw [← P3776T1CellCenterMembership, ← P3776T1CellCenterMembership,
      hmem, center]
  have hback (q : GaussianInt) : q ∈ T.cells ↔ f q ∈ S.cells := by
    simpa only [hf q] using (hcell (f q)).symm
  have hcells : T.cells = S.cells.image f := by
    ext q
    constructor
    · intro hq
      exact Finset.mem_image.mpr ⟨f q, (hback q).mp hq, hf q⟩
    · rintro hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      exact (hcell x).mp hx
  have transport (A B : ProtoTile)
      (hc : ∀ q, q ∈ A.cells ↔ f q ∈ B.cells)
      (e : Finset GaussianInt) (he : e ∈ BoundaryFootprintEdges A) :
      e.image r ∈ BoundaryFootprintEdges B := by
    rcases he with ⟨z, ⟨rfl, hz⟩ | ⟨rfl, hz⟩⟩
    · refine ⟨w - z - 1, Or.inl ⟨?_, ?_⟩⟩
      · simp only [Finset.image_insert, Finset.image_singleton]
        change ({w - z, w - (z + 1)} : Finset GaussianInt) =
          {w - z - 1, w - z - 1 + 1}
        have h1 : w - (z + 1) = w - z - 1 := by abel
        have h2 : w - z - 1 + 1 = w - z := by abel
        rw [h1, h2, Finset.pair_comm]
      · have h1 : f (z - ⟨0, 1⟩) = w - z - 1 := by dsimp [f]; abel
        have h2 : f z = w - z - 1 - ⟨0, 1⟩ := rfl
        rw [← h2, ← h1, ← hc (z - ⟨0, 1⟩), ← hc z]
        exact hz.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)
    · refine ⟨w - z - ⟨0, 1⟩, Or.inr ⟨?_, ?_⟩⟩
      · simp only [Finset.image_insert, Finset.image_singleton]
        change ({w - z, w - (z + ⟨0, 1⟩)} : Finset GaussianInt) =
          {w - z - ⟨0, 1⟩, w - z - ⟨0, 1⟩ + ⟨0, 1⟩}
        have h1 : w - (z + ⟨0, 1⟩) = w - z - ⟨0, 1⟩ := by abel
        have h2 : w - z - ⟨0, 1⟩ + ⟨0, 1⟩ = w - z := by abel
        rw [h1, h2, Finset.pair_comm]
      · have h1 : f (z - 1) = w - z - ⟨0, 1⟩ := by dsimp [f]; abel
        have h2 : f z = w - z - ⟨0, 1⟩ - 1 := by dsimp [f]; abel
        rw [← h2, ← h1, ← hc (z - 1), ← hc z]
        exact hz.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)
  have heinv (e : Finset GaussianInt) : (e.image r).image r = e := by
    rw [Finset.image_image]
    have hid : r ∘ r = id := funext hr
    rw [hid, Finset.image_id]
  have hedges : BoundaryFootprintEdges T =
      (fun e : Finset GaussianInt => e.image r) '' BoundaryFootprintEdges S := by
    ext e
    constructor
    · intro he
      exact ⟨e.image r, transport T S hback e he, heinv e⟩
    · rintro ⟨d, hd, rfl⟩
      exact transport S T hcell d hd
  refine ⟨hcells, hedges, ?_⟩
  ext z
  simp only [BoundaryFootprintVertices, ite_eq_left hT, ite_eq_left hS, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, he, hze⟩
    rw [hedges] at he
    obtain ⟨d, hd, rfl⟩ := he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hze
    exact ⟨x, ⟨d, hd, hx⟩, rfl⟩
  · rintro ⟨x, ⟨e, he, hxe⟩, rfl⟩
    exact ⟨e.image r, hedges ▸ ⟨e, he, rfl⟩, Finset.mem_image.mpr ⟨x, hxe, rfl⟩⟩

end ApollonianSuperharmonic

end
