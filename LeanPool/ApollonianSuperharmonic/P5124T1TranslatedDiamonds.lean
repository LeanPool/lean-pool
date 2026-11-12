/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5203T1IncreasingInterface
public import LeanPool.ApollonianSuperharmonic.P5203T1DecreasingInterface
public import LeanPool.ApollonianSuperharmonic.P5203T1CapInterface
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: P5124T1TranslatedDiamonds]

/-!
# P5124T1TranslatedDiamonds

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5124T1TranslatedDiamonds (k : Nat) (hk : 0 < k) :
    let D := DiamondTile k
    TouchingTriple D
      (TileTranslation D ⟨(k : Int) + 1, (k : Int)⟩)
      (TileTranslation D ⟨(k : Int) + 1, -(k : Int)⟩) ∧
    TouchingTriple D
      (TileTranslation D ⟨-(k : Int) - 1, (k : Int)⟩)
      (TileTranslation D ⟨0, 2 * (k : Int)⟩) ∧
    TouchingTriple D
      (TileTranslation D ⟨0, -(2 * (k : Int))⟩)
      (TileTranslation D ⟨-(k : Int) - 1, -(k : Int)⟩) := by
-- BODY
  classical
  let a : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
  let b : GaussianInt := ⟨(k : Int) + 1, -(k : Int)⟩
  let d : GaussianInt := ⟨0, 2 * (k : Int)⟩
  let T := fun u => TileTranslation (DiamondTile k) u
  have ba : b + d = a := by ext <;> simp [a, b, d]; ring
  have ma : -b + a = d := by ext <;> simp [a, b, d]; ring
  have mb : -a + b = -d := by ext <;> simp [a, b, d]; ring
  have touching (X Y : ProtoTile) (V : Set GaussianInt)
      (E : Set (Finset GaussianInt)) (hX : X.cells.Nonempty)
      (hY : Y.cells.Nonempty) (hd : Disjoint X.cells Y.cells)
      (hv : BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y = V)
      (he : BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y = E)
      (hp : SimpleGridPath V E) : TileTouching X Y ∧ TileTouching Y X := by
    have path : SimpleGridPath
        (BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)
        (BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y) := by
      rw [hv, he]
      exact hp
    exact ⟨Or.inl ⟨hX, hY, hd, path⟩,
      Or.inl ⟨hY, hX, hd.symm, by simpa only [Set.inter_comm] using path⟩⟩
  have increasing (u : GaussianInt) :
      TileTouching (T u) (T (u + b)) ∧ TileTouching (T (u + b)) (T u) := by
    obtain ⟨hX, hY, hd, hv, he, hp⟩ := P5203T1IncreasingInterface k hk u
    exact touching _ _ _ _ hX hY hd hv he hp
  have decreasing (u : GaussianInt) :
      TileTouching (T u) (T (u + a)) ∧ TileTouching (T (u + a)) (T u) := by
    obtain ⟨hX, hY, hd, hv, he, hp⟩ := P5203T1DecreasingInterface k hk u
    exact touching _ _ _ _ hX hY hd hv he hp
  have cap (u : GaussianInt) :
      TileTouching (T u) (T (u + d)) ∧ TileTouching (T (u + d)) (T u) := by
    obtain ⟨hX, hY, hd, hv, he, hp⟩ := P5203T1CapInterface k hk u
    exact touching _ _ _ _ hX hY hd hv he hp
  have vi (u z : GaussianInt) :
      (z ∈ BoundaryFootprintVertices (T u) ∧
        z ∈ BoundaryFootprintVertices (T (u + b))) ↔
      1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
        (z - u).re - 1 ≤ (z - u).im ∧ (z - u).im ≤ (z - u).re := by
    change z ∈ (BoundaryFootprintVertices (T u) ∩
      BoundaryFootprintVertices (T (u + b))) ↔ _
    rw [(P5203T1IncreasingInterface k hk u).2.2.2.1]
    rfl
  have vd (u z : GaussianInt) :
      (z ∈ BoundaryFootprintVertices (T u) ∧
        z ∈ BoundaryFootprintVertices (T (u + a))) ↔
      1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
        2 * (k : Int) ≤ (z - u).re + (z - u).im ∧
        (z - u).re + (z - u).im ≤ 2 * (k : Int) + 1 := by
    change z ∈ (BoundaryFootprintVertices (T u) ∩
      BoundaryFootprintVertices (T (u + a))) ↔ _
    rw [(P5203T1DecreasingInterface k hk u).2.2.2.1]
    rfl
  have vc (u z : GaussianInt) :
      (z ∈ BoundaryFootprintVertices (T u) ∧
        z ∈ BoundaryFootprintVertices (T (u + d))) ↔
      (z - u).im = 2 * (k : Int) ∧ -1 ≤ (z - u).re ∧ (z - u).re ≤ 1 := by
    change z ∈ (BoundaryFootprintVertices (T u) ∩
      BoundaryFootprintVertices (T (u + d))) ↔ _
    rw [(P5203T1CapInterface k hk u).2.2.2.1]
    rfl
  have row0 : TouchingTriple (T 0) (T a) (T b) := by
    refine ⟨by simpa only [zero_add] using (decreasing 0).1,
      by simpa only [ba] using (cap b).2,
      by simpa only [zero_add] using (increasing 0).2, ?_⟩
    refine ⟨⟨(k : Int), (k : Int)⟩, ?_, ?_⟩
    · have hA := (vd 0 ⟨(k : Int), (k : Int)⟩).mpr (by simp; omega)
      have hB := (vi 0 ⟨(k : Int), (k : Int)⟩).mpr (by simp; omega)
      exact ⟨hA.1, by simpa only [zero_add] using hA.2,
        by simpa only [zero_add] using hB.2⟩
    · intro z hz
      have hA := (vd 0 z).mp ⟨hz.1, by simpa only [zero_add] using hz.2.1⟩
      have hC := (vc b z).mp ⟨hz.2.2, by simpa only [ba] using hz.2.1⟩
      simp only [sub_zero, Zsqrtd.re_sub, Zsqrtd.im_sub, b] at hA hC
      apply Zsqrtd.ext <;> dsimp <;> omega
  have row1 : TouchingTriple (T 0) (T (-b)) (T d) := by
    refine ⟨by simpa only [neg_add_cancel] using (increasing (-b)).2,
      by simpa only [ma] using (decreasing (-b)).1,
      by simpa only [zero_add] using (cap 0).2, ?_⟩
    refine ⟨⟨-1, 2 * (k : Int)⟩, ?_, ?_⟩
    · have hA := (vi (-b) ⟨-1, 2 * (k : Int)⟩).mpr (by
        simp [b]; omega)
      have hC := (vc 0 ⟨-1, 2 * (k : Int)⟩).mpr (by simp)
      exact ⟨hC.1, hA.1, by simpa only [zero_add] using hC.2⟩
    · intro z hz
      have hA := (vi (-b) z).mp
        ⟨hz.2.1, by simpa only [neg_add_cancel] using hz.1⟩
      have hC := (vc 0 z).mp ⟨hz.1, by simpa only [zero_add] using hz.2.2⟩
      simp only [sub_zero, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_neg,
        Zsqrtd.im_neg, b] at hA hC
      apply Zsqrtd.ext <;> dsimp <;> omega
  have row2 : TouchingTriple (T 0) (T (-d)) (T (-a)) := by
    refine ⟨by simpa only [neg_add_cancel] using (cap (-d)).2,
      by simpa only [mb] using (increasing (-a)).2,
      by simpa only [neg_add_cancel] using (decreasing (-a)).1, ?_⟩
    refine ⟨⟨-1, 0⟩, ?_, ?_⟩
    · have hA := (vd (-a) ⟨-1, 0⟩).mpr (by simp [a]; omega)
      have hC := (vc (-d) ⟨-1, 0⟩).mpr (by simp [d])
      exact ⟨by simpa only [neg_add_cancel] using hC.2, hC.1, hA.1⟩
    · intro z hz
      have hA := (vd (-a) z).mp
        ⟨hz.2.2, by simpa only [neg_add_cancel] using hz.1⟩
      have hC := (vc (-d) z).mp
        ⟨hz.2.1, by simpa only [neg_add_cancel] using hz.1⟩
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_neg,
        Zsqrtd.im_neg, a, d] at hA hC
      apply Zsqrtd.ext <;> dsimp <;> omega
  have zero_tile : T 0 = DiamondTile k := by
    have hf : GaussianTranslation 0 = id := by
      funext z
      simp [GaussianTranslation]
    dsimp [T, TileTranslation]
    rw [hf, Finset.image_id]
    rfl
  have na : -a = (⟨-(k : Int) - 1, -(k : Int)⟩ : GaussianInt) := by
    ext <;> simp [a]; ring
  have nb : -b = (⟨-(k : Int) - 1, (k : Int)⟩ : GaussianInt) := by
    ext <;> simp [b]; ring
  have nd : -d = (⟨0, -(2 * (k : Int))⟩ : GaussianInt) := by
    ext <;> simp [d]
  simpa only [zero_tile, na, nb, nd, T, a, b, d] using
    And.intro row0 (And.intro row1 row2)

end ApollonianSuperharmonic

end
