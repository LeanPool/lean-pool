/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5253T1SingletonBoundary
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondVertexIncidence
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5253T1TopSquareContacts]

/-!
# P5253T1TopSquareContacts

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5253T1TopSquareContacts (k : Nat) (hk : 0 < k)
    (u : GaussianInt) (s : Int) (hs : s = -1 ∨ s = 0) :
    let D := TileTranslation (DiamondTile k) u
    let c := u + (⟨s, 2 * (k : Int)⟩ : GaussianInt)
    let U : ProtoTile := ⟨{c}, c⟩
    D.cells.Nonempty ∧ Disjoint D.cells U.cells ∧
      BoundaryFootprintVertices D ∩ BoundaryFootprintVertices U = {c, c + 1} ∧
      {c, c + 1} ∈ BoundaryFootprintEdges D := by
-- BODY
  classical
  let D := TileTranslation (DiamondTile k) u
  let c := u + (⟨s, 2 * (k : Int)⟩ : GaussianInt)
  have cell (z : GaussianInt) : z ∈ D.cells ↔
      0 ≤ (z - u).im ∧ (z - u).im < 2 * (k : Int) ∧
      -((z - u).im + 1) ≤ (z - u).re ∧ (z - u).re < (z - u).im + 1 ∧
      -(2 * (k : Int) - (z - u).im) ≤ (z - u).re ∧
        (z - u).re < 2 * (k : Int) - (z - u).im := by
    rw [← (P4194T1DiamondCellRows k (z - u)).1]
    change z ∈ (DiamondCellDomain k).image (GaussianTranslation u) ↔ _
    constructor
    · rintro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      simpa [GaussianTranslation] using hw
    · intro hz
      exact Finset.mem_image.mpr ⟨z - u, hz, by simp [GaussianTranslation]⟩
  have boundary (z : GaussianInt) : z ∈ BoundaryFootprintVertices D ↔
      (∃ j : Fin 4, LatticeVertexIncidentCell (z - u) j ∈ DiamondCellDomain k) ∧
      (∃ j : Fin 4, LatticeVertexIncidentCell (z - u) j ∉ DiamondCellDomain k) := by
    rw [show BoundaryFootprintVertices D =
      GaussianTranslation u '' BoundaryFootprintVertices (DiamondTile k) from
        (TileTranslationFormulas _ _).2.2.2.2.2.2.2.1]
    rw [← (P4194T1DiamondVertexIncidence k hk (z - u)).2]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [GaussianTranslation] using hw
    · intro hz
      exact ⟨z - u, hz, by simp [GaussianTranslation]⟩
  have bottom : c - ⟨0, 1⟩ ∈ D.cells := by
    rw [cell]
    simp only [c, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
    rcases hs with rfl | rfl <;> omega
  have outside : c ∉ D.cells := by
    rw [cell]
    simp only [c, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
    omega
  have hn : D.cells.Nonempty := ⟨_, bottom⟩
  have edge : {c, c + 1} ∈ BoundaryFootprintEdges D :=
    ⟨c, Or.inl ⟨rfl, Or.inr ⟨outside, bottom⟩⟩⟩
  have corners (z : GaussianInt) :
      z ∈ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) ↔
        z = c ∨ z = c + 1 := by
    rw [Set.mem_inter_iff, (P5253T1SingletonBoundary c c).1]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have b0 : c ∈ BoundaryFootprintVertices D := by
      rw [BoundaryFootprintVertices, ite_eq_left hn]
      exact ⟨_, edge, by simp⟩
    have b1 : c + 1 ∈ BoundaryFootprintVertices D := by
      rw [BoundaryFootprintVertices, ite_eq_left hn]
      exact ⟨_, edge, by simp⟩
    have no (v : GaussianInt) (hv : v.im = u.im + 2 * (k : Int) + 1) :
        v ∉ BoundaryFootprintVertices D := by
      rw [boundary]
      rintro ⟨⟨j, hj⟩, _⟩
      fin_cases j <;>
        simp only [LatticeVertexIncidentCell, (P4194T1DiamondCellRows _ _).1,
          ] at hj <;>
        norm_num at hj <;> omega
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim (no _ (by simp [c] ) hz)
      · exact False.elim (no _ (by simp [c] ) hz)
    · rintro (rfl | rfl) <;> simp [b0, b1]
  exact ⟨hn, Finset.disjoint_singleton_right.mpr outside, Set.ext corners, edge⟩

end ApollonianSuperharmonic

end
