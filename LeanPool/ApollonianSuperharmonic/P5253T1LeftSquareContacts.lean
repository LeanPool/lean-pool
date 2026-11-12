/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5253T1SingletonBoundary
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondVertexIncidence
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5253T1LeftSquareContacts]

/-!
# P5253T1LeftSquareContacts

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5253T1LeftSquareContacts (k : Nat) (hk : 0 < k)
    (u : GaussianInt) (h : Int) (hh : h = (k : Int) - 1 ∨ h = k) :
    let D := TileTranslation (DiamondTile k) u
    let c := u + (⟨-(k : Int) - 1, h⟩ : GaussianInt)
    let U : ProtoTile := ⟨{c}, c⟩
    D.cells.Nonempty ∧ Disjoint D.cells U.cells ∧
      BoundaryFootprintVertices D ∩ BoundaryFootprintVertices U =
        {c + 1, c + 1 + ⟨0, 1⟩} ∧
      {c + 1, c + 1 + ⟨0, 1⟩} ∈ BoundaryFootprintEdges D := by
-- BODY
  classical
  let D := TileTranslation (DiamondTile k) u
  let c := u + (⟨-(k : Int) - 1, h⟩ : GaussianInt)
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
  have inside : c + 1 ∈ D.cells := by
    rw [cell]
    simp only [c, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one]
    rcases hh with rfl | rfl <;> omega
  have outside : c ∉ D.cells := by
    rw [cell]
    simp only [c, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
    omega
  have hn : D.cells.Nonempty := ⟨_, inside⟩
  have edge : {c + 1, c + 1 + ⟨0, 1⟩} ∈ BoundaryFootprintEdges D := by
    refine ⟨c + 1, Or.inr ⟨rfl, Or.inl ⟨inside, ?_⟩⟩⟩
    simpa using outside
  have no (v : GaussianInt) (hv : (v - u).re = -(k : Int) - 1) :
      v ∉ BoundaryFootprintVertices D := by
    simp only [Zsqrtd.re_sub] at hv
    rw [(TileTranslationFormulas _ _).2.2.2.2.2.2.2.1]
    rintro ⟨w, hw, heq⟩
    have hwv : w = v - u := (eq_sub_iff_add_eq).mpr heq
    rw [hwv, (P4194T1DiamondVertexIncidence k hk (v - u)).2] at hw
    obtain ⟨⟨j, hj⟩, _⟩ := hw
    fin_cases j <;>
      simp only [LatticeVertexIncidentCell, (P4194T1DiamondCellRows _ _).1,
        ] at hj <;>
      norm_num at hj <;> omega
  have vertices : BoundaryFootprintVertices D ∩
      BoundaryFootprintVertices (⟨{c}, c⟩ : ProtoTile) =
        {c + 1, c + 1 + ⟨0, 1⟩} := by
    ext v
    rw [Set.mem_inter_iff, (P5253T1SingletonBoundary c c).1]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hv, rfl | rfl | rfl | rfl⟩
      · exact False.elim (no _ (by simp [c]) hv)
      · exact Or.inl rfl
      · exact False.elim (no _ (by simp [c]) hv)
      · exact Or.inr rfl
    · intro hv
      have hb : v ∈ BoundaryFootprintVertices D := by
        rw [BoundaryFootprintVertices, ite_eq_left hn]
        exact ⟨_, edge, by simpa using hv⟩
      exact ⟨hb, by tauto⟩
  exact ⟨hn, Finset.disjoint_singleton_right.mpr outside, vertices, edge⟩

end ApollonianSuperharmonic

end
