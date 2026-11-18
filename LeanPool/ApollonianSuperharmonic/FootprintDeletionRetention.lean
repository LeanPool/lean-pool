/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CellSupportedFootprintVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileCellComplement

-- [TABLET NODE: FootprintDeletionRetention]

/-!
# FootprintDeletionRetention

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FootprintDeletionRetention (A B O Y : ProtoTile)
    (hO : O.cells ⊆ A.cells)
    (hisolated : ∀ x ∈ CellSupportedFootprintVertices O,
      ∀ a : GaussianInt,
      x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) ->
        a ∈ A.cells ∨ a ∈ B.cells)
    (hYA : Disjoint Y.cells A.cells) (hYB : Disjoint Y.cells B.cells) :
    Disjoint (CellSupportedFootprintVertices Y)
        (CellSupportedFootprintVertices O) ∧
      FootprintEdges (TileCellComplement A O) ∩ FootprintEdges Y =
        FootprintEdges A ∩ FootprintEdges Y ∧
      (O.cells = ∅ ∨
          ((TileCellComplement A O).cells.Nonempty ∧ Y.cells.Nonempty) ->
        FootprintVertices (TileCellComplement A O) ∩ FootprintVertices Y =
          FootprintVertices A ∩ FootprintVertices Y) := by
-- BODY
  classical
  have singleton_corner {x a : GaussianInt}
      (hx : x = a ∨ x = a + 1 ∨ x = a + ⟨0, 1⟩ ∨
        x = a + 1 + ⟨0, 1⟩) :
      x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) := by
    simp only [FootprintVertices, Finset.singleton_nonempty, ite_true,
      Set.mem_ofPred_eq]
    exact ⟨a, Finset.mem_singleton_self a, hx⟩
  have hdisjoint : Disjoint (CellSupportedFootprintVertices Y)
      (CellSupportedFootprintVertices O) := by
    rw [Set.disjoint_left]
    intro x hxY hxO
    rcases hxY with ⟨a, haY, hxa⟩
    rcases hisolated x hxO a (singleton_corner hxa) with haA | haB
    · exact (Finset.disjoint_left.mp hYA haY) haA
    · exact (Finset.disjoint_left.mp hYB haY) haB
  have edge_endpoint_supported (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) :
      ∀ x ∈ e, x ∈ CellSupportedFootprintVertices T := by
    rcases he with ⟨a, ha, hshape⟩
    rcases hshape with hshape | hshape | hshape | hshape
    · intro x hx
      rw [hshape] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx <;> subst x
      · exact ⟨a, ha, Or.inl rfl⟩
      · exact ⟨a, ha, Or.inr (Or.inl rfl)⟩
    · intro x hx
      rw [hshape] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx <;> subst x
      · exact ⟨a, ha, Or.inl rfl⟩
      · exact ⟨a, ha, Or.inr (Or.inr (Or.inl rfl))⟩
    · intro x hx
      rw [hshape] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx <;> subst x
      · exact ⟨a, ha, Or.inr (Or.inl rfl)⟩
      · exact ⟨a, ha, Or.inr (Or.inr (Or.inr rfl))⟩
    · intro x hx
      rw [hshape] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx <;> subst x
      · exact ⟨a, ha, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨a, ha, Or.inr (Or.inr (Or.inr rfl))⟩
  have hedge :
      FootprintEdges (TileCellComplement A O) ∩ FootprintEdges Y =
        FootprintEdges A ∩ FootprintEdges Y := by
    ext e
    constructor
    · intro he
      rcases he with ⟨heAO, heY⟩
      refine ⟨?_, heY⟩
      rcases heAO with ⟨a, ha, hshape⟩
      exact ⟨a, (Finset.mem_sdiff.mp ha).1, hshape⟩
    · intro he
      rcases he with ⟨heA, heY⟩
      rcases heA with ⟨a, haA, hshape⟩
      have haO : a ∉ O.cells := by
        intro haO
        have heO : e ∈ FootprintEdges O := ⟨a, haO, hshape⟩
        have heNonempty : e.Nonempty := by
          rcases hshape with rfl | rfl | rfl | rfl <;> simp
        rcases heNonempty with ⟨x, hx⟩
        exact (Set.disjoint_left.mp hdisjoint
          (edge_endpoint_supported Y e heY x hx))
          (edge_endpoint_supported O e heO x hx)
      exact ⟨⟨a, Finset.mem_sdiff.mpr ⟨haA, haO⟩, hshape⟩, heY⟩
  refine ⟨hdisjoint, hedge, ?_⟩
  intro hsupport
  rcases hsupport with hOempty | ⟨hAO, hY⟩
  · have htile : TileCellComplement A O = A := by
      cases A
      cases O
      simp_all [TileCellComplement]
    rw [htile]
  · have footprint_eq_supported (T : ProtoTile) (hT : T.cells.Nonempty) :
        FootprintVertices T = CellSupportedFootprintVertices T := by
      simp [FootprintVertices, CellSupportedFootprintVertices, hT]
    rw [footprint_eq_supported _ hAO, footprint_eq_supported _ hY,
      footprint_eq_supported _ (by
        rcases hAO with ⟨a, ha⟩
        exact ⟨a, (Finset.mem_sdiff.mp ha).1⟩)]
    ext x
    constructor
    · intro hx
      rcases hx with ⟨⟨a, ha, hxa⟩, hxY⟩
      exact ⟨⟨a, (Finset.mem_sdiff.mp ha).1, hxa⟩, hxY⟩
    · intro hx
      rcases hx with ⟨⟨a, haA, hxa⟩, hxY⟩
      have haO : a ∉ O.cells := by
        intro haO
        exact (Set.disjoint_left.mp hdisjoint hxY) ⟨a, haO, hxa⟩
      exact ⟨⟨a, Finset.mem_sdiff.mpr ⟨haA, haO⟩, hxa⟩, hxY⟩

end ApollonianSuperharmonic

end
