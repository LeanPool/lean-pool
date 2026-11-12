/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3102T2CommonEdgeSectorTransition
public import LeanPool.ApollonianSuperharmonic.CommonFootprintEdgeVertices
public import LeanPool.ApollonianSuperharmonic.FootprintVertices

-- [TABLET NODE: P3192T1FourOwnerTriangleExclusion]

/-!
# P3192T1FourOwnerTriangleExclusion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3192T1FourOwnerTriangleExclusion
    (T : Fin 4 → ProtoTile) (x : GaussianInt)
    (hne : ∀ i, (T i).cells.Nonempty)
    (hd : ∀ i j, i ≠ j → Disjoint (T i).cells (T j).cells)
    (hx : ∀ i, x ∈ FootprintVertices (T i)) :
    ¬ (x ∈ CommonFootprintEdgeVertices (T 0) (T 1) ∧
      x ∈ CommonFootprintEdgeVertices (T 1) (T 2) ∧
      x ∈ CommonFootprintEdgeVertices (T 2) (T 0)) := by
-- BODY
  classical
  have incident (i : Fin 4) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (T i).cells := by
    have h := hx i
    simp only [FootprintVertices, hne i, ite_true, Set.mem_ofPred_eq] at h
    rcases h with ⟨c, hc, h | h | h | h⟩
    · refine ⟨0, ?_⟩
      simpa [LatticeVertexIncidentCell] using h ▸ hc
    · refine ⟨1, ?_⟩
      subst x
      convert hc using 1; simp [LatticeVertexIncidentCell]
    · refine ⟨3, ?_⟩
      subst x
      convert hc using 1; simp [LatticeVertexIncidentCell]
    · refine ⟨2, ?_⟩
      change x - 1 - ⟨0, 1⟩ ∈ (T i).cells
      rw [h]
      convert hc using 1
      ext <;> simp
  choose sector hsector using incident
  have hinj : Function.Injective sector := by
    intro i j hij
    by_contra hneij
    exact Finset.disjoint_left.mp (hd i j hneij) (hsector i)
      (by simpa [hij] using hsector j)
  have hsurj : Function.Surjective sector := Finite.surjective_of_injective hinj
  have unique_sector (i j : Fin 4)
      (hc : LatticeVertexIncidentCell x j ∈ (T i).cells) : j = sector i := by
    obtain ⟨k, hk⟩ := hsurj j
    have hik : i = k := by
      by_contra hik
      exact Finset.disjoint_left.mp (hd i k hik) hc (by rw [← hk]; exact hsector k)
    simpa [← hik] using hk.symm
  have edge_sectors (i j : Fin 4) (hij : i ≠ j)
      (hxij : x ∈ CommonFootprintEdgeVertices (T i) (T j)) :
      sector j = sector i + 1 ∨ sector i = sector j + 1 := by
    obtain ⟨e, he, hxe⟩ := hxij
    obtain ⟨k, _, hk | hk⟩ := P3102T2CommonEdgeSectorTransition
      (T i) (T j) x e (hd i j hij) hxe he
    · left
      rw [← unique_sector i k hk.1, ← unique_sector j (k + 1) hk.2]
    · right
      rw [← unique_sector j k hk.1, ← unique_sector i (k + 1) hk.2]
  have no_triangle : ∀ a b c : Fin 4,
      (b = a + 1 ∨ a = b + 1) →
      (c = b + 1 ∨ b = c + 1) →
      (a = c + 1 ∨ c = a + 1) → False := by
    decide
  rintro ⟨h01, h12, h20⟩
  exact no_triangle (sector 0) (sector 1) (sector 2)
    (edge_sectors 0 1 (by decide) h01)
    (edge_sectors 1 2 (by decide) h12)
    (edge_sectors 2 0 (by decide) h20)

end ApollonianSuperharmonic

end
