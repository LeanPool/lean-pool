/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileTouching
public import Mathlib.Tactic.NormNum

-- [TABLET NODE: P5253T1OneEdgeInterface]

/-!
# P5253T1OneEdgeInterface

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5253T1OneEdgeInterface (T U : ProtoTile) (x y : GaussianInt)
    (hnT : T.cells.Nonempty) (hnU : U.cells.Nonempty)
    (hd : Disjoint T.cells U.cells)
    (hv : BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = {x, y})
    (heT : {x, y} ∈ BoundaryFootprintEdges T)
    (heU : {x, y} ∈ BoundaryFootprintEdges U)
    (ha : y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) :
    BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = {{x, y}} ∧
    SimpleGridPath {x, y} {{x, y}} ∧ TileTouching T U ∧ TileTouching U T := by
-- BODY
  classical
  have hxy : x ≠ y := by
    rcases ha with h | h | h | h <;>
      intro he <;> rw [← he] at h <;>
      have hr := congrArg Zsqrtd.re h <;>
      have hi := congrArg Zsqrtd.im h <;> simp at hr hi <;> omega
  have edges : BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = {{x, y}} := by
    ext e
    constructor
    · intro he
      have hc : e.card = 2 := by
        obtain ⟨z, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := he.1
        all_goals simp [Zsqrtd.ext_iff]
      have hs : e ⊆ {x, y} := by
        intro v hm
        have hb : v ∈ BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U := by
          constructor
          · rw [BoundaryFootprintVertices, ite_eq_left hnT]
            exact ⟨e, he.1, hm⟩
          · rw [BoundaryFootprintVertices, ite_eq_left hnU]
            exact ⟨e, he.2, hm⟩
        rw [hv] at hb
        simpa using hb
      exact Finset.eq_of_subset_of_card_le hs (by simp [hxy, hc])
    · rintro rfl
      exact ⟨heT, heU⟩
  have path : SimpleGridPath {x, y} {{x, y}} := by
    refine ⟨[x, y], by simp [hxy], by simp, by simp, ?_, ?_⟩
    · intro a b l₁ l₂ hl
      have llen := congrArg List.length hl
      simp only [List.length_cons, List.length_nil, List.length_append] at llen
      have h₁ : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
      have h₂ : l₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst l₁
      subst l₂
      simp only [List.nil_append, List.cons.injEq, and_true] at hl
      rcases hl with ⟨rfl, rfl⟩
      exact ha
    · intro e
      constructor
      · rintro rfl
        exact ⟨x, y, [], [], rfl, rfl⟩
      · rintro ⟨a, b, l₁, l₂, hl, rfl⟩
        have llen := congrArg List.length hl
        simp only [List.length_cons, List.length_nil, List.length_append] at llen
        have h₁ : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
        have h₂ : l₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst l₁
        subst l₂
        simp only [List.nil_append, List.cons.injEq, and_true] at hl
        rcases hl with ⟨rfl, rfl⟩
        rfl
  have p : SimpleGridPath (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U)
      (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) := by
    rw [hv, edges]
    exact path
  exact ⟨edges, path, Or.inl ⟨hnT, hnU, hd, p⟩,
    Or.inl ⟨hnU, hnT, hd.symm, by simpa only [Set.inter_comm] using p⟩⟩

end ApollonianSuperharmonic

end
