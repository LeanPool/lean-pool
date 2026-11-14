/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.FinCases

public import LeanPool.ApollonianSuperharmonic.P3767T1FixedTrace
public import LeanPool.ApollonianSuperharmonic.P3767T1BarrierRegionMaximal
public import LeanPool.ApollonianSuperharmonic.P3767T1VertexEdgeIncidence

-- [TABLET NODE: P3767T1FixedFaceComponents]

/-!
# P3767T1FixedFaceComponents

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3767T1FixedFaceComponents {ι : Type} [Nontrivial ι]
    (P : PlaneTriangulation ι) :
    (∀ f, Disjoint (P3767T1FixedTrace P) (P.faceRegion f) ∧
      frontier (P.faceRegion f) ⊆ P3767T1FixedTrace P) ∧
    (∀ f (V : Set (Real × Real)), IsPreconnected V →
      Disjoint V (frontier (P.faceRegion f)) →
      (V ∩ P.faceRegion f).Nonempty → V ⊆ P.faceRegion f) ∧
    (P3767T1FixedTrace P)ᶜ = {x | ∃ f, x ∈ P.faceRegion f} := by
-- BODY
  have hfrontier (f g : P.Face) :
      Disjoint (frontier (P.faceRegion g)) (P.faceRegion f) := by
    by_cases h : g = f
    · subst g
      exact (disjoint_frontier_iff_isOpen).mpr (P.region_open f)
    · exact (P.region_disjoint h).frontier_left (P.region_open f)
  have hedge (f : P.Face) (a b : ι) (hab : P.adjacent a b) :
      Disjoint (P.edgeArc a b) (P.faceRegion f) := by
    obtain ⟨g, _, _, hg, _, _⟩ := P.every_edge_two_faces a b hab
    obtain ⟨i, hi⟩ := hg.1
    obtain ⟨j, hj⟩ := hg.2
    have hij : i ≠ j := by
      intro h
      have heq : a = b := hi.symm.trans (h ▸ hj)
      exact P.adjacent_irreflexive a (heq ▸ hab)
    have hs : P.edgeArc a b ⊆ frontier (P.faceRegion g) := by
      rw [P.face_boundary g, ← hi, ← hj]
      fin_cases i <;> fin_cases j <;> dsimp at *
      all_goals try exact (hij rfl).elim
      all_goals intro x hx
      all_goals first
        | exact Or.inl (Or.inl hx)
        | exact Or.inl (Or.inr hx)
        | exact Or.inr hx
        | rw [P.arc_symmetric] at hx
          first
            | exact Or.inl (Or.inl hx)
            | exact Or.inl (Or.inr hx)
            | exact Or.inr hx
    exact (hfrontier f g).mono_left hs
  have havoid (f : P.Face) :
      Disjoint (P3767T1FixedTrace P) (P.faceRegion f) := by
    apply Set.disjoint_left.mpr
    intro x hx hxf
    rcases hx with ⟨a, rfl⟩ | ⟨a, b, hab, hx⟩
    · obtain ⟨b, hab⟩ := (P3767T1VertexEdgeIncidence P a).1
      obtain ⟨h, hzero, _⟩ := P.arc_homeomorph a b hab
      have ha : P.position a ∈ P.edgeArc a b := by
        rw [← hzero]
        exact (h ⟨0, by norm_num⟩).property
      exact Set.disjoint_left.mp (hedge f a b hab) ha hxf
    · exact Set.disjoint_left.mp (hedge f a b hab) hx hxf
  refine ⟨?_, ?_, ?_⟩
  · intro f
    refine ⟨havoid f, ?_⟩
    intro x hx
    rw [P.face_boundary f] at hx
    right
    rcases hx with (hx | hx) | hx
    · exact ⟨_, _, P.face_edges f 0 1 (by decide), hx⟩
    · exact ⟨_, _, P.face_edges f 1 2 (by decide), hx⟩
    · exact ⟨_, _, P.face_edges f 2 0 (by decide), hx⟩
  · intro f V hV hdis hmeet
    exact P3767T1BarrierRegionMaximal _ _ _ (P.region_open f)
      (Set.Subset.refl _) hV hdis hmeet
  · ext x
    constructor
    · intro hx
      have hcover : x ∈ P3767T1FixedTrace P ∪
          {x | ∃ f, x ∈ P.faceRegion f} := by
        rw [P3767T1FixedTrace, P.plane_cover]
        trivial
      exact hcover.resolve_left hx
    · rintro ⟨f, hxf⟩ hxt
      exact Set.disjoint_left.mp (havoid f) hxt hxf

end ApollonianSuperharmonic

end
