/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3723T1AllContactRouting
public import LeanPool.ApollonianSuperharmonic.P3776T1FixedGeometry
public import LeanPool.ApollonianSuperharmonic.P3767T1VertexEdgeIncidence

-- [TABLET NODE: P3913T1RoutedTraceClosed]

/-!
# P3913T1RoutedTraceClosed

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3913T1RoutedTraceClosed {ι : Type} (P : PeriodicTileComplex ι)
    (D : P3723T1AllContactRouting P) :
    IsClosed (Set.range D.position ∪
      {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ D.edgeArc a b}) := by
-- BODY
  classical
  let : Nontrivial ι := (P3776T1FixedGeometry P.toPeriodicTileCore).1
  have contact (a b : ι) (h : P.plane.adjacent a b) :
      P3723T1EdgeContact P a b := by
    exact ⟨(show a ≠ b from fun e => P.plane.adjacent_irreflexive a (e.symm ▸ h)),
      P.adjacent_has_common_edge a b h⟩
  let E := {e : ι × ι // P.plane.adjacent e.1 e.2}
  let A : E → Set (Real × Real) := fun e => D.edgeArc e.val.1 e.val.2
  have compact (e : E) : IsCompact (A e) := by
    obtain ⟨g, hg, _, hr, _⟩ := D.edgeArc_parameterization _ _ (contact _ _ e.property)
    rw [show A e = Set.range g from hr.symm]
    exact isCompact_range hg
  have locally_finite : LocallyFinite A := by
    intro x
    refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x (by norm_num), ?_⟩
    apply ((D.compact_local_finiteness _ (isCompact_closedBall x 1)).preimage
      (show Function.Injective (fun e : E => e.val) from Subtype.val_injective).injOn).subset
    rintro e ⟨z, hza, hzb⟩
    exact ⟨contact _ _ e.property, z, hza, hzb⟩
  have closed_union : IsClosed (Set.iUnion A) :=
    locally_finite.isClosed_iUnion (fun e => (compact e).isClosed)
  have trace_eq : Set.range D.position ∪
      {p | ∃ a b, P.plane.adjacent a b ∧ p ∈ D.edgeArc a b} = Set.iUnion A := by
    ext x
    constructor
    · rintro (⟨a, rfl⟩ | ⟨a, b, hab, hx⟩)
      · obtain ⟨b, hab⟩ := (P3767T1VertexEdgeIncidence P.plane a).1
        obtain ⟨h, h0, _⟩ := D.edgeArc_homeomorph a b (contact a b hab)
        apply Set.mem_iUnion.mpr
        refine ⟨⟨(a, b), hab⟩, ?_⟩
        change D.position a ∈ D.edgeArc a b
        rw [← h0]
        exact (h ⟨0, by norm_num⟩).property
      · exact Set.mem_iUnion.mpr ⟨⟨(a, b), hab⟩, hx⟩
    · intro hx
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
      exact Or.inr ⟨e.val.1, e.val.2, e.property, he⟩
  rw [trace_eq]
  exact closed_union

end ApollonianSuperharmonic

end
