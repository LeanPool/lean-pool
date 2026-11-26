/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/


module

public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Truncation of a controlling tangle
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Graph Hypergraph Surface GM10 GM14

universe u v w

variable {α : Type u} {β : Type v}

/-- If `T*` controls `T` via `η` of order `θ` and `1 ≤ θ₁ ≤ θ`, then `T*` controls the
`θ₁`-truncation `GM10.truncation T θ₁` of order `θ₁` (Graph Minors XV, Section 5, page 129). -/
theorem IsControllingTangle.truncation {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ θ₁ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h : IsControllingTangle G H η θ_star θ T_star T) (h1 : 1 ≤ θ₁) (hle : θ₁ ≤ θ) :
    IsControllingTangle G H η θ_star θ₁ T_star (GM10.truncation T θ₁) where
  theta_le := hle.trans h.theta_le
  isTangle_star := h.isTangle_star
  isTangle_H := h.isTangle_H.truncation h1 hle
  controls A B hsep hlt A_H B_H hrest := by
    have hlt_θ : separationOrder A B < θ := lt_of_lt_of_le hlt hle
    have hiff := h.controls hsep hlt_θ hrest
    constructor
    · intro hAB
      have hAB_H : (A_H, B_H) ∈ T := hiff.mp hAB
      refine ⟨hAB_H, ?_⟩
      have hsub : A_H.vertexSet ∩ B_H.vertexSet ⊆ η.vMap ⁻¹' (A.vertexSet ∩ B.vertexSet) := by
        intro x ⟨hxA, hxB⟩
        have hxA' : η.vMap x ∈ A.vertexSet ∩ V(η.imageGraph) := by
          rw [← hrest.2.1]
          exact mem_image_of_mem _ hxA
        have hxB' : η.vMap x ∈ B.vertexSet ∩ V(η.imageGraph) := by
          rw [← hrest.2.2.2.1]
          exact mem_image_of_mem _ hxB
        exact ⟨hxA'.1, hxB'.1⟩
      have hcard_le : separationOrder A_H B_H ≤ separationOrder A B := by
        have hfin : (A.vertexSet ∩ B.vertexSet).Finite := (A ∩ B).vertexSet_finite
        have hinj : InjOn η.vMap (A_H.vertexSet ∩ B_H.vertexSet) :=
          η.bijOn_v.injOn.mono (inter_subset_left.trans hrest.1.left_le.vertexSet_subset)
        calc
          separationOrder A_H B_H = (A_H.vertexSet ∩ B_H.vertexSet).ncard := rfl
          _ = (η.vMap '' (A_H.vertexSet ∩ B_H.vertexSet)).ncard := (hinj.ncard_image).symm
          _ ≤ (A.vertexSet ∩ B.vertexSet).ncard :=
            ncard_le_ncard (image_subset_iff.mpr hsub) hfin
          _ = separationOrder A B := rfl
      exact lt_of_le_of_lt hcard_le hlt
    · intro hAB_H
      exact hiff.mpr hAB_H.1

end GraphMinor.GM15
