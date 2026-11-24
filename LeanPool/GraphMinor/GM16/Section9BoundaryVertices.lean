/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.ClearedPathVertices
import LeanPool.GraphMinor.GM16.Section9Zones

/-!
# The battlefield boundary vertices survive clearing

Every boundary point is retained when the separated discs are
cleared. An old vertex at such a point therefore remains a vertex.
Injectivity of the span map also keeps the boundary sets of distinct
battlefields disjoint. These are the endpoint facts used for the
global separator and Claim (9) of XVI (8.1).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
variable {α : Type u} {β : Type v}

/-- Every old vertex on a battlefield boundary survives clearing all
members of the separated family. -/
theorem boundary_vertex_mem_clearFamily {H : Drawing S} {d : Set S → Set S → ℕ}
    {Y : Set S} {γ : ℕ} {Λ : S → Set S}
    (hZone : ∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y))
    (hDis : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)))
    {y x : S} (hy : y ∈ Y) (hx : x ∈ H.V ∩ subBd (Λ y)) :
    x ∈ (clearEnvelopeDrawing H Y Λ).V := by
  have hxU := zone_boundary_subset_clearFamily hZone hDis hy hx.2
  exact mem_clearFamily_of_notMem_union hx.1 (clearFamily_U hZone ▸ hxU).2

omit [ConnectedSpace S] in
/-- Distinct battlefield boundary sets remain disjoint after applying
the span vertex map. -/
theorem battlefield_image_sets_disjoint {H C₁ C₂ : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ γ : ℕ} {z₁ z₂ Λ₁ Λ₂ X₁ X₂ : Set S}
    (hB₁ : IsBattlefield H T d θ γ z₁ Λ₁ C₁ X₁)
    (hB₂ : IsBattlefield H T d θ γ z₂ Λ₂ C₂ X₂)
    (hDis : Disjoint (closure Λ₁) (closure Λ₂)) :
    Disjoint (η.vMap '' X₁) (η.vMap '' X₂) := by
  apply disjoint_left.mpr
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  have haH := hB₁.isFree_X.1 ha
  have hbH := hB₂.isFree_X.1 hb
  have hba' := η.bijOn_v.injOn hbH.1 haH.1 hba
  exact hDis.notMem_of_mem_left haH.2.1 (hba' ▸ hbH.2.1)

end GraphMinor.GM16
