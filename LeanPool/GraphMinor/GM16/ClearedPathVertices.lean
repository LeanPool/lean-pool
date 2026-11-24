/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM11.Walks

/-!
# Old vertices on a path relative to the cleared drawing

An old drawing vertex outside all cleared discs survives clearing.
On a path with no other vertex in the cleared drawing, every old
vertex distinct from its first end is consequently either its last
end or lies in a cleared disc. This supplies the location of `t_i`
in Claim (8) and of `v` after Claim (15) of XVI (8.1).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe u v w
variable {S : Type w} [TopologicalSpace S] [T1Space S]
variable {α : Type u} {β : Type v}

/-- An old drawing vertex outside the cleared discs remains a vertex
of the drawing after the whole family is cleared. -/
theorem mem_clearFamily_of_notMem_union {H : Drawing S} {Y : Set S} {Λ : S → Set S}
    {x : S} (hx : x ∈ H.V) (hOut : x ∉ ⋃ y ∈ Y, Λ y) :
    x ∈ (clearEnvelopeDrawing H Y Λ).V :=
  Or.inl ⟨⟨hx, mem_univ _, hOut⟩, hx⟩

/-- Every old vertex of the new path, except its two ends, lies in
one of the discs that were cleared. -/
theorem old_vertex_place_on_cleared_path {H : Drawing S} {G P : Graph α β}
    (η : SpanEmbedding H G) {Y : Set S} {Λ : S → Set S}
    (η' : SpanEmbedding (clearEnvelopeDrawing H Y Λ) G) (hMap : η'.vMap = η.vMap)
    {s t x : S} (hs : s ∈ H.V) (ht : t ∈ H.V) (hx : x ∈ H.V)
    (hP : IsHPathWithEnds G η'.imageGraph P (η.vMap s) (η.vMap t))
    (hxP : η.vMap x ∈ V(P)) (hxs : x ≠ s) :
    x = t ∨ x ∈ ⋃ y ∈ Y, Λ y := by
  by_cases hIn : x ∈ ⋃ y ∈ Y, Λ y
  · exact Or.inr hIn
  · have hxClear := mem_clearFamily_of_notMem_union hx hIn
    have hxIm : η.vMap x ∈ V(η'.imageGraph) := by
      rw [← hMap]
      exact η'.bijOn_v.mapsTo hxClear
    have hEnds : η.vMap x ∈ ({η.vMap s, η.vMap t} : Set α) :=
      hP.2.2.2.2.2.1 ▸ ⟨hxP, hxIm⟩
    rcases hEnds with hxs' | hxt
    · exact False.elim (hxs (η.bijOn_v.injOn hx hs hxs'))
    · exact Or.inl (η.bijOn_v.injOn hx ht (mem_singleton_iff.mp hxt))

end GraphMinor.GM16
