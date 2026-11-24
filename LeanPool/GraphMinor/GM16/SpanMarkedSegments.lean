/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM16.MarkedPathSegments
import LeanPool.GraphMinor.GM09.Basic

/-!
# Consecutive drawing vertices along an ambient path

Apply the marked-path lemmas to the vertices of the image drawing.
The vertex bijection then identifies the selected vertices with
points of the original drawing. This supplies the choices of `t_i`
and of `u,v` in XVI (8.1), pages 72–75.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14
universe u v w
variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}

/-- Choose the second drawing vertex along a path starting at a
drawing vertex, and the segment up to that vertex. -/
theorem exists_initial_span_segment {H : Drawing S} {G P : Graph α β}
    (η : SpanEmbedding H G) {s t : S} (hs : s ∈ H.V) (ht : t ∈ H.V) (hst : s ≠ t)
    (hP : IsGraphPathWithEnds G P (η.vMap s) (η.vMap t)) :
    ∃ v ∈ H.V, v ≠ s ∧ ∃ R : Graph α β,
      R ≤ P ∧ IsGraphPathWithEnds G R (η.vMap s) (η.vMap v) ∧
      V(R) ∩ V(η.imageGraph) = {η.vMap s, η.vMap v} := by
  have hneq : η.vMap s ≠ η.vMap t := fun h => hst (η.bijOn_v.injOn hs ht h)
  obtain ⟨v', hv', hvs, R, hRP, hR, hInter⟩ := exists_initial_marked_segment hP
    (η.bijOn_v.mapsTo hs) (η.bijOn_v.mapsTo ht) hneq
  obtain ⟨v, hv, hmap⟩ := η.bijOn_v.surjOn hv'
  refine ⟨v, hv, ?_, R, hRP, ?_, ?_⟩
  · intro heq
    exact hvs (hmap.symm.trans (congrArg η.vMap heq))
  · simpa only [hmap] using hR
  · simpa only [hmap] using hInter

/-- Choose the first drawing vertex outside a shell, distinct from
the initial end, and the last drawing vertex before it. This is the
selection immediately before Claim (15) of XVI (8.1), pages 74–75. -/
theorem exists_consecutive_span_exit {H : Drawing S} {G P : Graph α β}
    (η : SpanEmbedding H G) {B : Set S} {s t : S}
    (hs : s ∈ H.V) (ht : t ∈ H.V) (hst : s ≠ t) (htB : t ∉ B)
    (hP : IsGraphPathWithEnds G P (η.vMap s) (η.vMap t)) :
    ∃ u ∈ H.V, ∃ v ∈ H.V,
      u ≠ v ∧ v ≠ s ∧ v ∉ B ∧ (u = s ∨ u ∈ B) ∧
      ∃ R : Graph α β, R ≤ P ∧ IsGraphPathWithEnds G R (η.vMap u) (η.vMap v) ∧
        V(R) ∩ V(η.imageGraph) = {η.vMap u, η.vMap v} := by
  have hneq : η.vMap s ≠ η.vMap t := fun h => hst (η.bijOn_v.injOn hs ht h)
  have htOut : η.vMap t ∉ η.vMap '' (H.V ∩ B) := by
    rintro ⟨x, hx, hxt⟩
    have hxt' := η.bijOn_v.injOn hx.1 ht hxt
    exact htB (hxt' ▸ hx.2)
  obtain ⟨u', hu', v', hv', huv', hvs', hvB', huCase, R, hRP, hR, hInter⟩ :=
    exists_consecutive_marked_exit hP (η.bijOn_v.mapsTo hs) (η.bijOn_v.mapsTo ht) hneq htOut
  obtain ⟨u, hu, humap⟩ := η.bijOn_v.surjOn hu'
  obtain ⟨v, hv, hvmap⟩ := η.bijOn_v.surjOn hv'
  have huCase' : u = s ∨ u ∈ B := by
    rcases huCase with hueq | ⟨x, hx, hxu⟩
    · exact Or.inl (η.bijOn_v.injOn hu hs (humap.trans hueq))
    · have hxu' := η.bijOn_v.injOn hx.1 hu (hxu.trans humap.symm)
      exact Or.inr (hxu' ▸ hx.2)
  refine ⟨u, hu, v, hv, ?_, ?_, ?_, huCase', R, hRP, ?_, ?_⟩
  · intro heq
    exact huv' (humap.symm.trans ((congrArg η.vMap heq).trans hvmap))
  · intro heq
    exact hvs' (hvmap.symm.trans (congrArg η.vMap heq))
  · intro hvB
    exact hvB' ⟨v, ⟨hv, hvB⟩, hvmap⟩
  · simpa only [humap, hvmap] using hR
  · simpa only [humap, hvmap] using hInter

end GraphMinor.GM16
