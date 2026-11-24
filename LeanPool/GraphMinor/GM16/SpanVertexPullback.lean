/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import Mathlib.Data.Set.Card

/-!
# Pulling a finite vertex set back through a span

Restrict the preimage to the drawing vertices, where the span map is
injective. Its cardinality is at most that of the original finite
set. Thus the ambient separator in XVI (8.1) is still smaller than
`κ` when applying the drawn-path arguments of Claims (11)–(14).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM14
universe u v w
variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}

/-- Pulling back an ambient finite set to the drawing vertices cannot
increase its cardinality. -/
theorem span_vertex_pullback_card {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) {Z : Set α} (hZ : Z.Finite) :
    (H.V ∩ η.vMap ⁻¹' Z).Finite ∧ (H.V ∩ η.vMap ⁻¹' Z).ncard ≤ Z.ncard := by
  have hA : (H.V ∩ η.vMap ⁻¹' Z).Finite := H.finite_V.subset inter_subset_left
  refine ⟨hA, ?_⟩
  have hi : InjOn η.vMap (H.V ∩ η.vMap ⁻¹' Z) := η.bijOn_v.injOn.mono inter_subset_left
  have hIm : η.vMap '' (H.V ∩ η.vMap ⁻¹' Z) ⊆ Z := by
    rintro x ⟨y, hy, rfl⟩
    exact hy.2
  calc
    (H.V ∩ η.vMap ⁻¹' Z).ncard = (η.vMap '' (H.V ∩ η.vMap ⁻¹' Z)).ncard :=
      hi.ncard_image.symm
    _ ≤ Z.ncard := ncard_le_ncard hIm hZ

end GraphMinor.GM16
