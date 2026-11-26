/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM16.Section6HairUnion
import LeanPool.GraphMinor.GM09.Basic

/-!
# A clean connected extension gives an attachment

Join a clean path to a connected subgraph that avoids the cleared
drawing. If the subgraph meets the bad path, their connected union
contains a clean attachment to it. This is the last graph argument
in XVI (8.1), Claim (14).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
universe u v

/-- Extending a path by a connected subgraph that avoids the cleared
graph preserves a clean attachment to any graph it meets. -/
theorem connected_extension_gives_attachment {α : Type u} {β : Type v}
    {G H P₀ Q J : Graph α β} {X Z : Set α} {a b : α}
    (hQ : IsGraphPathWithEnds G Q a b) (hJ : J ≤ G) (hConn : IsGraphConnected J)
    (hQJ : (V(Q) ∩ V(J)).Nonempty) (hP₀J : (V(P₀) ∩ V(J)).Nonempty)
    (hQH : V(Q) ∩ V(H) ⊆ X) (hJH : Disjoint V(J) V(H))
    (hQZ : Disjoint V(Q) Z) (hJZ : Disjoint V(J) Z) :
    ∃ c ∈ V(P₀), ∃ R : Graph α β,
      IsGraphPathWithEnds G R a c ∧ V(R) ∩ V(H) ⊆ X ∧ Disjoint V(R) Z := by
  let U := subgraphUnion G Q J
  have hUG : U ≤ G := subgraphUnion_le hQ.1 hJ
  have hQU : Q ≤ U := le_subgraphUnion_left hQ.1 hJ
  have hJU : J ≤ U := le_subgraphUnion_right hQ.1 hJ
  have hU : IsGraphConnected U := isGraphConnected_subgraphUnion hQ.1 hJ
    (graphPath_isGraphConnected hQ) hConn hQJ
  obtain ⟨c, hcP₀, hcJ⟩ := hP₀J
  obtain ⟨W⟩ := hU.2 a (hQU.vertexSet_mono hQ.left_mem) c (hJU.vertexSet_mono hcJ)
  obtain ⟨R, hR, _, _⟩ := exists_isGraphPathWithEnds_of_walk W
  have hUV : V(U) = V(Q) ∪ V(J) := vertexSet_subgraphUnion G Q J
  refine ⟨c, hcP₀, R, hR.mono hUG, ?_, ?_⟩
  · rintro x ⟨hxR, hxH⟩
    have hxU := hR.1.vertexSet_mono hxR
    rw [hUV] at hxU
    rcases hxU with hxQ | hxJ
    · exact hQH ⟨hxQ, hxH⟩
    · exact False.elim (hJH.notMem_of_mem_left hxJ hxH)
  · have hUZ : Disjoint V(U) Z := by
      rw [hUV]
      exact hQZ.union_left hJZ
    exact hUZ.mono hR.1.vertexSet_mono Subset.rfl

end GraphMinor.GM16
