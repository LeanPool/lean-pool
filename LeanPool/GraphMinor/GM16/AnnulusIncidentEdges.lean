/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section88

/-!
# Edges at interior vertices of an annulus

An edge cannot cross either drawn zone boundary. At a vertex of the
closed annulus on neither boundary, every incident edge is therefore
retained in the annular subdrawing. This is the local condition used
to prove the connectedness assertion in XVI (8.1), Claim (14).
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The annular subdrawing retains every incident edge at a vertex
away from its two boundary circles. -/
theorem annular_subdrawing_keeps_edges {H : Drawing S}
    {d : Set S → Set S → ℕ} {γ δ : ℕ} {z w I O : Set S}
    (hI : IsLambdaZoneAround H d γ z I) (hO : IsLambdaZoneAround H d δ w O)
    {e : Set S} {x y : S} (hl : H.toGraph.IsLink e x y)
    (hx : x ∈ (H.interSet (closure O \ I)).V)
    (hNot : x ∉ (H.V ∩ subBd I) ∪ (H.V ∩ subBd O)) :
    (H.interSet (closure O \ I)).toGraph.IsLink e x y := by
  have hClosed : IsClosed (closure O \ I) := isClosed_closure.sdiff hI.isOpenDisc.1
  obtain ⟨hxH, hxO, hxI⟩ := (mem_interSet_V_iff hClosed).mp hx
  have hxNotI : x ∉ subBd I := fun h => hNot (Or.inl ⟨hxH, h⟩)
  have hxNotO : x ∉ subBd O := fun h => hNot (Or.inr ⟨hxH, h⟩)
  have hclI := (isOpen_disjoint_subBd_and_closure_eq hI.isOpenDisc.1).2
  have hclO := (isOpen_disjoint_subBd_and_closure_eq hO.isOpenDisc.1).2
  have hxOpenO : x ∈ O := by
    rw [hclO] at hxO
    exact hxO.resolve_right hxNotO
  have hxNotClI : x ∉ closure I := by
    rw [hclI]
    exact fun h => h.elim hxI hxNotI
  have heO : e ⊆ O := by
    rcases edge_subset_or_subset_compl_of_zone hO hl.1 with h | h
    · exact h
    · have hc := closure_minimal h (isClosed_univ.sdiff hO.isOpenDisc.1)
      exact False.elim ((hc (hl.2.2.2.symm ▸ (show x ∈ ({x, y} : Set S) from Or.inl rfl)).1).2
        hxOpenO)
  have heI : e ⊆ univ \ I := by
    rcases edge_subset_or_subset_compl_of_zone hI hl.1 with h | h
    · have hc := closure_mono h
      have hxcl : x ∈ closure e := (hl.2.2.2.symm ▸ (show x ∈ ({x, y} : Set S) from Or.inl rfl)).1
      exact False.elim (hxNotClI (hc hxcl))
    · exact h
  have heNew : e ∈ (H.interSet (closure O \ I)).E :=
    mem_interSet_E_iff.mpr ⟨hl.1, fun t ht => ⟨subset_closure (heO ht), (heI ht).2⟩⟩
  exact ((interSet_isSub (Γ := H)).isLink_iff heNew).mpr hl

end GraphMinor.GM16
