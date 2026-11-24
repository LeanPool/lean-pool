/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2Corners
public import LeanPool.GraphMinor.GM12.Section2HalfEdgeNeighbourhood
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# A spoke in a corner, or a neighbourhood free of spokes

For the entry-edge existence assertion on XII page 243, compare the
short radial half-edges with the sectors of the original drawing.
Each half-edge enters one sector. If none enters the prescribed sector,
compactness removes all the other parts of the radial drawing from a
small neighbourhood. A chord in that sector can then be chosen away
from the radial drawing.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

/-- Either a half-edge has its germ in the prescribed sector interior,
or the sector off the original drawing misses the second drawing in a
neighbourhood of the vertex. The second drawing's half-edges are assumed
to stay off the original drawing, as radial spokes do. -/
theorem sector_spoke_or_free_neighbourhood {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ K : Drawing S} {γ η : Set S → I → S} (hη : EdgePar K η)
    {v : S} (hvΓ : v ∈ Γ.V) (hvK : v ∈ K.V)
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ P Q : halfEdges Γ γ v → Set S} {W : Set S}
    {τ : halfEdges Γ γ v → I}
    (hsec : IsSectors Γ γ v next ρ P W Q τ)
    (hcover : W \ Γ.U ⊆ ⋃ k, Q k)
    (hoff : ∀ i : halfEdges K η v, ∀ t : I, 0 < t → spoke η i.val t ∉ Γ.U)
    (k : halfEdges Γ γ v) :
    (∃ (i : halfEdges K η v) (ε : I), 0 < ε ∧
      ∀ t, 0 < t → t ≤ ε → spoke η i.val t ∈ Q k \ discBd (Q k)) ∨
    (∃ O : Set S, IsOpen O ∧ v ∈ O ∧ Disjoint ((O ∩ Q k) \ Γ.U) K.U) := by
  classical
  have hg : ∀ i : halfEdges K η v, Continuous (spoke η i.val) :=
    fun i => (hη.cont i.val.1 i.property.1).comp (continuous_halfPar i.val.2)
  have hg0 : ∀ i : halfEdges K η v, spoke η i.val 0 = v := by
    intro i
    rw [spoke_zero]
    exact i.property.2
  have hchoice : ∀ i : halfEdges K η v,
      ∃ (j : halfEdges Γ γ v) (ε : I), 0 < ε ∧
        ∀ t, t ≤ ε → spoke η i.val t ∈ Q j := by
    intro i
    obtain ⟨j, ε, hε, hQ, _⟩ :=
      initially_in_given_corner hsec hcover (hg i) (hg0 i) (hoff i)
    exact ⟨j, ε, hε, hQ⟩
  choose j ε hε hQ using hchoice
  by_cases hex : ∃ i, j i = k
  · left
    obtain ⟨i, hi⟩ := hex
    obtain ⟨δ, hδ, hδε, hδW⟩ := exists_pos_le (hg i) hsec.isOpen
      ((hg0 i).symm ▸ hsec.mem) (hε i)
    refine ⟨i, δ, hδ, ?_⟩
    intro t ht htδ
    refine ⟨hi ▸ hQ i t (htδ.trans hδε), ?_⟩
    intro hbd
    exact hoff i t ht (hsec.bdU k ⟨hδW t htδ, hbd⟩)
  · right
    obtain ⟨O, hO, hvO, hOK⟩ := exists_halfEdge_neighbourhood K hη hvK ε hε
    refine ⟨O, hO, hvO, Set.disjoint_left.mpr ?_⟩
    intro x hx hxK
    rcases hOK ⟨hx.1.1, hxK⟩ with hxv | hxspoke
    · exact hx.2 (mem_singleton_iff.mp hxv ▸ Γ.V_subset_U hvΓ)
    · obtain ⟨i, t, ht, htx⟩ := mem_iUnion.mp hxspoke
      have ht0 : 0 < t := by
        apply unitInterval.pos_iff_ne_zero.mpr
        intro htzero
        have hxv : x = v := by rw [htzero, hg0 i] at htx; exact htx.symm
        exact hx.2 (hxv ▸ Γ.V_subset_U hvΓ)
      have hxi : x ∈ Q (j i) := htx ▸ hQ i t ht.2
      exact hx.2 (hsec.inter k (j i) (fun h => hex ⟨i, h.symm⟩) ⟨hx.1.2, hxi⟩)

end GraphMinor.GM12
