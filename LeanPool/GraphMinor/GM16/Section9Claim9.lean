/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9Attachments
import LeanPool.GraphMinor.GM16.PathEndSubpath
import LeanPool.GraphMinor.GM16.Section6HairUnion
import LeanPool.GraphMinor.GM09.Basic

/-!
# At least one battlefield has no clean attachment to the bad path

This is Claim (9) in the proof of XVI (8.1). Two clean attachments,
one from each boundary set, could be joined through the bad path.
Trim them first, and keep only the segment between their contacts
with that path. The resulting connected union avoids the separator
and meets the cleared drawing only in the two boundary ends.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM14
universe u v

/-- Graph Minors XVI, proof of (8.1), Claim (9), page 73: two clean
attachments to the bad path contradict its boundary-path separator.
The subpath between the contacts avoids the original two ends unless
one of those ends is itself a contact. -/
theorem section9_no_two_clean_attachments {α : Type u} {β : Type v}
    {G H P₀ Q₁ Q₂ : Graph α β} {X₁ X₂ Z : Set α} {s₁ s₂ a b x y : α}
    (hHG : H ≤ G) (hX₁ : X₁ ⊆ V(H)) (hX₂ : X₂ ⊆ V(H)) (hDisX : Disjoint X₁ X₂)
    (hP₀ : IsHPathWithEnds G H P₀ s₁ s₂) (hPZ : V(P₀) ∩ Z ⊆ {s₁, s₂})
    (hCut : ∀ P a b, IsHPathWithEnds G H P a b → a ∈ X₁ → b ∈ X₂ → (V(P) ∩ Z).Nonempty)
    (hQ₁ : IsGraphPathWithEnds G Q₁ a x) (ha : a ∈ X₁) (hx : x ∈ V(P₀))
    (hQ₁H : V(Q₁) ∩ V(H) ⊆ X₁) (hQ₁Z : Disjoint V(Q₁) Z)
    (hQ₂ : IsGraphPathWithEnds G Q₂ b y) (hb : b ∈ X₂) (hy : y ∈ V(P₀))
    (hQ₂H : V(Q₂) ∩ V(H) ⊆ X₂) (hQ₂Z : Disjoint V(Q₂) Z) : False := by
  obtain ⟨a', ha', x', hx', A, hAQ₁, hA, hAH, hAE⟩ :=
    trim_boundary_attachment hHG hX₁ hQ₁ ha hx hQ₁H
  obtain ⟨b', hb', y', hy', B, hBQ₂, hB, hBH, hBE⟩ :=
    trim_boundary_attachment hHG hX₂ hQ₂ hb hy hQ₂H
  have hAZ := hQ₁Z.mono hAQ₁.vertexSet_mono Subset.rfl
  have hBZ := hQ₂Z.mono hBQ₂.vertexSet_mono Subset.rfl
  obtain ⟨R, hRP, _, hR⟩ := hP₀.2.1.exists_subpath hx' hy'
  have hRend := subpath_inter_ends_subset hP₀.2.1 hR hRP
  have hRZ : Disjoint V(R) Z := by
    apply disjoint_left.mpr
    intro w hwR hwZ
    have hwEnd := hPZ ⟨hRP.vertexSet_mono hwR, hwZ⟩
    have hwNew := hRend ⟨hwR, hwEnd⟩
    rcases hwNew with hwx | hwy
    · exact hAZ.notMem_of_mem_left hA.right_mem (hwx ▸ hwZ)
    · rw [mem_singleton_iff] at hwy
      exact hBZ.notMem_of_mem_left hB.right_mem (hwy ▸ hwZ)
  have hRH : V(R) ∩ V(H) ⊆ {a', b'} := by
    rintro w ⟨hwR, hwH⟩
    have hwEnd : w ∈ ({s₁, s₂} : Set α) := hP₀.2.2.2.2.2.1 ▸ ⟨hRP.vertexSet_mono hwR, hwH⟩
    have hwNew := hRend ⟨hwR, hwEnd⟩
    rcases hwNew with hwx | hwy
    · have hxH : x' ∈ V(H) := hwx ▸ hwH
      have hxa : x' = a' := mem_singleton_iff.mp (hAH ▸ ⟨hA.right_mem, hxH⟩)
      exact Or.inl (hwx.trans hxa)
    · rw [mem_singleton_iff] at hwy
      have hyH : y' ∈ V(H) := hwy ▸ hwH
      have hyb : y' = b' := mem_singleton_iff.mp (hBH ▸ ⟨hB.right_mem, hyH⟩)
      exact Or.inr (hwy.trans hyb)
  have hRE : Disjoint E(R) E(H) := hP₀.2.2.2.2.2.2.mono hRP.edgeSet_mono Subset.rfl
  let J₁ := subgraphUnion G R A
  have hJ₁G : J₁ ≤ G := subgraphUnion_le hR.1 hA.1
  have hRJ₁ : R ≤ J₁ := le_subgraphUnion_left hR.1 hA.1
  have hAJ₁ : A ≤ J₁ := le_subgraphUnion_right hR.1 hA.1
  have hConn₁ : IsGraphConnected J₁ := isGraphConnected_subgraphUnion hR.1 hA.1
    (graphPath_isGraphConnected hR) (graphPath_isGraphConnected hA) ⟨x', hR.left_mem, hA.right_mem⟩
  let J := subgraphUnion G J₁ B
  have hJG : J ≤ G := subgraphUnion_le hJ₁G hB.1
  have hJ₁J : J₁ ≤ J := le_subgraphUnion_left hJ₁G hB.1
  have hBJ : B ≤ J := le_subgraphUnion_right hJ₁G hB.1
  have hConn : IsGraphConnected J := isGraphConnected_subgraphUnion hJ₁G hB.1
    hConn₁ (graphPath_isGraphConnected hB) ⟨y', hRJ₁.vertexSet_mono hR.right_mem, hB.right_mem⟩
  have hJV : V(J) = (V(R) ∪ V(A)) ∪ V(B) := by
    rw [show J = subgraphUnion G J₁ B from rfl, vertexSet_subgraphUnion,
      show J₁ = subgraphUnion G R A from rfl, vertexSet_subgraphUnion]
  have hJE : E(J) = (E(R) ∪ E(A)) ∪ E(B) := by
    rw [show J = subgraphUnion G J₁ B from rfl, edgeSet_subgraphUnion hJ₁G hB.1,
      show J₁ = subgraphUnion G R A from rfl, edgeSet_subgraphUnion hR.1 hA.1]
  have hJZ : Disjoint V(J) Z := by
    rw [hJV]
    exact (hRZ.union_left hAZ).union_left hBZ
  have hJH : V(J) ∩ V(H) ⊆ {a', b'} := by
    rintro w ⟨hwJ, hwH⟩
    rw [hJV] at hwJ
    rcases hwJ with (hwR | hwA) | hwB
    · exact hRH ⟨hwR, hwH⟩
    · exact Or.inl (mem_singleton_iff.mp (hAH ▸ ⟨hwA, hwH⟩))
    · exact Or.inr (mem_singleton_iff.mp (hBH ▸ ⟨hwB, hwH⟩))
  have hJEdges : Disjoint E(J) E(H) := by
    rw [hJE]
    exact (hRE.union_left hAE).union_left hBE
  have haJ : a' ∈ V(J) := hJ₁J.vertexSet_mono (hAJ₁.vertexSet_mono hA.left_mem)
  have hbJ : b' ∈ V(J) := hBJ.vertexSet_mono hB.left_mem
  obtain ⟨W⟩ := hConn.2 a' haJ b' hbJ
  obtain ⟨L, hL, _, _⟩ := exists_isGraphPathWithEnds_of_walk W
  have hLG := hL.mono hJG
  have hLH : V(L) ∩ V(H) = {a', b'} := by
    apply subset_antisymm
    · rintro w ⟨hwL, hwH⟩
      exact hJH ⟨hL.1.vertexSet_mono hwL, hwH⟩
    · rintro w (rfl | rfl)
      · exact ⟨hL.left_mem, hX₁ ha'⟩
      · exact ⟨hL.right_mem, hX₂ hb'⟩
  have hHP : IsHPathWithEnds G H L a' b' :=
    ⟨hHG, hLG, fun he => hDisX.notMem_of_mem_left ha' (he.symm ▸ hb'), hX₁ ha', hX₂ hb', hLH,
      hJEdges.mono hL.1.edgeSet_mono Subset.rfl⟩
  obtain ⟨w, hwL, hwZ⟩ := hCut L a' b' hHP ha' hb'
  exact hJZ.notMem_of_mem_left (hL.1.vertexSet_mono hwL) hwZ

end GraphMinor.GM16
