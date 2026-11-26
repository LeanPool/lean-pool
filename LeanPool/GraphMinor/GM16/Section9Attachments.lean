/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section3c

/-!
# Trimming the attachment paths in XVI (8.1)

For Claim (9), an attachment from a boundary set to the bad path can
be trimmed at its last boundary vertex and first vertex of that path.
Its only vertex in the cleared drawing is then its initial vertex.
A simple path with only one vertex in a subgraph has no edge there.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14
universe u v

/-- A path whose intersection with a subgraph is a singleton has no
edge in that subgraph, since such an edge would be a loop in the path. -/
theorem path_edges_disjoint_of_singleton_inter {α : Type u} {β : Type v}
    {G H P : Graph α β} {a b x : α} (hHG : H ≤ G)
    (hP : IsGraphPathWithEnds G P a b) (hInter : V(P) ∩ V(H) ⊆ {x}) :
    Disjoint E(P) E(H) := by
  apply disjoint_left.mpr
  intro e heP heH
  obtain ⟨u, v, hl⟩ := P.exists_isLink_of_mem_edgeSet heP
  have hlG := hP.1.isLink_mono hl
  have hlH := (hHG.isLink_iff heH).mpr hlG
  have hu : u = x := mem_singleton_iff.mp (hInter ⟨hl.left_mem, hlH.left_mem⟩)
  have hv : v = x := mem_singleton_iff.mp (hInter ⟨hl.right_mem, hlH.right_mem⟩)
  have hLoop : G.IsLink e x x := by simpa only [hu, hv] using hlG
  exact hP.not_isLoopAt heP x hLoop

/-- Trim one of the attachments in XVI (8.1), Claim (9), page 73, so
that it meets the cleared drawing in just its initial boundary vertex. -/
theorem trim_boundary_attachment {α : Type u} {β : Type v}
    {G H Q : Graph α β} {X A : Set α} {a x : α}
    (hHG : H ≤ G) (hX : X ⊆ V(H)) (hQ : IsGraphPathWithEnds G Q a x)
    (ha : a ∈ X) (hx : x ∈ A) (hQH : V(Q) ∩ V(H) ⊆ X) :
    ∃ b ∈ X, ∃ y ∈ A, ∃ R : Graph α β,
      R ≤ Q ∧ IsGraphPathWithEnds G R b y ∧ V(R) ∩ V(H) = {b} ∧ Disjoint E(R) E(H) := by
  obtain ⟨b, hb, y, hy, R, hRQ, hR⟩ := hQ.exists_isFromToPathWithEnds ha hx
  have hInter : V(R) ∩ V(H) = {b} := by
    apply subset_antisymm
    · rintro z ⟨hzR, hzH⟩
      exact hR.2.1 ▸ ⟨hzR, hQH ⟨hRQ.vertexSet_mono hzR, hzH⟩⟩
    · rintro z rfl
      exact ⟨hR.1.left_mem, hX hb⟩
  exact ⟨b, hb, y, hy, R, hRQ, hR.1, hInter,
    path_edges_disjoint_of_singleton_inter hHG hR.1 hInter.subset⟩

end GraphMinor.GM16
