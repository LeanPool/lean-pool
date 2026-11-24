/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3UnselectedBoundary
import LeanPool.GraphMinor.GM12.Section2NormalNoncover
import LeanPool.GraphMinor.GM11.Theorem66
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# The separator inequality in the one-disc sphere case

In XII (3.2), pages 247--248, a normal line and the two arcs of
the prescribed boundary determine two discs covering the drawing.
The second tangle axiom leaves at least one disc unselected. The
free boundary vertices lie on its reverse side, so the unselected
boundary lemma bounds their total number by its boundary count.
Cancel the common arc and common ends. The line has at least as
many vertices as one of the two prescribed arcs, hence at least
the smaller of their two counts.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

private theorem vertex_count_le_of_union_count_le
    {S : Type*} [TopologicalSpace S] (Γ : Drawing S) {A B P : Set S}
    (hcap : A ∩ B = A ∩ P)
    (hcount : (Γ.V ∩ (A ∪ B)).ncard ≤ (Γ.V ∩ (A ∪ P)).ncard) :
    (Γ.V ∩ B).ncard ≤ (Γ.V ∩ P).ncard := by
  have hcommon : (Γ.V ∩ A) ∩ (Γ.V ∩ B) = (Γ.V ∩ A) ∩ (Γ.V ∩ P) := by
    have h₁ : (Γ.V ∩ A) ∩ (Γ.V ∩ B) = Γ.V ∩ (A ∩ B) := by
      ext x
      simp only [mem_inter_iff]
      tauto
    have h₂ : (Γ.V ∩ A) ∩ (Γ.V ∩ P) = Γ.V ∩ (A ∩ P) := by
      ext x
      simp only [mem_inter_iff]
      tauto
    rw [h₁, h₂, hcap]
  have h₁ := Set.ncard_union_add_ncard_inter (Γ.V ∩ A) (Γ.V ∩ B)
    (Γ.finite_V.inter_of_left A) (Γ.finite_V.inter_of_left B)
  have h₂ := Set.ncard_union_add_ncard_inter (Γ.V ∩ A) (Γ.V ∩ P)
    (Γ.finite_V.inter_of_left A) (Γ.finite_V.inter_of_left P)
  rw [hcommon] at h₁
  rw [inter_union_distrib_left, inter_union_distrib_left] at hcount
  omega

/-- The normal-line vertex inequality used to apply VI (3.6) in
XII (3.2), pages 247--248. The two side discs and the reverse-side
containments are displayed explicitly. -/
theorem sphere_separator_vertex_count_ge_min
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T) {A B P D E Q : Set S}
    (hfree : GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ (A ∪ B)))
    (hAB : A ∩ B = Q) (hAP : A ∩ P = Q) (hBP : B ∩ P = Q)
    (hn : Γ.IsNormal (A ∪ B ∪ P))
    (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hbD : discBd D = B ∪ P) (hbE : discBd E = A ∪ P)
    (hcover : Γ.U ⊆ D ∪ E)
    (houtsideD : Γ.V ∩ (A ∪ B) ⊆ closure (univ \ D))
    (houtsideE : Γ.V ∩ (A ∪ B) ⊆ closure (univ \ E)) :
    min (Γ.V ∩ A).ncard (Γ.V ∩ B).ncard ≤ (Γ.V ∩ P).ncard := by
  let G : PaintingOrDrawing S := .drawing Γ
  have hfD : frontier D = B ∪ P := (IsClosedDisc.frontier_eq_discBd hS hD).trans hbD
  have hfE : frontier E = A ∪ P := (IsClosedDisc.frontier_eq_discBd hS hE).trans hbE
  have hnD : G.IsNormal (frontier D) := by
    rw [hfD]
    intro x hx
    exact hn ⟨hx.1.elim (fun h => Or.inl (Or.inr h)) Or.inr, hx.2⟩
  have hnE : G.IsNormal (frontier E) := by
    rw [hfE]
    intro x hx
    exact hn ⟨hx.1.elim (fun h => Or.inl (Or.inl h)) Or.inr, hx.2⟩
  have hnot : (G.inter D, G.interOutside D) ∉ T ∨ (G.inter E, G.interOutside E) ∉ T := by
    by_cases hmD : (G.inter D, G.interOutside D) ∈ T
    · right
      intro hmE
      exact not_support_subset_of_normal_frontiers (Γ := G) (GM11.IsTangle.isPretangle hT)
        hD.isCompact.isClosed hE.isCompact.isClosed hE.isCompact.isClosed hnD hnE hnE
        hmD hmE hmE (fun x hx => Or.inl (hcover hx))
    · exact Or.inl hmD
  rcases hnot with hnDsel | hnEsel
  · have hcount := free_set_card_le_frontier_of_not_selected hT hfree hD.isCompact.isClosed hnD
      houtsideD hnDsel
    rw [hfD, union_comm A B] at hcount
    have hcap : B ∩ A = B ∩ P := (inter_comm B A).trans (hAB.trans hBP.symm)
    exact (min_le_left _ _).trans (vertex_count_le_of_union_count_le Γ hcap hcount)
  · have hcount := free_set_card_le_frontier_of_not_selected hT hfree hE.isCompact.isClosed hnE
      houtsideE hnEsel
    rw [hfE] at hcount
    exact (min_le_right _ _).trans (vertex_count_le_of_union_count_le Γ (hAB.trans hAP.symm) hcount)

end GraphMinor.GM12
