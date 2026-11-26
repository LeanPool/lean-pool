/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9ZoneCuts
import LeanPool.GraphMinor.GM16.Section9Uncross
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Normalizing the Menger separation between two boundaries

Join the inner side of the separator to the closed inner zone and
cut off everything beyond the outer zone. The zone boundary vertices
already belong to the corresponding sides, so this uncrossing does
not enlarge the separator. The resulting inner side contains every
edge in the inner closed disc and only edges in the outer open disc.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- The annular normalization in the planar Menger argument of
XVI (8.1), Claim (10), page 73. -/
theorem exists_annular_separation {H : Drawing S} {d : Set S → Set S → ℕ}
    {γ γ' : ℕ} {z Λ M : Set S} {A B : Hypergraph S (Set S)}
    (hΛ : IsLambdaZoneAround H d γ z Λ) (hM : IsLambdaZoneAround H d γ' z M)
    (hNest : closure M ⊆ Λ) (hSep : H.toHypergraph.IsSeparation A B)
    (hInner : H.V ∩ subBd M ⊆ A.vertexSet) (hOuter : H.V ∩ subBd Λ ⊆ B.vertexSet) :
    ∃ A' B' : Hypergraph S (Set S), H.toHypergraph.IsSeparation A' B' ∧
      Hypergraph.separationOrder A' B' ≤ Hypergraph.separationOrder A B ∧
      (∀ e ∈ A'.edgeSet, e ⊆ Λ) ∧
      ∀ e ∈ H.E, e ⊆ closure M → e ∈ A'.edgeSet := by
  let C := (PaintingOrDrawing.drawing H).inter (closure M)
  let D := ((PaintingOrDrawing.drawing H).inter (univ \ M)).deleteEdges C.edgeSet
  let E := ((PaintingOrDrawing.drawing H).inter (closure Λ)).deleteEdges
    ((PaintingOrDrawing.drawing H).inter (univ \ Λ)).edgeSet
  let F := (PaintingOrDrawing.drawing H).inter (univ \ Λ)
  have hCD : H.toHypergraph.IsSeparation C D := (zone_cut_separations hM).1
  have hEF : H.toHypergraph.IsSeparation E F := (zone_cut_separations hΛ).2
  have hCE : C.edgeSet ⊆ E.edgeSet := by
    intro e he
    change e ∈ H.E ∧ e ⊆ closure M at he
    change (e ∈ H.E ∧ e ⊆ closure Λ) ∧ ¬ (e ∈ H.E ∧ e ⊆ univ \ Λ)
    refine ⟨⟨he.1, he.2.trans (hNest.trans subset_closure)⟩, ?_⟩
    intro hnot
    obtain ⟨x, hxe⟩ := he.1.1
    exact (hnot.2 hxe).2 (hNest (he.2 hxe))
  have hCF : Disjoint C.vertexSet F.vertexSet := by
    apply disjoint_left.mpr
    rintro x ⟨_, hxM⟩ ⟨_, _, hxΛ⟩
    exact hxΛ (hNest hxM)
  have hInner' : C.vertexSet ∩ D.vertexSet ⊆ A.vertexSet := by
    rintro x ⟨⟨hxH, hxCl⟩, _, _, hxNot⟩
    exact hInner ⟨hxH, hxCl, subset_closure ⟨mem_univ _, hxNot⟩⟩
  have hOuter' : E.vertexSet ∩ F.vertexSet ⊆ B.vertexSet := by
    rintro x ⟨⟨hxH, hxCl⟩, _, _, hxNot⟩
    exact hOuter ⟨hxH, hxCl, subset_closure ⟨mem_univ _, hxNot⟩⟩
  obtain ⟨hSep', hCutSub, hEdgesIn, hLeE⟩ :=
    uncross_annular_separation hSep hCD hEF hCE hCF hInner' hOuter'
  refine ⟨(A ∪ C) ∩ E, (B ∩ D) ∪ F, hSep', ?_, ?_, ?_⟩
  · exact ncard_le_ncard hCutSub (A ∩ B).vertexSet_finite
  · intro e he
    have heE := hLeE.2 he
    change (e ∈ H.E ∧ e ⊆ closure Λ) ∧ ¬ (e ∈ H.E ∧ e ⊆ univ \ Λ) at heE
    rcases edge_subset_or_subset_compl_of_zone hΛ heE.1.1 with heIn | heOut
    · exact heIn
    · exact False.elim (heE.2 ⟨heE.1.1, heOut⟩)
  · intro e heH heM
    exact hEdgesIn ⟨heH, heM⟩

end GraphMinor.GM16
