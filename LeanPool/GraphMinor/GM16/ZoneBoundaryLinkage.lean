/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM16.PathBoundaryIntersection
import LeanPool.GraphMinor.GM16.LineBoundarySide
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section88
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# Keeping a boundary linkage inside its zone

Trim each path from an interior vertex set to the zone boundary so
that it meets each end set only at its end. A trimmed path has just
one vertex on the outer circle and therefore just one point there.
Removing that point shows that the path stays in the closed disc.
This puts Claim (10)'s linkage in the society used for XVI (8.1),
Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- Disjoint paths to a zone boundary can be trimmed into the closed
zone, with exactly one vertex on each of the two end sets. -/
theorem linkage_inside_closed_zone {H : Drawing S}
    {d : Set S → Set S → ℕ} {γ p : ℕ} {z Λ A : Set S}
    (hZone : IsLambdaZoneAround H d γ z Λ) (hA : A ⊆ Λ)
    (P : Fin p → Drawing S)
    (hP : ∀ i, ∃ a ∈ A, ∃ b ∈ H.V ∩ subBd Λ,
      (P i).IsPathBetween a b ∧ (P i).IsSubdrawing H)
    (hDis : Pairwise (fun i j => Disjoint (P i).V (P j).V)) :
    ∃ Q : Fin p → Graph S (Set S),
      (∀ i, IsFromToPath (H.interSet (closure Λ)).toGraph (Q i)
        (H.V ∩ subBd Λ) A) ∧
      Pairwise (fun i j => Disjoint V(Q i) V(Q j)) := by
  classical
  let B := H.interSet (subBd Λ)
  have hBH : B.IsSubdrawing H := interSet_isSub
  have hBU : B.U = subBd Λ := by
    apply subset_antisymm
    · exact interSet_U_subset (by rw [subBd_eq_frontier]; exact isClosed_frontier)
    · exact oArc_subset_interSet_U hZone.isOArc_bd hZone.bd_subset_U Subset.rfl
  have hBD : Disjoint Λ (subBd Λ) :=
    (isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1).1
  have hTrim (i : Fin p) : ∃ b ∈ H.V ∩ subBd Λ, ∃ a ∈ A,
      ∃ J : Drawing S, J.IsPathBetween b a ∧ J.IsSubdrawing H ∧
        J.IsSubdrawing (P i) ∧ J.V ∩ (H.V ∩ subBd Λ) = {b} ∧
        J.V ∩ A = {a} ∧ J.U ⊆ closure Λ := by
    obtain ⟨a, ha, b, hb, hPath, hPH⟩ := hP i
    obtain ⟨b', hb', a', ha', R, hRP, hR⟩ :=
      (graphPath_of_drawingPath hPH hPath).symm.exists_isFromToPathWithEnds hb ha
    obtain ⟨J, hJPath, hJH, hJR⟩ := exists_drawing_of_graphPath hR.1
    have hJP : J.IsSubdrawing (P i) := by
      constructor
      · intro x hx
        exact hRP.vertexSet_mono (hJR ▸ hx)
      · intro e he
        exact hRP.edgeSet_mono (hJR ▸ he)
    have hOuter : J.V ∩ (H.V ∩ subBd Λ) = {b'} := by
      change V(J.toGraph) ∩ (H.V ∩ subBd Λ) = {b'}
      rw [hJR]
      exact hR.2.1
    have hInner : J.V ∩ A = {a'} := by
      change V(J.toGraph) ∩ A = {a'}
      rw [hJR]
      exact hR.2.2
    have hJbd : J.U ∩ subBd Λ ⊆ {b'} := by
      rw [← hBU]
      apply path_inter_subdrawing_subset_singleton hJH hBH hJPath
      rw [hBU]
      intro x hx
      exact hOuter ▸ ⟨hx.1, hJH.1 hx.1, hx.2⟩
    have hne : b' ≠ a' := fun heq => hBD.notMem_of_mem_left (hA ha') (heq ▸ hb'.2)
    have hLine := GM11.isLine_of_isPathBetween hJPath hne
    have hJU : J.U ⊆ closure Λ := by
      apply line_subset_closed_of_boundary_end isClosed_closure
        (Surface.IsLineWithEnds.symm hLine) (subset_closure (hA ha')) hne.symm hb'.2.1
      intro x hx
      rw [subBd_eq_frontier] at hJbd
      exact hJbd ⟨hx.1, frontier_closure_subset hx.2⟩
    exact ⟨b', hb', a', ha', J, hJPath, hJH, hJP, hOuter, hInner, hJU⟩
  choose b hb a ha J hJPath hJH hJP hOuter hInner hJU using hTrim
  refine ⟨fun i => (J i).toGraph, ?_, ?_⟩
  · intro i
    refine ⟨b i, a i, ?_, hOuter i, hInner i⟩
    exact graphPath_of_drawingPath
      (subdrawing_interSet_of_U_subset (hJH i) (hJU i)) (hJPath i)
  · intro i j hij
    exact (hDis hij).mono (hJP i).1 (hJP j).1

end GraphMinor.GM16
