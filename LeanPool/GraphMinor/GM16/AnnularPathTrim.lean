/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM16.LineBoundarySide
import LeanPool.GraphMinor.GM16.Section9Attachments
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Section7
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# Trimming a path at an inner circle

Keep the subpath from its outside end to its first vertex on the
inner circle. It has no other vertex on that circuit and no edge of
the circuit, so its point set also meets the circle only at that end.
Connectedness then keeps it outside the inner disc. This is the
trimming used for linkedness in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- A path from an inner circle to a point outside its closed disc
has a terminal subpath lying outside the disc interior. -/
theorem exists_annular_terminal_path {H C P : Drawing S} {D E : Set S} {a b : S}
    (hC : C.IsSubdrawing H) (hP : P.IsSubdrawing H)
    (hPath : P.IsPathBetween a b) (ha : a ∈ C.V)
    (hD : IsClosed D) (hBd : frontier D = C.U) (hb : b ∉ D)
    (hPE : P.U ⊆ E) :
    ∃ c ∈ C.V, ∃ J : Drawing S,
      J.IsPathBetween b c ∧ J.IsSubdrawing P ∧
      J.U ⊆ E \ interior D ∧ J.V ∩ C.V = {c} ∧ J.U ∩ C.U = {c} := by
  have hPG := graphPath_of_drawingPath hP hPath
  obtain ⟨b', hb', c, hc, R, hRP, hR⟩ :=
    hPG.symm.exists_isFromToPathWithEnds (mem_singleton b) ha
  have hbb : b' = b := mem_singleton_iff.mp hb'
  subst b'
  obtain ⟨J, hJPath, hJH, hJR⟩ := exists_drawing_of_graphPath hR.1
  have hJP : J.IsSubdrawing P := by
    constructor
    · intro x hx
      have hxR : x ∈ V(R) := hJR ▸ hx
      exact hRP.vertexSet_mono hxR
    · intro e he
      have heR : e ∈ E(R) := hJR ▸ he
      exact hRP.edgeSet_mono heR
  have hJV : J.V ∩ C.V = {c} := by
    change V(J.toGraph) ∩ V(C.toGraph) = {c}
    rw [hJR]
    exact hR.2.2
  have hEdges : Disjoint J.E C.E := by
    change Disjoint E(J.toGraph) E(C.toGraph)
    rw [hJR]
    exact path_edges_disjoint_of_singleton_inter
      (toGraph_le_of_isSubdrawing hC) hR.1 hR.2.2.subset
  have hInter : J.U ∩ frontier D = {c} := by
    rw [hBd, U_inter_of_disjoint hJH hC hEdges, hJV]
  have hbc : b ≠ c := by
    intro heq
    have hcD : c ∈ D := hD.frontier_subset (hBd.symm ▸ C.V_subset_U hc)
    exact hb (heq.symm ▸ hcD)
  have hLine := isLine_of_isPathBetween hJPath hbc
  have hAvoid : Disjoint J.U (interior D) :=
    line_avoids_interior_of_boundary_start hD (Surface.IsLineWithEnds.symm hLine)
      (hBd.symm ▸ C.V_subset_U hc) hb hInter.subset
  refine ⟨c, hc, J, hJPath, hJP, ?_, hJV, ?_⟩
  · intro x hx
    exact ⟨hPE (hJP.U_subset hx), fun hxi => hAvoid.notMem_of_mem_left hx hxi⟩
  · rwa [hBd] at hInter

end GraphMinor.GM16
