/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CliquePortGraph
public import LeanPool.GraphMinor.GM12.Section4SubdivisionCrossingModel
public import LeanPool.GraphMinor.GM12.Section4SubdivisionMeetings
public import LeanPool.GraphMinor.GM12.Section4SubdivisionIntersections
public import LeanPool.GraphMinor.GM12.Section4SubdivisionNoncrossing
import LeanPool.GraphMinor.GM12.Section4CliqueCrossingArcs
import LeanPool.GraphMinor.GM12.Section4FamilySubdivision
import LeanPool.GraphMinor.GM12.Section4CrossingMultiplicity

/-!
# The complete one-crossing source for the clique minor

This assembles the source construction of XII (4.5), pages
252--253, with no construction step as a hypothesis. Draw the
clique using the Hamilton-cycle port order, subdivide between
successive crossings, and identify the shared original ends.
The resulting finite graph has the clique as a minor, every
edge crosses exactly once, and every vertex has two incident
edges which do not cross each other. Every crossing has the
local straight-line model used to choose its small disc.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph

/-- The actual finite one-crossing source graph and all its
geometric properties in XII (4.5), pages 252--253. The graph,
subdivision, clique minor, crossing count, noncrossing incident
pairs, and local coordinates are all constructed here. -/
theorem exists_clique_one_crossing_source {p : ℕ} (hp : 4 ≤ p) :
    ∃ (W F : Type) (L : Graph W F) (v : W → ℂ) (ends : F × Bool → W) (P : F → Set ℂ),
      Finite W ∧ Finite F ∧ IsIsoMinor (GM16.completeGraph p) L ∧ Function.Injective v ∧
      L.vertexSet = univ ∧ L.edgeSet = univ ∧
      (∀ e, L.IsLink e (ends (e, false)) (ends (e, true))) ∧
      (∀ e, IsLineWithEnds (P e) (v (ends (e, false))) (v (ends (e, true)))) ∧
      (∀ e w, v w ∈ P e ↔ w = ends (e, false) ∨ w = ends (e, true)) ∧
      (∀ e f, e ≠ f → (P e ∩ P f).Finite) ∧
      (∀ e f g, e ≠ f → f ≠ g → e ≠ g → P e ∩ P f ∩ P g ⊆ range v) ∧
      (∀ e, ∃ x ∈ edgeMeetingPoints v P, P e ∩ edgeMeetingPoints v P = {x}) ∧
      (∀ w, ∃ e f, e ≠ f ∧ P e ∩ P f = {v w}) ∧
      (edgeMeetingPoints v P).Finite ∧ 2 ≤ (edgeMeetingPoints v P).ncard ∧ Nat.card F = 2 *
        (edgeMeetingPoints v P).ncard ∧
      ∀ x ∈ edgeMeetingPoints v P, ∃ e f, e ≠ f ∧ x ∈ P e ∩ P f ∧
        ∃ (A : ℂ ≃L[ℝ] ℂ) (U : Set ℂ), IsOpen U ∧ x ∈ U ∧
          P e ∩ U = (line[ℝ, x, x + A 1] : Set ℂ) ∩ U ∧
          P f ∩ U = (line[ℝ, x, x + A Complex.I] : Set ℂ) ∩ U := by
  classical
  obtain ⟨ψ, hψ, V, s, E, _, hV, _, hs, _, hEline, hEvertex, hchord, hfinite,
    hEinter, htriple, hcross, htwo, _, _, _, _⟩ := exists_clique_crossing_arcs hp
  let κ := fun q => (ψ q).val.1
  obtain ⟨k, hk, w, P, hw, hw0, hwlast, hPline, hcover, hmeet, havoid, hinter, hPvertices,
    _, hcount⟩ := exists_family_one_meeting_subdivision V κ E hEline hfinite htriple hcross
  let W := SubdivisionVertex p (p * (p - 1) / 2) k
  let F := Σ e : Fin (p * (p - 1) / 2), Fin (k e)
  let L := subdivisionGraph κ k
  let v := subdivisionPosition V k w
  let P' := subdivisionEdgeArc k P
  let ends : F × Bool → W := fun q =>
    if q.2 then subdivisionVertexAt κ k q.1.1 q.1.2.succ
    else subdivisionVertexAt κ k q.1.1 q.1.2.castSucc
  have hmem := family_cut_mem_original_edge E k hk w P hPline hcover
  have hinternal := internal_family_cut_not_mem_vertices V κ E k w hw hw0 hwlast hmem hEvertex
  have hvinj := subdivisionPosition_injective V E k w hV hw hmem havoid hinternal
  have hM := edgeMeetingPoints_subdivision_eq V κ E k hk w P hw0 hwlast hPline hcover havoid hinter
  have hMfinite : (edgeMeetingPoints v P').Finite := by
    rw [hM]
    exact finite_edgeMeetingPoints V E hfinite
  refine ⟨W, F, L, v, ends, P', inferInstance, inferInstance,
    completeGraph_isIsoMinor_port_subdivision ψ hψ k hk, hvinj, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hMfinite, ?_, ?_, ?_⟩
  · intro e
    exact subdivisionGraph_isLink κ k e.1 e.2
  · intro e
    exact subdivisionEdgeArc_isLine V κ k hk w P hw0 hwlast hPline e
  · intro e z
    change subdivisionPosition V k w z ∈ subdivisionEdgeArc k P e ↔
      z = subdivisionVertexAt κ k e.1 e.2.castSucc ∨ z = subdivisionVertexAt κ k e.1 e.2.succ
    rw [subdivisionEdgeArc_vertex_inc_iff V κ E k hk w P hV hw hw0 hwlast hPline hcover
      havoid hPvertices hEvertex, subdivisionGraph_inc_iff]
  · intro e f hef
    exact finite_subdivisionEdgeArc_inter E k w P hcover hinter hfinite hef
  · exact subdivisionEdgeArcs_triple_subset_vertices V κ E k hk w P hw0 hwlast hcover hinter htriple
  · exact subdivisionEdgeArc_one_meeting V κ E k hk w P hw0 hwlast hPline hcover havoid hinter hmeet
  · exact subdivision_has_two_noncrossing_arcs V E k w P hw hPline hcover hinter hPvertices htwo
  · let z : W := Sum.inl ⟨0, by omega⟩
    obtain ⟨e, f, _, hef⟩ := subdivision_has_two_noncrossing_arcs V E k w P hw
      hPline hcover hinter hPvertices htwo z
    exact two_le_ncard_meetings_of_noncrossing_pair v P' hMfinite
      (subdivisionEdgeArc_one_meeting V κ E k hk w P hw0 hwlast hPline hcover havoid hinter hmeet)
        hef
  · rw [Nat.card_eq_fintype_card, hM]
    exact hcount
  · intro x hx
    have hxold : x ∈ edgeMeetingPoints V E := hM ▸ hx
    obtain ⟨e, f, i, j, hef, hxP, A, U, hU, hxU, hl, hr⟩ :=
      exists_subdivision_crossing_model V E s hs hchord hEinter k w P hPline hcover havoid hinter
        hxold
    exact ⟨⟨e, i⟩, ⟨f, j⟩, (fun h => hef (congrArg Sigma.fst h)), hxP, A, U, hU, hxU, hl, hr⟩

end GraphMinor.GM12
