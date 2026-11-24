/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.DrawingConnected
import LeanPool.GraphMinor.GM16.ClearedPathVertices
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM16.ZoneBoundaryLinkage
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM16.Section9BoundaryVertices
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section88

/-!
# Exit paths from the cleared discs

Take a path from an interior vertex to the drawn zone boundary and
stop at its first boundary vertex. It stays in the closed zone and
has no other boundary vertex. For a disjoint envelope this is also
its only vertex in the final cleared drawing. These are the paths
`P_y` and the terminal exit paths in XVI (7.1), Claims (5) and (6),
pages 69–70.
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- A vertex in a zone has a path to its boundary with just its last
vertex there, and with its entire point set in the closed zone. -/
theorem exists_zone_exit_path (hS : IsClosedSurface S) {H : Drawing S}
    (hH : (PaintingOrDrawing.drawing H).IsTwoCell)
    {d : Set S → Set S → ℕ} {γ : ℕ} {z Λ : Set S}
    (hZone : IsLambdaZoneAround H d γ z Λ) {s : S} (hs : s ∈ H.V) (hsΛ : s ∈ Λ) :
    ∃ p ∈ H.V ∩ subBd Λ, ∃ P : Drawing S,
      P.IsPathBetween s p ∧ P.IsSubdrawing H ∧ P.U ⊆ closure Λ ∧
      P.V ∩ (H.V ∩ subBd Λ) = {p} := by
  have hC := interSet_isCircuit_of_oArc hZone.isOArc_bd hZone.bd_subset_U
  obtain ⟨b, W, _, _, hV, _⟩ := hC
  have hb : b ∈ H.V ∩ subBd Λ := by
    have hbV : b ∈ (H.interSet (subBd Λ)).V := hV.symm ▸ W.start_mem_support
    exact (GraphMinor.GM11.mem_interSet_V_iff
      (by rw [subBd_eq_frontier]; exact isClosed_frontier)).mp hbV
  obtain ⟨W₀⟩ := drawing_walk_of_twoCell hS hH hs hb.1
  obtain ⟨P₀, hP₀, _, _⟩ := exists_isGraphPathWithEnds_of_walk W₀
  obtain ⟨L, hL, hLH, _⟩ := exists_drawing_of_graphPath hP₀
  have hA : ({s} : Set S) ⊆ Λ := singleton_subset_iff.mpr hsΛ
  obtain ⟨Q, hQ, _⟩ := linkage_inside_closed_zone hZone hA (fun _ : Fin 1 => L)
    (fun _ => ⟨s, rfl, b, hb, hL, hLH⟩)
    (fun i j hij => False.elim (hij (Subsingleton.elim i j)))
  obtain ⟨p, s', hR⟩ := hQ 0
  have hp : p ∈ H.V ∩ subBd Λ := (hR.2.1 ▸ (show p ∈ ({p} : Set S) from rfl)).2
  have hs's : s' = s := (hR.2.2 ▸ (show s' ∈ ({s'} : Set S) from rfl)).2
  subst s'
  obtain ⟨P, hP, hPH, hPQ⟩ := exists_drawing_of_graphPath hR.1.symm
  refine ⟨p, hp, P, hP, hPH.trans interSet_isSub,
    fun _ hx => interSet_U_subset isClosed_closure (hPH.U_subset hx), ?_⟩
  change V(P.toGraph) ∩ (H.V ∩ subBd Λ) = {p}
  rw [hPQ]
  exact hR.2.1

/-- The exit path from an envelope centre meets the final cleared
drawing just in its boundary end. This is `P_y` in XVI (7.1). -/
theorem exists_envelope_centre_exit (hS : IsClosedSurface S) {H : Drawing S}
    (hH : (PaintingOrDrawing.drawing H).IsTwoCell)
    {d : Set S → Set S → ℕ} {γ : ℕ} {Y : Set S} {Λ : S → Set S}
    (hEnv : IsEnvelope H d Y γ Λ) {y : S} (hy : y ∈ Y) :
    ∃ p ∈ (clearEnvelopeDrawing H Y Λ).V, p ∈ subBd (Λ y) ∧ ∃ P : Drawing S,
      P.IsPathBetween y p ∧ P.IsSubdrawing H ∧ P.U ⊆ closure (Λ y) ∧
      P.V ∩ (clearEnvelopeDrawing H Y Λ).V = {p} ∧ d {y} {p} ≤ γ := by
  have hZone := hEnv.2.1 y hy
  obtain ⟨p, hp, P, hP, hPH, hPU, hOuter⟩ := exists_zone_exit_path hS hH hZone
    (hEnv.1 hy) (hZone.z_subset (mem_singleton y))
  have hpClear := boundary_vertex_mem_clearFamily hEnv.2.1 hEnv.2.2.1 hy hp
  refine ⟨p, hpClear, hp.2, P, hP, hPH, hPU, ?_, ?_⟩
  · apply subset_antisymm
    · rintro x ⟨hxP, hxClear⟩
      have hxOut := (clearFamily_U hEnv.2.1 ▸ (clearEnvelopeDrawing H Y Λ).V_subset_U hxClear).2
      have hxNot : x ∉ Λ y := fun h => hxOut (mem_iUnion₂.mpr ⟨y, hy, h⟩)
      have hxBd : x ∈ subBd (Λ y) := ⟨hPU (P.V_subset_U hxP), subset_closure ⟨mem_univ _, hxNot⟩⟩
      exact hOuter ▸ ⟨hxP, hPH.1 hxP, hxBd⟩
    · rintro x rfl
      exact ⟨(graphPath_of_drawingPath hPH hP).right_mem, hpClear⟩
  · exact hZone.dist_le {p} (Or.inl (Or.inl ⟨p, hp.1, rfl⟩))
      (singleton_subset_iff.mpr hp.2.1)

/-- Every old vertex has a terminal exit path to the cleared drawing.
If it was cleared, the exit stays in one envelope disc. Its endpoint
is at distance at most twice the envelope radius. This is `R_y` in
XVI (7.1), Claim (6), page 70. -/
theorem exists_envelope_vertex_exit (hS : IsClosedSurface S) {H : Drawing S}
    {θ γ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {Y : Set S} {Λ : S → Set S}
    (hMet : HasTangleMetric H θ T d) (hEnv : IsEnvelope H d Y γ Λ)
    {x : S} (hx : x ∈ H.V) :
    ∃ p ∈ (clearEnvelopeDrawing H Y Λ).V, ∃ P : Drawing S,
      P.IsPathBetween x p ∧ P.IsSubdrawing H ∧
      P.V ∩ (clearEnvelopeDrawing H Y Λ).V = {p} ∧ d {x} {p} ≤ 2 * γ := by
  classical
  obtain ⟨_, hSelf, _, hSymm, hTri, _⟩ := GM11.gm15_theorem_9_1 H θ T d hS inferInstance hMet
  by_cases hxClear : x ∈ (clearEnvelopeDrawing H Y Λ).V
  · let W : GraphWalk H.toGraph x x := .nil hx
    let P := walkDrawing H W
    have hsW : W.support = [x] := Surface.GraphWalk.support_nil hx
    have hW : W.IsSimple := by
      change W.support.Nodup
      rw [hsW]
      exact List.nodup_singleton x
    have hPV : P.V = {x} := by
      rw [show P.V = {z | z ∈ W.support} from walkDrawing_V H W, hsW]
      ext z
      simp only [mem_ofPred_eq, List.mem_singleton, mem_singleton_iff]
    refine ⟨x, hxClear, P, walkDrawing_isPathBetween H hW, walkDrawing_isSubdrawing H W, ?_, ?_⟩
    · rw [hPV]
      exact inter_eq_left.mpr (singleton_subset_iff.mpr hxClear)
    · rw [hSelf {x} (Or.inl (Or.inl ⟨x, hx, rfl⟩))]
      exact Nat.zero_le _
  · have hxIn : x ∈ ⋃ y ∈ Y, Λ y := by
      by_contra hOut
      exact hxClear (mem_clearFamily_of_notMem_union hx hOut)
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hxIn
    have hZone := hEnv.2.1 y hy
    obtain ⟨p, hp, P, hP, hPH, hPU, hOuter⟩ :=
      exists_zone_exit_path hS hMet.1.1 hZone hx hxy
    have hpClear := boundary_vertex_mem_clearFamily hEnv.2.1 hEnv.2.2.1 hy hp
    refine ⟨p, hpClear, P, hP, hPH, ?_, ?_⟩
    · apply subset_antisymm
      · rintro z ⟨hzP, hzClear⟩
        have hzOut := (clearFamily_U hEnv.2.1 ▸ (clearEnvelopeDrawing H Y Λ).V_subset_U hzClear).2
        have hzNot : z ∉ Λ y := fun h => hzOut (mem_iUnion₂.mpr ⟨y, hy, h⟩)
        have hzBd : z ∈ subBd (Λ y) := ⟨hPU (P.V_subset_U hzP), subset_closure ⟨mem_univ _, hzNot⟩⟩
        exact hOuter ▸ ⟨hzP, hPH.1 hzP, hzBd⟩
      · rintro z rfl
        exact ⟨(graphPath_of_drawingPath hPH hP).right_mem, hpClear⟩
    · have hxA : ({x} : Set S) ∈ H.A := Or.inl (Or.inl ⟨x, hx, rfl⟩)
      have hpA : ({p} : Set S) ∈ H.A := Or.inl (Or.inl ⟨p, hp.1, rfl⟩)
      have hyA := hZone.z_mem
      have hdx := hZone.dist_le {x} hxA (singleton_subset_iff.mpr (subset_closure hxy))
      have hdp := hZone.dist_le {p} hpA (singleton_subset_iff.mpr hp.2.1)
      have htri := hTri {x} hxA {y} hyA {p} hpA
      rw [hSymm {x} hxA {y} hyA] at htri
      omega

end GraphMinor.GM16
