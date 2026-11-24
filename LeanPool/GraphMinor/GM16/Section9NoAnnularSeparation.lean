/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9ZoneSeparation
import LeanPool.GraphMinor.GM16.Section9RadialBoundary
import LeanPool.GraphMinor.GM16.Section9RadialObstruction
import LeanPool.GraphMinor.GM16.DrawingConnected
import LeanPool.GraphMinor.GM11.RadialFacts
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM12.Section4WalkMetric
import LeanPool.GraphMinor.GM14.Section7b

/-!
# No small separator between the nested zone boundaries

The radial form of the planar Menger step in XVI (8.1), Claim (10),
marks the radial regions of the inner separation side. That side is
small in the tangle. Its radial boundary captures an edge at the
centre, so one of its circuits encloses the inner open zone. The
circuit has at most twice as many edges as separator vertices. The
short radial enclosure contradiction then rules it out.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The small-separator contradiction in the planar Menger step of
XVI (8.1), Claim (10), page 73. The separation has already been moved
into the annulus by `exists_annular_separation`. -/
theorem section9_no_annular_separation (hS : IsClosedSurface S)
    {H : Drawing S} {θ γ κ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {y : S} {Λ M : Set S} {A B : Hypergraph S (Set S)}
    (hMet : HasTangleMetric H θ T d) (hy : y ∈ H.V)
    (hΛ : IsLambdaZoneAround H d γ {y} Λ)
    (hM : IsLambdaZoneAround H d (κ + 2) {y} M)
    (hCapture : ∀ a ∈ H.A, d {y} a < κ → a ⊆ M)
    (_hκ : 3 ≤ κ) (hOrder : κ + γ < θ)
    (hSep : H.toHypergraph.IsSeparation A B) (hSmallOrder : Hypergraph.separationOrder A B < κ)
    (hOuter : ∀ e ∈ A.edgeSet, e ⊆ Λ)
    (hInner : ∀ e ∈ H.E, e ⊆ closure M → e ∈ A.edgeSet) : False := by
  have hθ : 2 ≤ θ := by omega
  have hAB : (A, B) ∈ T := separation_mem_of_edges_in_zone hS hMet hθ hy hΛ hSep
    (by omega) (fun e he => (hOuter e he).trans subset_closure)
  obtain ⟨hResp, K, ins, hK, hd, hMetric⟩ := hMet
  have hMet : HasTangleMetric H θ T d := ⟨hResp, K, ins, hK, hd, hMetric⟩
  have hE := edges_nonempty_of_tangle hS hMet.1 hθ
  have hFacts := regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  have hInd := (theorem_6_3_of_regionFacts (Γ := PaintingOrDrawing.drawing H) hS
    hMet.1.2.1.isPretangle hK.2.1 hd hFacts).2
  have hMem : (A, B) ∈ inducedPretangle (PaintingOrDrawing.drawing H) K θ ins := hInd ▸ hAB
  have hSmall := hMem.2.2
  let N := boundaryDrawing K (PaintingOrDrawing.regionsIncludingEdge K A)
  have hNK : N.IsSubdrawing K := Drawing.span_isSubdrawing K _ _
  have hAnnulus := radial_boundary_in_annulus hS hK hE hΛ hM hSep hOuter hInner
  obtain ⟨e, he, hye⟩ := exists_edge_of_regionFacts hS hFacts hy
  have heM : e ⊆ M := by
    rcases edge_subset_or_subset_compl_of_zone hM he with hIn | hOut
    · exact hIn
    · have hyOut := closure_minimal hOut (isClosed_univ.sdiff hM.isOpenDisc.1) hye
      exact False.elim (hyOut.2 (hM.z_subset (mem_singleton y)))
  have heA : e ∈ A.edgeSet := hInner e he (heM.trans subset_closure)
  obtain ⟨r, hr, heR⟩ := radial_region_of_edge hK he
  obtain ⟨D, hD, hDN, hLen, hRIns⟩ := hSmall.2 r ⟨hr, e, heA, heR⟩
  have hDK := hDN.trans hNK
  have hCut : D.V ∩ H.V ⊆ (A ∩ B).vertexSet := by
    rintro x ⟨hxD, hxH⟩
    exact boundary_vertex hS hFacts hSep hxH (hDN.1 hxD)
  have hCount := ncard_le_ncard hCut (A ∩ B).vertexSet_finite
  have hLength := (circuit_length_eq_two_mul_ncard hK.2.1 hD hDK).1
  have hShort : D.length < 2 * κ := by
    change (D.V ∩ H.V).ncard ≤ Hypergraph.separationOrder A B at hCount
    omega
  have hDU : D.U ⊆ closure Λ := hDN.U_subset.trans hAnnulus.1
  have hDM : Disjoint D.U M := hAnnulus.2.mono hDN.U_subset Subset.rfl
  obtain ⟨hIns, hInsBd, _⟩ := hd D hD hDK hLen
  have hfr : frontier (ins D) = D.U := by rw [← subBd_eq_frontier, hInsBd]
  have hMIns : M ⊆ ins D := by
    obtain ⟨x, hxe⟩ := he.1
    exact subset_of_disjoint_frontier hM.isOpenDisc.isPathConnected.isConnected.isPreconnected
      hIns.isClosed (hfr ▸ hDM.symm) (heM hxe) (hRIns (heR hxe))
  have hInsOut := GraphMinor.GM14.theorem_7_5_proof H K D θ γ T d ins {y} Λ
    hS inferInstance hMet hK hd hΛ hD hDK hDU (by omega)
  have hBd : discBd (ins D) = D.U := by
    rw [← GraphMinor.GM11.IsClosedDisc.frontier_eq_discBd hS hIns, hfr]
  obtain ⟨_, _, _, hSymm, _, _⟩ := GraphMinor.GM11.gm15_theorem_9_1 H θ T d hS inferInstance hMet
  exact section9_no_short_radial_enclosure hS hMet hK hd hMetric hy
    (hM.z_subset (mem_singleton y)) hΛ hCapture hSymm (by omega) hD hDK hShort hDU
    hIns hInsOut hBd (fun x hx => ⟨hMIns hx, hDM.notMem_of_mem_right hx⟩)

end GraphMinor.GM16
