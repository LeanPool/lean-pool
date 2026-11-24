/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2DeformationConclusion
public import LeanPool.GraphMinor.GM12.Section2PartitionDeformation
public import LeanPool.GraphMinor.GM12.Section2TraceSubdivision
import LeanPool.GraphMinor.GM12.Section2VisitCarrier
import LeanPool.GraphMinor.GM12.Section2DistinctVisits
import LeanPool.GraphMinor.GM12.Section2DistinctRegionPaths
import LeanPool.GraphMinor.GM12.Section2TraceDeterminacy
import LeanPool.GraphMinor.GM12.Section2TraceImage
import LeanPool.GraphMinor.GM12.Section2PeriodicHits
import LeanPool.GraphMinor.GM12.Section2

/-!
# Case 1 of Graph Minors XII (2.1)

If every region intersection of the original simple circle is
connected, its ordered region visits are distinct. Deform each
visit to its two spokes and join these deformations around the
circle. Trace determinacy identifies the resulting drawing with
the original trace. The joined curve is embedded unless a visit
backtracks along one spoke. Such a visit has equal ends, so the
original embedded circle has only one vertex visit and the whole
trace is a line. Apply the selected-inside comparison in the circle
case, and the contraction argument in the line case. This follows
Case 1 on page 244, making its continuous deformation explicit.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM07

/-- Graph Minors XII, (2.1), Case 1, page 244. If each region
intersection of the embedded original curve is preconnected, every
atom meeting its selected inside meets the trace inside. -/
theorem theorem_2_1_case1
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {φ : C(Circle, S)} (hφ : IsEmbedding φ) {u : S} (W : GraphWalk K.toGraph u u)
    (hW : IsTrace Γ K φ W) (hpos : 0 < curveLength Γ φ) (hlen : curveLength Γ φ < θ)
    (hconn : ∀ r ∈ Γ.R, IsPreconnected (range φ ∩ r))
    {D c : Set S} (hD : IsClosedDisc D) (hbdD : subBd D = range φ)
    (hmD : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hc : c ∈ Γ.A) (hcD : (c ∩ D).Nonempty) :
    (c ∩ insWalk ins K W).Nonempty := by
  obtain ⟨n, t, r, hn, ht, hperiod, _, hΓ, hsteps, hr, hfr⟩ := exists_trace_subdivision W hW hpos
  obtain ⟨Z, hφZ, hrZ, hZorig, hZregion⟩ := exists_region_visit_carrier t hperiod hΓ r hr hfr
  have hfu := (traceSteps_parameters W hsteps).2.1
  have hdeform := exists_partition_trace_deformation hS hK hE hφZ hn t ht hperiod hΓ r hr hrZ hfr
  rw [hfu] at hdeform
  obtain ⟨δ, hmatch, Q, hQ, _, hψUQ, hh, hδ0, hδ1, hδr, halt⟩ := hdeform
  let ψ := concatLoop hn δ hmatch
  have hWQ := traceSteps_drawing_unique hS inferInstance hK (periodicCurve_continuous φ) W Q hsteps
    hQ
  have hψU : range ψ = (walkDrawing K W).U := hψUQ.trans (congrArg Drawing.U hWQ.symm)
  have hZΓ : Z ∩ Γ.U ⊆ range ψ := by
    intro x hx
    have hxW := trace_vertex_in_image W hW (hZorig hx).1 (hZorig hx).2
    have hxU : x ∈ (walkDrawing K W).U := by
      apply (walkDrawing K W).V_subset_U
      rw [walkDrawing_V]
      exact hxW
    exact hψU.symm ▸ hxU
  have hZR : ∀ R ∈ Γ.R, (Z ∩ R).Nonempty → (range ψ ∩ R).Nonempty := by
    intro R hR hmeet
    obtain ⟨i, hRi⟩ := hZregion R hR hmeet
    subst R
    let half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    refine ⟨δ i half, ?_, hδr i half (by change (0 : ℝ) < 1 / 2; norm_num)
      (by change (1 / 2 : ℝ) < 1; norm_num)⟩
    change δ i half ∈ range (concatLoop hn δ hmatch)
    rw [range_concatLoop]
    exact mem_iUnion.mpr ⟨i, half, rfl⟩
  have hVi := vertex_visits_injective hφ.injective t ht hperiod
  by_cases hall : ∀ i, InjOn (δ i) (Ico (0 : unitInterval) 1)
  · have hRi := region_visits_injective hφ hconn t ht hperiod hΓ r hr hfr
    have hψ := concatLoop_isEmbedding_of_distinct_regions hn (fun i => hΓ i.castSucc)
      hVi hr hRi δ hall hδ0 hδr hmatch
    exact meets_insWalk_of_embedded_trace_deformation hS hT hK hd hφ hψ hW.1.2 W
      (theorem_2_1_length hW hlen) hψU hD hbdD hmD hh hZΓ hZR hc hcD
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    rcases halt i with h | ⟨heq, L, hL, hδL, _⟩
    · exact (hi h).elim
    · have hn1 : n = 1 := by
        by_contra hn1
        have hn2 : 2 ≤ n := by omega
        have hnext := hVi (heq.trans (periodic_value_succ_eq_next (periodicCurve_periodic φ) hn t
          hperiod i))
        exact finNext_ne_of_two_le hn2 i hnext.symm
      have hji : ∀ j : Fin n, j = i := by
        intro j
        apply Fin.ext
        have hj := j.isLt
        have hi := i.isLt
        omega
      have hψL : range ψ = L := by
        change range (concatLoop hn δ hmatch) = L
        rw [range_concatLoop]
        have hu : (⋃ j, range (δ j)) = range (δ i) := by
          ext x
          constructor
          · intro hx
            obtain ⟨j, hj⟩ := mem_iUnion.mp hx
            exact hji j ▸ hj
          · intro hx
            exact mem_iUnion.mpr ⟨i, hx⟩
        exact hu.trans hδL
      exact meets_insWalk_of_line_trace_deformation hS hT hφ hW.1.2 W hψU hD hbdD hmD
        hh hL hψL (fun x hx => (hZorig hx).1) hZΓ hZR hc hcD ins

end GraphMinor.GM12
