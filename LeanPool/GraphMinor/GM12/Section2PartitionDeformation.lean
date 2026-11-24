/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2SingleVisitDeformation
public import LeanPool.GraphMinor.GM12.Section2CyclicDeformation
public import LeanPool.GraphMinor.GM12.Section2CyclicHitParameters
import LeanPool.GraphMinor.GM12.Section2TracePartitionCarrier
import LeanPool.GraphMinor.GM12.Section2PeriodicHits
import LeanPool.GraphMinor.GM11.RadialRegions

/-!
# Assembling the actual trace deformation

For XII (2.1), Case 1, page 244, apply the single-visit deformation
to every real interval of the trace subdivision. The endpoints match
cyclically. Glue the homotopies, and assemble the two-edge walks while
retaining their point sets. The resulting closed curve has exactly
the point set of the resulting trace walk. Each piece is injective
on its half-open interval or is a backtracking line at one vertex.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM07

/-- The finite assembly of the deformation used in XII (2.1), Case 1.
It retains the real trace steps, exact point set, endpoint and region
data, and the simplicity or backtracking alternative of every piece. -/
theorem exists_partition_trace_deformation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ : C(Circle, S)} {Z : Set S} (hφZ : range φ ⊆ Z)
    {n : ℕ} (hn : 0 < n) (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    (hperiod : t (Fin.last n) = t 0 + 1) (hΓ : ∀ i, periodicCurve φ (t i) ∈ Γ.V)
    (r : Fin n → Set S) (hr : ∀ i, r i ∈ Γ.R) (hrZ : ∀ i, r i ⊆ Z)
    (hfr : ∀ i s, s ∈ Ioo (t i.castSucc) (t i.succ) → periodicCurve φ s ∈ r i) :
    ∃ (δ : Fin n → C(unitInterval, S))
      (hmatch : ∀ i, δ i 1 = δ (finNext hn i) 0)
      (W : GraphWalk K.toGraph (periodicCurve φ (t 0)) (periodicCurve φ (t 0))),
      TraceSteps Γ K (periodicCurve φ) (t 0) (t 0 + 1) W ∧ W.length = 2 * n ∧
      range (concatLoop hn δ hmatch) = (walkDrawing K W).U ∧
      ClosedCurvesHomotopicIn Z φ (concatLoop hn δ hmatch) ∧
      (∀ i, δ i 0 = periodicCurve φ (t i.castSucc)) ∧
      (∀ i, δ i 1 = periodicCurve φ (t i.succ)) ∧
      (∀ i s, 0 < s.val → s.val < 1 → δ i s ∈ r i) ∧
      ∀ i, InjOn (δ i) (Ico (0 : unitInterval) 1) ∨
        (periodicCurve φ (t i.castSucc) = periodicCurve φ (t i.succ) ∧
          ∃ L : Set S, IsLine L ∧ range (δ i) = L ∧ L ⊆ r i ∪ {periodicCurve φ (t i.castSucc)})
            := by
  let γ : Fin n → C(unitInterval, S) := fun i =>
    ⟨fun s => periodicCurve φ (t i.castSucc + s.val * (t i.succ - t i.castSucc)),
      (periodicCurve_continuous φ).comp (by fun_prop)⟩
  have hγ : ∀ i s, γ i s = periodicCurve φ (t i.castSucc + s.val * (t i.succ - t i.castSucc))
    := fun _ _ => rfl
  have hγZ : ∀ i, range (γ i) ⊆ Z := by
    rintro i x ⟨s, rfl⟩
    exact hφZ (mem_range_self _)
  have hvisit : ∀ i : Fin n,
      ∃ (δ : C(unitInterval, S))
        (W : GraphWalk K.toGraph (periodicCurve φ (t i.castSucc)) (periodicCurve φ (t i.succ))),
        TraceSteps Γ K (periodicCurve φ) (t i.castSucc) (t i.succ) W ∧
        W.length = 2 ∧ range δ = (walkDrawing K W).U ∧ CurvesHomotopicIn Z (γ i) δ ∧
        δ 0 = periodicCurve φ (t i.castSucc) ∧ δ 1 = periodicCurve φ (t i.succ) ∧
        (∀ s, 0 < s.val → s.val < 1 → δ s ∈ r i) ∧
        (InjOn δ (Ico (0 : unitInterval) 1) ∨
          (periodicCurve φ (t i.castSucc) = periodicCurve φ (t i.succ) ∧
            ∃ L : Set S, IsLine L ∧ range δ = L ∧ L ⊆ r i ∪ {periodicCurve φ (t i.castSucc)})) := by
    intro i
    exact exists_single_visit_deformation hS hK hE (periodicCurve_continuous φ)
      (ht i.castSucc_lt_succ) (hΓ _) (hΓ _) (hr i) (hrZ i) (hfr i) (γ i) (hγ i) (hγZ i)
  choose δ Wi htrace hlen hcarrier hrel hδ0 hδ1 hδr halt using hvisit
  have hmatch : ∀ i, δ i 1 = δ (finNext hn i) 0 := by
    intro i
    exact (hδ1 i).trans ((periodic_value_succ_eq_next (periodicCurve_periodic φ) hn t hperiod
      i).trans
      (hδ0 (finNext hn i)).symm)
  have hγmatch : ∀ i, γ i 1 = γ (finNext hn i) 0 := by
    intro i
    simp only [hγ, Icc.coe_one, one_mul, add_sub_cancel, Icc.coe_zero, zero_mul, add_zero]
    exact periodic_value_succ_eq_next (periodicCurve_periodic φ) hn t hperiod i
  have hh := closedCurve_homotopic_to_deformed_real_pieces hφZ hn
    (fun i => t i.castSucc) (fun i => t i.succ)
    (cyclic_step_of_period_endpoints hn t hperiod) γ δ hγ hγmatch hmatch hrel
  have hassembly := exists_traceSteps_of_partition_with_carrier t hΓ
    (fun i => radial_V (show PreRad (.drawing Γ) K from ⟨hK.1, hK.2.1⟩) (hΓ i))
    (fun i => range (δ i)) (fun i => ⟨Wi i, htrace i, hlen i, (hcarrier i).symm⟩)
  rw [hperiod, periodicCurve_periodic φ (t 0)] at hassembly
  obtain ⟨W, hW, hWlen, hWU⟩ := hassembly
  have hstart : periodicCurve φ (t 0) ∈ ⋃ i, range (δ i) := by
    let i : Fin n := ⟨0, hn⟩
    exact mem_iUnion.mpr ⟨i, 0, hδ0 i⟩
  have hWU' : (walkDrawing K W).U = ⋃ i, range (δ i) :=
    hWU.trans (union_eq_right.mpr (singleton_subset_iff.mpr hstart))
  exact ⟨δ, hmatch, W, hW, hWlen, (range_concatLoop hn δ hmatch).trans hWU'.symm,
    hh, hδ0, hδ1, hδr, halt⟩

end GraphMinor.GM12
