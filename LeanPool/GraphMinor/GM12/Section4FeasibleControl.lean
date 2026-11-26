/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4EndPartition
public import LeanPool.GraphMinor.GM12.Cited
import LeanPool.GraphMinor.GM12.Section4PartitionControl
import LeanPool.GraphMinor.GM12.Section3Theorem
import LeanPool.GraphMinor.GM12.Section3DiscRegion

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Applying the connection theorem in XII (4.3)

After claim (7), XII (4.3), page 251, applies (3.2) to the
free-edge discs and their oriented end classes. The boundary has
at most twice as many vertices as there are selected edges. Each
region meeting a disc is its chosen incident region. Thus the
connection theorem gives the required branch drawings, and the
end-partition assembly proves control.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM11 GM14

universe u

/-- The application of (3.2) and subsequent branch assembly in
XII (4.3), page 251. The topological feasibility condition is an
input here, exactly as it is for (3.2). -/
theorem exists_threshold_for_control_from_feasible_discs
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {p t : ℕ}
    (L : Graph (Fin p) (Fin t)) (κ : Fin t × Bool → Fin p)
    (hloopless : ∀ e v, ¬ L.IsLink e v v)
    (hassign : ∀ e u v, L.IsLink e u v →
      (κ (e, true) = u ∧ κ (e, false) = v) ∨
        (κ (e, true) = v ∧ κ (e, false) = u))
    (htwo : ∀ v ∈ L.vertexSet, ∃ i j, i ≠ j ∧
      ∃ c d : Bool, κ (i, c) = v ∧ κ (j, d) = v) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 * p ≤ k ∧
      ∀ (Γ : Drawing S) (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ) (f : Fin t → Set S) (a b : Fin t → S)
        (Δ r : Fin t → Set S),
      HasTangleMetric Γ θ T d → k ≤ θ →
      (∀ i, Γ.toGraph.IsLink (f i) (a i) (b i) ∧ a i ≠ b i) →
      (∀ i, IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i) ∧
        Γ.V ∩ discBd (Δ i) = {a i, b i}) →
      (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) →
      (∀ i j, i ≠ j → k + 4 ≤ d (f i) (f j)) →
      (∀ i, r i ∈ Γ.R ∧ (r i ∩ Δ i).Nonempty) →
      (∀ i j, i ≠ j → k ≤ d (r i) (r j)) →
      (∀ i, IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ i))) →
      IsTopologicallyFeasible Δ
        (edgeEndClass (fun q : Fin t × Bool => if q.2 then a q.1 else b q.1) κ) →
      ControlsMinor Γ.toHypergraph θ T L := by
  obtain ⟨η, hη, h32⟩ := theorem_3_2_proof hS t (2 * t)
  let k := max η (2 * p)
  refine ⟨k, hη.trans (le_max_left _ _), le_max_right _ _, ?_⟩
  intro Γ θ T d f a b Δ r hm hkθ hl hΔ hdisj hsep hr hreg hfree hfeas
  let ends : Fin t × Bool → S := fun q => if q.2 then a q.1 else b q.1
  have hbd : ∀ i, Γ.V ∩ discBd (Δ i) = {a i, b i} := fun i => (hΔ i).2.2
  have hZ := discBoundaryVertices_eq_range_ends Δ a b hbd
  have haD : ∀ i, a i ∈ Δ i := by
    intro i
    exact Surface.discBd_subset (Δ i) (((hbd i).symm.subset (by simp)).2)
  have hbD : ∀ i, b i ∈ Δ i := by
    intro i
    exact Surface.discBd_subset (Δ i) (((hbd i).symm.subset (by simp)).2)
  have hinj : Function.Injective ends := edge_ends_injective_of_disjoint_discs a b Δ
    (fun i => (hl i).2) haD hbD hdisj
  have hcover : (⋃ v, edgeEndClass ends κ v) = discBoundaryVertices Γ Δ :=
    (iUnion_edgeEndClass ends κ).trans hZ.symm
  have hreg' : ∀ i j, i ≠ j → ∀ ri ∈ Γ.R, (ri ∩ Δ i).Nonempty →
      ∀ rj ∈ Γ.R, (rj ∩ Δ j).Nonempty → η ≤ d ri rj := by
    intro i j hij ri hri hriD rj hrj hrjD
    obtain ⟨q, _, _, _, huniq⟩ := exists_unique_region_meeting_disc hS (hΔ i).1 (hΔ i).2.1
    have hri' : ri = r i := (huniq ri hri hriD).trans (huniq (r i) (hr i).1 (hr i).2).symm
    obtain ⟨q', _, _, _, huniq'⟩ := exists_unique_region_meeting_disc hS (hΔ j).1 (hΔ j).2.1
    have hrj' : rj = r j := (huniq' rj hrj hrjD).trans (huniq' (r j) (hr j).1 (hr j).2).symm
    rw [hri', hrj']
    exact (le_max_left η (2 * p)).trans (hreg i j hij)
  obtain ⟨H, hHs, hconn, hHdisj, hclasses⟩ := h32 Δ Γ θ T d p (edgeEndClass ends κ)
    (fun i => ⟨(hΔ i).1, (hΔ i).2.1⟩) hdisj (discBoundaryVertices_ncard_le_twice Δ a b hbd)
    hcover (fun i j hij => disjoint_edgeEndClass ends κ hinj hij) hfeas
    ((le_max_left _ _).trans hkθ) hm hreg' hfree
  apply controlsMinor_of_end_partition hS hm L f a b κ (fun i => (hl i).1) hsep hloopless
    hassign htwo (Nat.le_trans (by omega : p ≤ k) hkθ) (le_max_right _ _) H hHs hconn hHdisj
  intro v
  rw [← hZ]
  exact hclasses v

end GraphMinor.GM12
