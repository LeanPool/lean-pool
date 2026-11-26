/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SeparatedDiscs
import LeanPool.GraphMinor.GM11.Regions

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Separated free discs stated using a tangle metric

Each prescribed disc has an interior point outside the drawing,
since it meets the drawing only on its boundary. Choose the region
containing that point, unpack the radial description of the metric,
and apply the proved nonsphere-or-three-disc case of XII (3.2).
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14

universe u

/-- The first case of XII (3.2), pages 246--247, with the radial
drawing hidden in the hypothesis that `d` is the tangle metric. -/
theorem theorem_3_2_separated_metric
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) (hcase : ¬ IsSphere S ∨ 3 ≤ t) :
    ∃ η : ℕ, 1 ≤ η ∧ ∀ (Δ : Fin t → Set S) (Γ : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (p : ℕ) (Zs : Fin p → Set S),
      (∀ i, IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) →
      Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
      (discBoundaryVertices Γ Δ).ncard ≤ z →
      (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) → IsTopologicallyFeasible Δ Zs →
      η ≤ θ → HasTangleMetric Γ θ T d →
      (∀ i j, i ≠ j → ∀ ri ∈ Γ.R, (ri ∩ Δ i).Nonempty →
        ∀ rj ∈ Γ.R, (rj ∩ Δ j).Nonempty → η ≤ d ri rj) →
      (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ i))) →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  obtain ⟨η, hηpos, hη⟩ := theorem_3_2_of_not_sphere_or_three_le hS t z hcase
  refine ⟨η, hηpos, ?_⟩
  intro Δ Γ θ T d p Zs hΔ hdis hcount hcover hdisZ hfeasible horder hmetric hsep hfree
  have hregion : ∀ i, ∃ r ∈ Γ.R, (r ∩ Δ i).Nonempty := by
    intro i
    obtain ⟨x, hx⟩ := (hΔ i).1.nonempty_discInt
    have hxU : x ∉ Γ.U := by
      intro hxU
      exact hx.2 (((hΔ i).2.subset ⟨hxU, hx.1⟩).2)
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
    exact ⟨r, hr, x, hxr, hx.1⟩
  choose r hr hrΔ using hregion
  obtain ⟨hT, K, ins, hK, hd, heq⟩ := hmetric
  have hsep' : ∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j) := by
    intro i j hij
    rw [← heq (r i) (Or.inr (hr i)) (r j) (Or.inr (hr j))]
    exact hsep i j hij (r i) (hr i) (hrΔ i) (r j) (hr j) (hrΔ j)
  exact hη Γ K θ T ins Δ r p Zs hT.2.1 hT.2.2 hK hd horder
    (fun i => (hΔ i).1) hdis (fun i => (hΔ i).2) hr hrΔ hsep' hfree
    hcount hcover hdisZ hfeasible

end GraphMinor.GM12
