/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SeparatedMetric
public import LeanPool.GraphMinor.GM12.Section3TwoDiscs
public import LeanPool.GraphMinor.GM12.Section3OneDisc
import LeanPool.GraphMinor.GM12.Section3EmptyClasses
import LeanPool.GraphMinor.GM12.Section3DiscRegion
import Mathlib.Tactic.IntervalCases

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XII, (3.2)

For a nonspherical surface or at least three prescribed discs, the
five geometric checks give (3.1). For two discs, choose a separated
intermediate region and add an empty-boundary disc away from the
feasibility forest. For one disc on the sphere, freeness gives the
normal-chord inequality and VI (3.6) gives the connections. With no
discs, the prescribed vertex set is empty. These are the cases of
the proof on pages 246--248.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM14

universe u

/-- Graph Minors XII, (3.2), pages 245--248. A uniform separation
threshold for the prescribed regions and free boundary vertices
ensures disjoint connected subdrawings realizing every topologically
feasible boundary partition. -/
theorem theorem_3_2_proof
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) :
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
  by_cases hcase : ¬ IsSphere S ∨ 3 ≤ t
  · exact theorem_3_2_separated_metric hS t z hcase
  · have hs : IsSphere S := by
      by_contra hn
      exact hcase (Or.inl hn)
    have ht : t ≤ 2 := by
      by_contra hn
      exact hcase (Or.inr (by omega))
    interval_cases t
    · refine ⟨1, le_rfl, ?_⟩
      intro Δ Γ θ T d p Zs _ _ _ hcover _ _ _ _ _ _
      have hZ : discBoundaryVertices Γ Δ = ∅ := by simp [discBoundaryVertices]
      rw [hZ] at hcover ⊢
      exact hasConnectingSubdrawings_of_empty_union Γ Zs hcover
    · refine ⟨max 1 z, le_max_left _ _, ?_⟩
      intro Δ Γ θ T d p Zs hΔ _ _ hcover hdisZ hfeas _ hm _ hfree
      exact theorem_3_2_one_disc hS hs Γ hm.1.2.1 Δ (fun i => (hΔ i).1)
        (fun i => (hΔ i).2) Zs hcover hdisZ hfeas (hfree 0)
    · obtain ⟨η, hηpos, htwo⟩ := theorem_3_2_two_discs hS z
      refine ⟨η, hηpos, ?_⟩
      intro Δ Γ θ T d p Zs hΔ hdis hcount hcover hdisZ hfeas horder hm hsep hfree
      have hreg : ∀ i, ∃ r ∈ Γ.R, (r ∩ Δ i).Nonempty := by
        intro i
        obtain ⟨r, hr, hInt, _, _⟩ := exists_unique_region_meeting_disc hS (hΔ i).1 (hΔ i).2
        obtain ⟨x, hx⟩ := (hΔ i).1.nonempty_discInt
        exact ⟨r, hr, x, hInt hx, hx.1⟩
      choose r hr hrΔ using hreg
      exact htwo Γ θ T d Δ r p Zs hm horder (fun i => (hΔ i).1) hdis
        (fun i => (hΔ i).2) hr hrΔ
        (fun i j hij => hsep i j hij (r i) (hr i) (hrΔ i) (r j) (hr j) (hrΔ j))
        hfree hcount hcover hdisZ hfeas

end GraphMinor.GM12
