/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3OneDiscComplement
public import LeanPool.GraphMinor.GM12.Section3SphereChordTransfer
import LeanPool.GraphMinor.GM12.Section3DiscVIEmpty
import LeanPool.GraphMinor.GM12.Section3DiscCrossFree
import LeanPool.GraphMinor.GM12.Section3BoundaryEquality
import LeanPool.GraphMinor.GM12.Section3AmbientTransfer
import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# The one-disc sphere case of XII (3.2)

Read the drawing in the complementary closed disc. Topological
feasibility makes its boundary partition cross-free. The tangle
and freeness give the normal-chord inequality there, as proved on
the sphere and preserved by inclusion. The VI (3.6) reduction now
gives the connected subdrawings. Include them back into the sphere.
This completes the last case on pages 247--248.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM06

/-- Graph Minors XII (3.2), pages 247--248, for one prescribed disc
on the sphere. Freeness already bounds the prescribed vertex count
by the tangle order, as used in the paper's argument. -/
theorem theorem_3_2_one_disc
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hs : IsSphere S) (Γ : Drawing S) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T) (Δ : Fin 1 → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i)) (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
    {p : ℕ} (Zs : Fin p → Set S) (hcover : (⋃ j, Zs j) = discBoundaryVertices Γ Δ)
    (hdisZ : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) (hfeasible : IsTopologicallyFeasible Δ Zs)
    (hfree : GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ 0))) :
    HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  have hdis : Pairwise (fun i j => Disjoint (Δ i) (Δ j)) := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))
  let C := discComplement Δ
  let hUC := drawing_support_subset_discComplement hS Γ Δ hΔ hdis havoid
  let G := drawingInSubspace Γ C hUC
  have hDisc : GM06.IsClosedDiscSpace C := isClosedDiscSpace_discComplement_one hS hs Δ hΔ
  have hGproper : G.IsProper := drawingInDiscComplement_isProper hS Γ Δ hΔ hdis havoid
  have hZbd : ∀ j, Zs j ⊆ ⋃ i, discBd (Δ i) := by
    intro j x hx
    have hxZ := hcover.subset (mem_iUnion.mpr ⟨j, hx⟩)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxZ
    exact mem_iUnion.mpr ⟨i, hi.2⟩
  have hZC : ∀ j, Zs j ⊆ C := by
    intro j x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hZbd j hx)
    exact disc_boundary_subset_discComplement hS Δ hΔ hdis i hi
  have hGB : G.V ∩ bd C = (Subtype.val : C → S) ⁻¹' discBoundaryVertices Γ Δ := by
    dsimp only [G, C]
    rw [drawingInSubspace_V, discComplement_boundary_eq hS Δ hΔ]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_iUnion, discBoundaryVertices]
    constructor
    · rintro ⟨hv, i, hi⟩
      exact ⟨i, hv, hi⟩
    · rintro ⟨i, hv, hi⟩
      exact ⟨hv, i, hi⟩
  have hcoverC : (⋃ j, (Subtype.val : C → S) ⁻¹' Zs j) = G.V ∩ bd C := by
    rw [hGB, ← hcover]
    ext x
    simp only [mem_iUnion, mem_preimage]
  have hCF := isCrossFree_of_topological_feasible_in_discComplement hS Δ hΔ hdis Zs
    hZbd hfeasible hDisc
  have hunionBd : (⋃ i, discBd (Δ i)) = discBd (Δ 0) := by
    ext x
    simp only [mem_iUnion, Fin.exists_fin_one]
  have hbdC : bd C = (Subtype.val : C → S) ⁻¹' discBd (Δ 0) := by
    have h := discComplement_boundary_eq hS Δ hΔ
    rw [hunionBd] at h
    exact h
  have hCΔ : C ∩ Δ 0 = discBd (Δ 0) := by
    apply Subset.antisymm (discComplement_inter_disc_subset_boundary hS Δ hΔ 0)
    intro x hx
    exact ⟨disc_boundary_subset_discComplement hS Δ hΔ hdis 0 hx, Surface.discBd_subset _ hx⟩
  have hconnect := connecting_subdrawings_of_disc_chord_bound_allowing_empty G hDisc hGproper
    (fun j => (Subtype.val : C → S) ⁻¹' Zs j) hcoverC
    (fun i j hij => (hdisZ i j hij).preimage Subtype.val) hCF
    (sphere_chord_bound_in_complement hS hs Γ hT (hΔ 0) (havoid 0) hfree C hUC hbdC hCΔ)
  rw [hGB] at hconnect
  exact hasConnectingSubdrawings_from_closed_subspace Γ C isClosed_closure hUC hZC hconnect

end GraphMinor.GM12
