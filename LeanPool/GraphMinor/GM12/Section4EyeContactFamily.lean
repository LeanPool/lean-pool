/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM12.Section4RegionContactFamily
import LeanPool.GraphMinor.GM12.Section4EyeRegionDistance
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Walks

/-!
# Contact discs at distant eye regions

For XII (4.5), page 253, distant regions have disjoint vertex
contact sets. The regions themselves are disjoint components
of the complement of the drawing. Applying the simultaneous
contact construction gives the discs required by claim (1),
retaining each given circle parametrization at every mark.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM14

/-- The target disc family for XII (4.5), page 253, obtained
from the two-cell drawing and region-distance assumptions. -/
theorem exists_eye_contact_family
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} (hcell : Γ.IsTwoCell)
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d) (hE : Γ.E.Nonempty)
    {ι : Type*} [Nontrivial ι] (r N : ι → Set S)
    (hr : ∀ i, r i ∈ Γ.R) (hri : Function.Injective r)
    (hfar : ∀ i j, i ≠ j → 3 ≤ d (r i) (r j))
    (hC : ∀ i, IsOArc (frontier (r i)))
    (hNV : ∀ i, N i ⊆ Γ.V) (hNb : ∀ i, N i ⊆ frontier (r i))
    (hfin : ∀ i, (N i).Finite) (hne : ∀ i, (N i).Nonempty)
    (φ : ∀ i, Circle ≃ₜ frontier (r i)) :
    ∃ (D : ι → Set S) (q : ι → Circle → S),
      (∀ i, IsClosedDisc (D i)) ∧
      Pairwise (fun i j => Disjoint (D i) (D j)) ∧
      (∀ i, D i ⊆ closure (r i) ∧ D i ∩ Γ.U = N i ∧ N i ⊆ discBd (D i)) ∧
      (∀ i, Continuous (q i) ∧ Function.Injective (q i) ∧ range (q i) = discBd (D i)) ∧
      ∀ i w, (φ i w).val ∈ N i → q i w = (φ i w).val := by
  let : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  have hrr : Pairwise (fun i j => Disjoint (r i) (r j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    exact hij (hri (GM11.region_eq_of_mem (hr i) (hr j) hxi hxj))
  have hrZ : ∀ i, Disjoint (r i) Γ.U := fun i =>
    disjoint_left.mpr (fun x hx hxu => GM11.region_subset (hr i) hx hxu)
  have hbdZ : ∀ i, frontier (r i) ⊆ Γ.U := by
    intro i x hx
    rcases GM11.closure_region_subset (hr i) hx.1 with hxr | hxU
    · exact False.elim (hx.2 ((hcell.2 _ (hr i)).1.interior_eq.symm ▸ hxr))
    · exact hxU
  have hNN : Pairwise (fun i j => Disjoint (N i) (N j)) := by
    intro i j hij
    have hi : N i ⊆ Γ.V ∩ closure (r i) :=
      fun x hx => ⟨hNV i hx, frontier_subset_closure (hNb i hx)⟩
    have hj : N j ⊆ Γ.V ∩ closure (r j) :=
      fun x hx => ⟨hNV j hx, frontier_subset_closure (hNb j hx)⟩
    exact (vertex_closures_disjoint_of_regions_distant hS hm hE (hr i) (hr j)
      (hfar i j hij)).mono hi hj
  exact exists_region_contact_family hS r N Γ.U (fun i => hcell.2 _ (hr i)) hrr
    hC hrZ hbdZ (fun i => (hNV i).trans Γ.V_subset_U) hNb hfin hne hNN φ

end GraphMinor.GM12
