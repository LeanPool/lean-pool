/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.GM12.Section3Punctured
import LeanPool.GraphMinor.GM12.Section3Theorem
import LeanPool.GraphMinor.GM11.Regions
import Mathlib.Data.Fintype.EquivFin

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Applying the connection theorem to eye discs

XII (4.5), page 253, applies (3.2) to the endpoint classes.
The classes can have any finite label type. Enumerate those
labels to apply (3.2), and then restore them. A disc lying in
a region closure can meet no other region, which supplies the
region-separation condition of that theorem.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM14

universe u

/-- The application of XII (3.2) to discs inside prescribed
region closures, with arbitrary finite labels for the classes. -/
theorem exists_threshold_for_disc_connections
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) :
    ∃ η : ℕ, 1 ≤ η ∧
      ∀ {W : Type*} [Fintype W] (Γ : Drawing S) (θ : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ) (D r : Fin t → Set S) (Zs : W → Set S),
      (∀ i, IsClosedDisc (D i) ∧ Γ.U ∩ D i = Γ.V ∩ discBd (D i)) →
      Pairwise (fun i j => Disjoint (D i) (D j)) →
      (discBoundaryVertices Γ D).ncard ≤ z →
      (⋃ w, Zs w) = discBoundaryVertices Γ D →
      Pairwise (fun v w => Disjoint (Zs v) (Zs w)) →
      (∃ B : W → Set S, (∀ w, IsClosedDisc (B w)) ∧
        Pairwise (fun v w => Disjoint (B v) (B w)) ∧
        ∀ w, B w ∩ ⋃ i, D i = Zs w) →
      η ≤ θ → HasTangleMetric Γ θ T d →
      (∀ i, r i ∈ Γ.R ∧ D i ⊆ closure (r i)) →
      (∀ i j, i ≠ j → η ≤ d (r i) (r j)) →
      (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (D i))) →
      ∃ H : W → Drawing S, (∀ w, (H w).IsSubdrawing Γ) ∧
        (∀ w, IsConnectedDrawing (H w)) ∧
        Pairwise (fun v w => Disjoint (H v).V (H w).V) ∧
        ∀ w, (H w).V ∩ discBoundaryVertices Γ D = Zs w := by
  obtain ⟨η, hη, hmain⟩ := theorem_3_2_proof hS t z
  refine ⟨η, hη, ?_⟩
  intro W _ Γ θ T d D r Zs hD hDD hcount hcover hZZ hfeas hθ hm hr hfar hfree
  classical
  let : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let ν : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  have hcover' : (⋃ i, Zs (ν i)) = discBoundaryVertices Γ D := by
    rw [← hcover]
    ext x
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨ν i, hi⟩,
      fun ⟨w, hw⟩ => ⟨ν.symm w, by simpa only [ν.apply_symm_apply] using hw⟩⟩
  obtain ⟨B, hB, hBB, hBZ⟩ := hfeas
  have hfeas' : IsTopologicallyFeasible D (fun i => Zs (ν i)) :=
    ⟨fun i => B (ν i), fun i => hB (ν i),
      fun i j hij => hBB (fun h => hij (ν.injective h)), fun i => hBZ (ν i)⟩
  have hreg : ∀ i j, i ≠ j → ∀ ri ∈ Γ.R, (ri ∩ D i).Nonempty →
      ∀ rj ∈ Γ.R, (rj ∩ D j).Nonempty → η ≤ d ri rj := by
    intro i j hij ri hri hriD rj hrj hrjD
    have heq : ∀ k (s : Set S), s ∈ Γ.R → (s ∩ D k).Nonempty → s = r k := by
      intro k s hs hmeet
      obtain ⟨x, hxs, hxD⟩ := hmeet
      rcases GM11.closure_region_subset (hr k).1 ((hr k).2 hxD) with hxr | hxU
      · exact GM11.region_eq_of_mem hs (hr k).1 hxs hxr
      · exact False.elim (GM11.region_subset hs hxs hxU)
    rw [heq i ri hri hriD, heq j rj hrj hrjD]
    exact hfar i j hij
  obtain ⟨H, hHs, hHc, hHH, hHZ⟩ := hmain D Γ θ T d (Fintype.card W)
    (fun i => Zs (ν i)) hD hDD hcount hcover'
    (fun i j hij => hZZ (fun h => hij (ν.injective h))) hfeas' hθ hm hreg hfree
  refine ⟨fun w => H (ν.symm w), fun w => hHs _, fun w => hHc _,
    fun v w hvw => hHH _ _ (fun h => hvw (ν.symm.injective h)), ?_⟩
  intro w
  simpa only [ν.apply_symm_apply] using hHZ (ν.symm w)

end GraphMinor.GM12
