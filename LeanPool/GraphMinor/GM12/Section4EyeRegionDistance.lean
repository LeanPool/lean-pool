/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM11.CitedResults

/-!
# Distances at the eye-region boundary

XII (4.5), page 253, loses at most two units when replacing
regions by incident vertices. The same metric estimate shows
that regions at distance at least three have no common vertex
in their closures. These facts supply disjoint contact sets
and the final branch-size estimate.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM14

/-- The vertex-distance estimate used in XII (4.5), page 253. -/
theorem incident_vertices_distant_of_regions_distant
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d) (hE : Γ.E.Nonempty)
    {u v : S} (hu : u ∈ Γ.V) (hv : v ∈ Γ.V)
    {r s : Set S} (hr : r ∈ Γ.R) (hs : s ∈ Γ.R)
    (hur : u ∈ closure r) (hvs : v ∈ closure s)
    {k : ℕ} (hfar : k + 2 ≤ d r s) : k ≤ d {u} {v} := by
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have hsym := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have hvr := h91.2.2.2.2.2.1 hE u hu r hr hur
  have hvs' := h91.2.2.2.2.2.1 hE v hv s hs hvs
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hrA : r ∈ Γ.A := Or.inr hr
  have hsA : s ∈ Γ.A := Or.inr hs
  have ht₁ := htri r hrA {u} huA s hsA
  have ht₂ := htri {u} huA {v} hvA s hsA
  rw [hsym r hrA {u} huA] at ht₁
  omega

/-- Distant eye regions cannot share a drawing vertex on their
boundaries. This makes their prescribed contact sets disjoint. -/
theorem vertex_closures_disjoint_of_regions_distant
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d) (hE : Γ.E.Nonempty)
    {r s : Set S} (hr : r ∈ Γ.R) (hs : s ∈ Γ.R)
    (hfar : 3 ≤ d r s) : Disjoint (Γ.V ∩ closure r) (Γ.V ∩ closure s) := by
  apply disjoint_left.mpr
  intro u hur hus
  have hd := incident_vertices_distant_of_regions_distant hS hm hE hur.1 hus.1
    hr hs hur.2 hus.2 (k := 1) hfar
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  rw [h91.2.1 {u} (Or.inl (Or.inl ⟨u, hur.1, rfl⟩))] at hd
  exact Nat.not_succ_le_zero 0 hd

end GraphMinor.GM12
