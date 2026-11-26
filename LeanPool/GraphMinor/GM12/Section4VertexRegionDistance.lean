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
# Distance between regions at distant vertices

XII (4.4), page 251, uses the threshold from (3.2) plus two.
Each selected vertex is at distance at most one from its incident
region. Two applications of the triangle inequality from XI (9.1)
therefore leave the required distance between the regions.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM14

/-- The two-unit distance adjustment in XII (4.4), page 251. -/
theorem regions_distant_of_incident_vertices_distant
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d) (hE : Γ.E.Nonempty)
    {u v : S} (hu : u ∈ Γ.V) (hv : v ∈ Γ.V)
    {r s : Set S} (hr : r ∈ Γ.R) (hs : s ∈ Γ.R)
    (hur : u ∈ closure r) (hvs : v ∈ closure s)
    {k : ℕ} (hfar : k + 2 ≤ d {u} {v}) : k ≤ d r s := by
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have hsym := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have hvr := h91.2.2.2.2.2.1 hE u hu r hr hur
  have hvs' := h91.2.2.2.2.2.1 hE v hv s hs hvs
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hrA : r ∈ Γ.A := Or.inr hr
  have hsA : s ∈ Γ.A := Or.inr hs
  have ht₁ := htri {u} huA r hrA {v} hvA
  have ht₂ := htri r hrA s hsA {v} hvA
  rw [hsym s hsA {v} hvA] at ht₂
  omega

end GraphMinor.GM12
