/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM12.Section4EdgeCircuit
import LeanPool.GraphMinor.GM12.Section4CircuitAtomDistance
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.Section7

/-!
# The distance from an edge to an incident region

The local estimate in XII (4.3), claim (5), page 250, is two.
Enclose the edge in a radial circuit with at most two original
vertices. Since original edges miss radial edges and vertices,
the edge lies in the interior of the inside. A region incident
with the edge therefore meets that inside too. The circuit bounds
the distance between the two atoms by two.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM10 GM11 GM14

/-- The local distance bound used in XII (4.3), claim (5), page 250.
Any atom whose closure contains an edge is at distance at most two
from that edge. In particular this applies to either incident region. -/
theorem edge_atom_distance_le_two_of_subset_closure
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    {e x : Set S} (he : e ∈ Γ.E) (hx : x ∈ Γ.A) (hsub : e ⊆ closure x) :
    d e x ≤ 2 := by
  obtain ⟨hT, K, ins, hK, hd, heq⟩ := hm
  have heA : e ∈ Γ.A := Or.inl (Or.inr he)
  rw [heq e heA x hx]
  by_cases hθ : θ ≤ 2
  · exact (tangleMetric_le_order hK.2.1 e x).trans hθ
  have hθ' : 2 < θ := Nat.lt_of_not_ge hθ
  obtain ⟨C, hC, hCs, hCl, hcount, heC⟩ :=
    exists_radial_circuit_around_edge hS hT hθ' hK hd he
  have hdisc := (hd C hC hCs hCl).1
  have hbd : frontier (ins C) = C.U := by
    rw [← subBd_eq_frontier]
    exact (hd C hC hCs hCl).2.1
  obtain ⟨z, hz⟩ := he.1
  have hzD : z ∈ interior (ins C) := by
    rw [← self_sdiff_frontier]
    refine ⟨heC hz, ?_⟩
    intro hfront
    have hzK : z ∈ K.U := hCs.U_subset (hbd ▸ hfront)
    have hzΓ : z ∈ Γ.U := (he.2.1 hz).1
    have hzV : z ∈ Γ.V := by
      have hi : z ∈ (PaintingOrDrawing.drawing Γ).U ∩ K.U := ⟨hzΓ, hzK⟩
      rw [hK.2.1.1] at hi
      exact hi
    exact (he.2.1 hz).2 hzV
  obtain ⟨w, hwD, hwx⟩ := mem_closure_iff.mp (hsub hz) (interior (ins C))
    isOpen_interior hzD
  have hdist := atom_distance_le_circuit_vertex_count hS hK hd hC hCs hCl heA hx
    ⟨z, hz, heC hz⟩ ⟨w, hwx, interior_subset hwD⟩
  exact hdist.trans hcount

/-- XII (4.3), claim (5), page 250: incident regions of edges
at distance at least `k + 4` are at distance at least `k`. -/
theorem incident_regions_distance_ge
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ k : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    {e f r s : Set S} (he : e ∈ Γ.E) (hf : f ∈ Γ.E)
    (hr : r ∈ Γ.R) (hs : s ∈ Γ.R) (her : e ⊆ closure r) (hfs : f ⊆ closure s)
    (hfar : k + 4 ≤ d e f) : k ≤ d r s := by
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have hsym := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have heA : e ∈ Γ.A := Or.inl (Or.inr he)
  have hfA : f ∈ Γ.A := Or.inl (Or.inr hf)
  have hrA : r ∈ Γ.A := Or.inr hr
  have hsA : s ∈ Γ.A := Or.inr hs
  have hlocal₁ := edge_atom_distance_le_two_of_subset_closure hS hm he hrA her
  have hlocal₂ := edge_atom_distance_le_two_of_subset_closure hS hm hf hsA hfs
  have ht₁ := htri e heA r hrA f hfA
  have ht₂ := htri r hrA s hsA f hfA
  rw [hsym s hsA f hfA] at ht₂
  omega

/-- The endpoint estimate in the final paragraph of XII (4.3),
page 251. Ends of edges at distance at least `k + 4` are at
distance at least `k`. -/
theorem distant_edges_endpoints_distance_ge
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ k : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    {e f : Set S} (he : e ∈ Γ.E) (hf : f ∈ Γ.E)
    {u v : S} (hu : u ∈ Γ.V) (hv : v ∈ Γ.V)
    (hue : u ∈ closure e) (hvf : v ∈ closure f)
    (hfar : k + 4 ≤ d e f) : k ≤ d {u} {v} := by
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have hsym := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have heA : e ∈ Γ.A := Or.inl (Or.inr he)
  have hfA : f ∈ Γ.A := Or.inl (Or.inr hf)
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hlocal₁ := h91.2.2.2.2.2.2 u hu e he hue
  have hlocal₂ := h91.2.2.2.2.2.2 v hv f hf hvf
  have ht₁ := htri e heA {u} huA f hfA
  have ht₂ := htri {u} huA {v} hvA f hfA
  rw [hsym e heA {u} huA] at ht₁
  omega

end GraphMinor.GM12
