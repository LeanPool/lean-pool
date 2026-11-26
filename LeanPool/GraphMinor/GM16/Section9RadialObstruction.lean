/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM11.Separate
import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# The short radial circuit contradiction in XVI (8.1)

Claim (10) excludes a short radial circuit enclosing the inner zone.
XIV (7.5) puts its tangle inside in the battlefield disc. Uniqueness
of the inside of a circle within a disc identifies that inside with
the disc enclosing the zone. A radial region touching the circuit is
then too close to the centre to touch the boundary.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

omit [ConnectedSpace S] in
omit [T2Space S] in
/-- A radial circuit meets a region of the original drawing, at an end
of any of its edges on the region side of the radial bipartition. -/
theorem radial_circuit_meets_region {H K D : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hD : D.IsCircuit) (hDs : D.IsSubdrawing K) :
    ∃ r ∈ H.R, (r ∩ D.U).Nonempty := by
  obtain ⟨e, he⟩ := GraphMinor.GM11.IsCircuit.E_nonempty hD
  obtain ⟨v, _, x, hx, hEnds⟩ := hK.2.1.2.2.2.2.1 e (hDs.2 he)
  obtain ⟨r, hr, hxr⟩ := hK.2.1.2.2.2.1 x hx
  have hxcl : x ∈ closure e := by
    have hxPair : x ∈ ({v, x} : Set S) := Or.inr rfl
    exact (hEnds.symm ▸ hxPair).1
  exact ⟨r, hr, x, hxr, D.closure_subset_U he hxcl⟩

/-- The contradiction part of XVI (8.1), Claim (10), page 73.
No radial circuit of length less than `2κ` can bound a disc inside
the battlefield that includes the entire atom-capturing inner zone. -/
theorem section9_no_short_radial_enclosure (hS : IsClosedSurface S)
    {H K D : Drawing S} {θ γ κ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {ins : Drawing S → Set S} {y : S} {Λ M Δ : Set S}
    (hMet : HasTangleMetric H θ T d)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hMetric : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = tangleMetric H K ins θ a b)
    (hy : y ∈ H.V) (hyM : y ∈ M)
    (hZone : IsLambdaZoneAround H d γ {y} Λ)
    (hCapture : ∀ a ∈ H.A, d {y} a < κ → a ⊆ M)
    (hSymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hκ : κ ≤ θ - γ)
    (hD : D.IsCircuit) (hDs : D.IsSubdrawing K) (hLen : D.length < 2 * κ)
    (hDU : D.U ⊆ closure Λ) (hΔ : IsClosedDisc Δ) (hΔsub : Δ ⊆ closure Λ)
    (hΔbd : discBd Δ = D.U) (hMΔ : M ⊆ Δ \ D.U) : False := by
  have hDlen : D.length < 2 * θ := by omega
  obtain ⟨hIns, hInsBd, _⟩ := hd D hD hDs hDlen
  have hInsSub : ins D ⊆ closure Λ := GraphMinor.GM14.theorem_7_5_proof H K D θ γ T d ins {y} Λ
    hS inferInstance hMet hK hd hZone hD hDs hDU (by omega)
  have hInsDiscBd : discBd (ins D) = D.U := by
    rw [← GraphMinor.GM11.IsClosedDisc.frontier_eq_discBd hS hIns, ← subBd_eq_frontier]
    exact hInsBd
  obtain ⟨Δ₀, _, hUnique⟩ := disc_oArc (closure Λ) D.U hZone.isClosedDisc_closure hDU
    (GraphMinor.GM11.IsCircuit.isOArc_U hD)
  have hEq : Δ = ins D :=
    (hUnique Δ hΔsub hΔ hΔbd).trans (hUnique (ins D) hInsSub hIns hInsDiscBd).symm
  have hyIns : y ∈ ins D := hEq ▸ (hMΔ hyM).1
  obtain ⟨r, hr, x, hxr, hxD⟩ := radial_circuit_meets_region hK hD hDs
  have hxIns : x ∈ ins D := by
    have hbd : x ∈ discBd (ins D) := hInsDiscBd.symm ▸ hxD
    exact GraphMinor.Surface.discBd_subset _ hbd
  have hyA : ({y} : Set S) ∈ H.A := Or.inl (Or.inl ⟨y, hy, rfl⟩)
  have hBound := (tangleMetric_le_of_circuit hS hK hd hD hDs hDlen
    (Or.inr hr) hyA ⟨x, hxr, hxIns⟩ ⟨y, mem_singleton y, hyIns⟩).1
  rw [← hMetric r (Or.inr hr) {y} hyA, hSymm r (Or.inr hr) {y} hyA] at hBound
  have hrM : r ⊆ M := hCapture r (Or.inr hr) (by omega)
  exact (hMΔ (hrM hxr)).2 hxD

end GraphMinor.GM16
