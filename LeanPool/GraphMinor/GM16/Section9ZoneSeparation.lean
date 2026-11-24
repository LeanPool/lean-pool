/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
import LeanPool.GraphMinor.GM14.Section7a
import LeanPool.GraphMinor.GM16.DrawingConnected

/-!
# A separation side contained in a zone is small

The planar separator argument in XVI (8.1), Claim (10), uses the
inside of the battlefield. A low-order separation side whose edges
all lie in that zone belongs to the tangle. Otherwise XIV (7.3)
would put an edge on that side farther from the centre than the
zone's radius.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- Orient a small separation towards the complement of a zone.
This is the tangle orientation used in the radial form of the planar
Menger argument in XVI (8.1), Claim (10). -/
theorem separation_mem_of_edges_in_zone (hS : IsClosedSurface S)
    {H : Drawing S} {θ γ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {y : S} {Λ : Set S}
    {A B : Hypergraph S (Set S)} (hMet : HasTangleMetric H θ T d) (hθ : 2 ≤ θ)
    (hy : y ∈ H.V) (hZone : IsLambdaZoneAround H d γ {y} Λ)
    (hSep : H.toHypergraph.IsSeparation A B)
    (hOrder : Hypergraph.separationOrder A B + γ < θ)
    (hEdges : ∀ e ∈ A.edgeSet, e ⊆ closure Λ) : (A, B) ∈ T := by
  by_contra hnot
  have hBA := (hMet.1.2.1.axiom1 hSep (by omega)).resolve_left hnot
  have hAne : A.edgeSet ≠ {{y}} := by
    intro heq
    have heA : ({y} : Set S) ∈ A.edgeSet := heq ▸ mem_singleton _
    have heH : ({y} : Set S) ∈ H.E := hSep.left_le.2 heA
    exact (heH.2.1 (mem_singleton y)).2 hy
  obtain ⟨e, heA, hFar⟩ := GraphMinor.GM14.theorem_7_3_proof H θ T d B A {y}
    hS inferInstance (edges_nonempty_of_tangle hS hMet.1 hθ) hMet hZone.z_mem hBA hAne
  have heH : e ∈ H.E := hSep.left_le.2 heA
  have hNear := hZone.dist_le e (Or.inl (Or.inr heH)) (hEdges e heA)
  rw [separationOrder_comm] at hFar
  omega

end GraphMinor.GM16
