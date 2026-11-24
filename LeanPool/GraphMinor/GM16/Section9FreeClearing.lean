/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM16.Section9Compressions
import LeanPool.GraphMinor.GM16.Section9ZonePreservation
import LeanPool.GraphMinor.GM14.Section3

/-!
# Free sets under a battlefield clearing

Claim (3) of XVI (8.1) uses XV (4.7). The atom condition in that
theorem follows from the zone bound: atoms farther than the radius
survive the clearing. This file supplies that application with all
its side conditions.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The application of XV (4.7) in XVI (8.1), Claim (3), page 72.
A free set sufficiently far from the centre remains free after clearing. -/
theorem freeSet_after_clearing
    (hS : IsClosedSurface S) {H : Drawing S} {θ γ : ℕ} {z Λ X : Set S}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} (hMet : HasTangleMetric H θ T d)
    (hγ : 2 ≤ γ) (hθ : 4 * γ + 2 < θ)
    (hZone : IsLambdaZoneAround H d γ z Λ)
    (hClear : IsClearedTangle H T d θ γ Λ T' d')
    (hFree : IsFreeSet H.toHypergraph T θ X)
    (hFar : ∀ v ∈ X, 2 * X.ncard + 5 * γ + 2 < d z {v}) :
    IsFreeSet (clearedSubdrawing H Λ).toHypergraph T' (θ - (4 * γ + 2)) X := by
  exact GraphMinor.GM15.theorem_4_7_proof.{w} H (clearedSubdrawing H Λ) θ γ T T' d d' z X hS
    inferInstance
    hMet hZone.z_mem hγ hFree hFar (clearedSubdrawing_isTwoCell hMet.1.1 hZone)
    (fun a ha hfar => far_atom_mem_cleared hZone ha hfar)
    (compression_of_clearing hMet hθ hClear)

end GraphMinor.GM16
