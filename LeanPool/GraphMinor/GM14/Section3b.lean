/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM14.Section3Proved

/-!
# Graph Minors XIV, (3.2): Unconditional Clearing Theorem

This file proves **Graph Minors XIV, (3.2)** (`theorem_3_2`, page 28) unconditionally from
the closed clearing proof `theorem_3_2_of_710`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- Graph Minors XIV, (3.2) (page 28):
"If $\theta \ge 4\lambda + 3$ then there is a unique tangle of order $\theta - 4\lambda - 2$
obtained by clearing $\Lambda$." -/
theorem theorem_3_2_proof
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Λ : Set S}
    (hθ : 4 * lam + 3 ≤ θ)
    (hMetric : HasTangleMetric H θ T d)
    (hZone : IsLambdaZoneAround H d lam z Λ) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ),
      IsClearedTangle H T d θ lam Λ T' d' ∧
      ∀ (T'' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d'' : Set S → Set S → ℕ),
        IsClearedTangle H T d θ lam Λ T'' d'' → T'' = T' :=
  theorem_3_2_of_710 hS hConn hθ hMetric hZone

end GraphMinor.GM14
