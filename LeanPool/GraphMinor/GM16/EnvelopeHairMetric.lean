/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM16.MetricPoints
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Section88

/-!
# Metric bounds at the new hair ends

Moving two centres to their boundary ends costs at most `2γ` in
the old metric. Moving the two ends of a hair costs at most `3γ`.
The final compression costs its total loss once more. These are
exactly the calculations of XVI (7.1), Claims (5) and (6), page 70.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

private theorem envelope_distance_of_endpoint_budgets (hS : IsClosedSurface S) {H K : Drawing S}
    {θ loss leftBudget rightBudget sep θ₂ : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} (hK : K.IsSubdrawing H)
    (hComp : IsLambdaCompression H K θ loss T T' d d')
    {y z p q : S} (hy : y ∈ H.V) (hz : z ∈ H.V) (hp : p ∈ K.V) (hq : q ∈ K.V)
    (hSep : sep ≤ d {y} {z}) (hyp : d {y} {p} ≤ leftBudget)
    (hzq : d {z} {q} ≤ rightBudget)
    (hBudget : θ₂ + leftBudget + rightBudget + loss ≤ sep) : θ₂ ≤ d' {p} {q} := by
  obtain ⟨_, _, _, hSymm, hTri, _⟩ := GM11.gm15_theorem_9_1 H θ T d hS inferInstance hComp.hasMetric
  have hyA : ({y} : Set S) ∈ H.A := Or.inl (Or.inl ⟨y, hy, rfl⟩)
  have hzA : ({z} : Set S) ∈ H.A := Or.inl (Or.inl ⟨z, hz, rfl⟩)
  have hpA : ({p} : Set S) ∈ H.A := Or.inl (Or.inl ⟨p, hK.1 hp, rfl⟩)
  have hqA : ({q} : Set S) ∈ H.A := Or.inl (Or.inl ⟨q, hK.1 hq, rfl⟩)
  have h₁ := hTri {y} hyA {p} hpA {z} hzA
  have h₂ := hTri {p} hpA {q} hqA {z} hzA
  rw [hSymm {q} hqA {z} hzA] at h₂
  have hc := hComp.dist_le p q
  rw [pointDist_of_mem_vertices d (hK.1 hp) (hK.1 hq), pointDist_of_mem_vertices d' hp hq] at hc
  omega

/-- The new boundary ends of two hairs remain separated after
clearing, as in XVI (7.1), Claim (5), page 70. -/
theorem envelope_boundary_distance (hS : IsClosedSurface S) {H K : Drawing S}
    {θ loss γ sep θ₂ : ℕ} {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} (hK : K.IsSubdrawing H)
    (hComp : IsLambdaCompression H K θ loss T T' d d')
    {y z p q : S} (hy : y ∈ H.V) (hz : z ∈ H.V) (hp : p ∈ K.V) (hq : q ∈ K.V)
    (hSep : sep ≤ d {y} {z}) (hyp : d {y} {p} ≤ γ) (hzq : d {z} {q} ≤ γ)
    (hBudget : θ₂ + 2 * γ + loss ≤ sep) : θ₂ ≤ d' {p} {q} := by
  exact envelope_distance_of_endpoint_budgets hS hK hComp hy hz hp hq hSep hyp hzq (by omega)

/-- The path formed by the old hair and its two exit paths has far
new ends, as in XVI (7.1), Claim (6), page 70. -/
theorem envelope_hair_end_distance (hS : IsClosedSurface S) {H K : Drawing S}
    {θ loss γ sep θ₂ : ℕ} {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} (hK : K.IsSubdrawing H)
    (hComp : IsLambdaCompression H K θ loss T T' d d')
    {y r p q : S} (hy : y ∈ H.V) (hr : r ∈ H.V) (hp : p ∈ K.V) (hq : q ∈ K.V)
    (hFar : sep ≤ d {y} {r}) (hyp : d {y} {p} ≤ γ) (hrq : d {r} {q} ≤ 2 * γ)
    (hBudget : θ₂ + 3 * γ + loss ≤ sep) : θ₂ ≤ d' {p} {q} := by
  exact envelope_distance_of_endpoint_budgets hS hK hComp hy hr hp hq hFar hyp hrq (by omega)

end GraphMinor.GM16
