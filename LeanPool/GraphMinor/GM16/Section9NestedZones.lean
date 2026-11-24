/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
import LeanPool.GraphMinor.GM16.Section6ZoneWalks

import LeanPool.GraphMinor.GM14.Section9a

/-!
# The nested zones in XVI (8.1)

After Claim (9), Section 9 chooses zones at successive radii around
one centre. A gap of three between the indices puts the closure of
the smaller zone inside the larger one. The same atom argument puts
the annuli inside the battlefield disc.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The zone choices preceding Claim (10) in XVI (8.1), page 73. -/
theorem section9_exists_nested_zones
    (hS : IsClosedSurface S) {H : Drawing S} {θ β : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {y : S} (hy : y ∈ H.V)
    (hMet : HasTangleMetric H θ T d) (hθ : β < θ) :
    ∃ M : ℕ → Set S, ∀ i, 3 ≤ i → i ≤ β - 3 →
      IsLambdaZoneAround H d (i + 2) {y} (M i) ∧
      ∀ a ∈ H.A, d {y} a < i → a ⊆ M i := by
  classical
  have hex : ∀ i : ℕ, ∃ A : Set S, (3 ≤ i ∧ i ≤ β - 3) →
      IsLambdaZoneAround H d (i + 2) {y} A ∧ ∀ a ∈ H.A, d {y} a < i → a ⊆ A := by
    intro i
    by_cases hi : 3 ≤ i ∧ i ≤ β - 3
    · obtain ⟨A, hA⟩ := GraphMinor.GM14.theorem_9_2_proof.{w} H θ i T d {y} hS inferInstance hMet
        (Or.inl (Or.inl ⟨y, hy, rfl⟩)) (by omega) (by omega)
      exact ⟨A, fun _ => hA⟩
    · exact ⟨∅, fun h => False.elim (hi h)⟩
  choose M hM using hex
  exact ⟨M, fun i hi hβ => hM i ⟨hi, hβ⟩⟩

/-- Graph Minors XVI, proof of (8.1), Claim (12), page 74.
The atom containing a point of the smaller closure has distance at
most `i + 2`, so it belongs to the larger zone when `i + 3 ≤ j`. -/
theorem section9_nested_closures {H : Drawing S} {d : Set S → Set S → ℕ}
    {y : S} {M : ℕ → Set S} {i j : ℕ}
    (hi : IsLambdaZoneAround H d (i + 2) {y} (M i))
    (hj : ∀ a ∈ H.A, d {y} a < j → a ⊆ M j) (hgap : i + 3 ≤ j) :
    closure (M i) ⊆ M j :=
  zone_closure_subset_of_atom_neighborhood hi (fun a ha hd => hj a ha (by omega))

/-- The battlefield containment in XVI (8.1), Claim (13), page 74.
The entire outer zone closure lies in the battlefield disc when its
radius is less than the battlefield size. -/
theorem section9_zone_inside_battlefield {H : Drawing S}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ β i : ℕ} {y : S} {Λ M X : Set S} {C : Drawing S}
    (hBattle : IsBattlefield H T d θ β {y} Λ C X)
    (hM : IsLambdaZoneAround H d (i + 2) {y} M) (hbound : i + 3 ≤ β) :
    closure M ⊆ Λ := by
  obtain ⟨Δ, _, hΔΛ, _, hSmall⟩ := hBattle.openDisc_includes
  exact (zone_closure_subset_of_atom_neighborhood hM
    (fun a ha hd => hSmall a ha (by omega))).trans hΔΛ

end GraphMinor.GM16
