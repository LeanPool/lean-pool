/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section4SpacedFreeEdges
import LeanPool.GraphMinor.GM12.Section4EdgeEmptyDisc
import LeanPool.GraphMinor.GM12.Section4EmptyDiscsDisjoint
import LeanPool.GraphMinor.GM12.Section4EdgeRegionDistance

/-!
# The free-edge discs for XII (4.3)

Choose the mutually distant free edges from claims (1)--(4) and
put an empty disc through each pair of ends. The distance bound
makes these discs disjoint. Their incident regions remain far
apart by claim (5). Their boundary vertex sets are free by claim
(6), since they are exactly the ends of the chosen free edges.
This supplies the geometric and metric input to XII (3.2).
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM11 GM14

/-- The free-edge discs of XII (4.3), page 250, including claims
(5)--(6). Topological feasibility is the remaining claim (7). -/
theorem exists_spaced_free_edge_discs
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ k t : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    (hk : 1 ≤ k) (hθ : 5 + t * (k + 7) ≤ θ) :
    ∃ (f : Fin t → Set S) (a b : Fin t → S) (Δ r : Fin t → Set S),
      (∀ i, Γ.toGraph.IsLink (f i) (a i) (b i) ∧ a i ≠ b i ∧
        IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = {a i, b i} ∧
        ({a i, b i} : Set S) ⊆ discBd (Δ i) ∧
        Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i) ∧
        IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ i)) ∧
        r i ∈ Γ.R ∧ f i ⊆ closure (r i) ∧ (r i ∩ Δ i).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) ∧
      (∀ i j, i ≠ j → k ≤ d (r i) (r j)) ∧
      (∀ i j, i ≠ j → k + 4 ≤ d (f i) (f j)) := by
  classical
  obtain ⟨f, a, b, hf, hsep⟩ := exists_spaced_free_edges hS hm hθ
  have hex : ∀ i : Fin t, ∃ (D r : Set S), IsClosedDisc D ∧ r ∈ Γ.R ∧ f i ⊆ closure r ∧
      Γ.U ∩ D = {a i, b i} ∧ ({a i, b i} : Set S) ⊆ discBd D ∧
      Γ.U ∩ D = Γ.V ∩ discBd D ∧ (r ∩ D).Nonempty := by
    intro i
    exact exists_empty_disc_at_edge hS (hf i).2.1 (hf i).2.2.1
  choose Δ r hD hr hcl hUD hbd havoid hmeet using hex
  refine ⟨f, a, b, Δ, r, ?_, ?_, ?_, hsep⟩
  · intro i
    refine ⟨(hf i).2.1, (hf i).2.2.1, hD i, hUD i, hbd i, havoid i, ?_, hr i, hcl i, hmeet i⟩
    rw [← havoid i, hUD i]
    exact (hf i).2.2.2
  · intro i j hij
    exact empty_discs_disjoint_of_edges_distant hS hm (hf i).2.1 (hf j).2.1 (hD i) (hD j)
      (hUD i) (hUD j) (havoid i) (havoid j) (hr i) (hr j) (hcl i) (hcl j) (hmeet i) (hmeet j)
      ((show 5 ≤ k + 4 by omega).trans (hsep i j hij))
  · intro i j hij
    exact incident_regions_distance_ge hS hm (hf i).1 (hf j).1 (hr i) (hr j) (hcl i) (hcl j)
      (hsep i j hij)

end GraphMinor.GM12
