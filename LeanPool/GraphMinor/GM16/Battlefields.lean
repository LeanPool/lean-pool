/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM10.Section12

/-!
# Battlefields and their selected boundary vertices

XIV defines a battlefield without requiring that its boundary set have
exactly the size parameter many vertices. In the proof of XVI (8.1), select
the ends of the specified disjoint paths to obtain a boundary set of that
size. The normalization is proved here rather than included in the cited
existence result.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Function GraphMinor.GM10 GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T1Space S]

/-- A battlefield as defined in Graph Minors XIV, Section 9, page 45.
In particular condition (ii) says `X ⊆ V(H) ∩ bd(Λ)` and that `X` is free,
not that `|X| = β`. XVI chooses a set of that cardinality on page 71. -/
structure IsBattlefieldData (H : Drawing S)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (θ beta : ℕ) (z Λ : Set S) (C : Drawing S) (X : Set S) : Prop where
  params_valid : 4 ≤ beta ∧ Even beta ∧ 12 * beta + 15 ≤ θ ∧ z ∈ H.A
  isZone : IsLambdaZoneAround H d (3 * beta + 3) z Λ
  isRigid_cleared : IsRigid (clearedSubdrawing H Λ)
  isFree_X : X ⊆ H.V ∩ subBd Λ ∧
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ),
      IsClearedTangle H T d θ (3 * beta + 3) Λ T' d' ∧
      IsFreeSet (clearedSubdrawing H Λ).toHypergraph T' (θ - 4 * (3 * beta + 3) - 2) X
  circuit_and_paths :
    C.IsCircuit ∧ C.IsSubdrawing H ∧ C.U ⊆ Λ ∧
    ∃ P : Fin beta → Drawing S,
      (∀ k, ∃ u ∈ C.V, ∃ v ∈ X,
        (P k).IsPathBetween u v ∧ (P k).IsSubdrawing H ∧
        (P k).U ∩ (H.U ∩ subBd Λ) = {v}) ∧
      Pairwise (fun i j => Disjoint (P i).V (P j).V)
  regionalDistance_ge : 1 + beta / 2 ≤ regionalDistance H C.U (subBd Λ)
  openDisc_includes : ∃ Δ₀ : Set S,
    IsOpenDisc Δ₀ ∧ Δ₀ ⊆ Λ ∧ subBd Δ₀ = C.U ∧
      ∀ x ∈ H.A, d z x < beta → x ⊆ Δ₀

/-- The normalization in Graph Minors XVI, proof of (8.1), page 71:
"We may assume that $|X_i| = \beta$ for each $i$."
Choose the ends in `X` of the `β` disjoint paths. Their ends are distinct,
and their set remains free because it is a subset of `X`. -/
theorem IsBattlefieldData.normalize {H : Drawing S}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ beta : ℕ} {z Λ : Set S} {C : Drawing S} {X : Set S}
    (h : IsBattlefieldData H T d θ beta z Λ C X) :
    ∃ X' ⊆ X, GM14.IsBattlefield H T d θ beta z Λ C X' := by
  classical
  obtain ⟨P, hP, hdisj⟩ := h.circuit_and_paths.2.2.2
  choose u hu v hv hpath hsub hboundary using hP
  have hvmem : ∀ i, v i ∈ (P i).V := by
    intro i
    obtain ⟨W, _, hV, _⟩ := hpath i
    rw [hV]
    exact W.end_mem_support
  have hinj : Injective v := by
    intro i j hij
    by_contra hne
    exact (hdisj hne).notMem_of_mem_left (hvmem i) (hij ▸ hvmem j)
  have hXsub : range v ⊆ X := by rintro _ ⟨i, rfl⟩; exact hv i
  obtain ⟨T', d', hclear, hfree⟩ := h.isFree_X.2
  refine ⟨range v, hXsub, h.params_valid, h.isZone, h.isRigid_cleared,
    ⟨hXsub.trans h.isFree_X.1, ?_, T', d', hclear, ?_⟩,
    ⟨h.circuit_and_paths.1, h.circuit_and_paths.2.1, h.circuit_and_paths.2.2.1,
      P, ?_, hdisj⟩, h.regionalDistance_ge, h.openDisc_includes⟩
  · rw [Set.ncard_range_of_injective hinj]
    simp
  · exact hfree.subset hclear.hasMetric.1.2.1 hXsub
  · intro i
    exact ⟨u i, hu i, v i, mem_range_self i, hpath i, hsub i, hboundary i⟩

end GraphMinor.GM16
