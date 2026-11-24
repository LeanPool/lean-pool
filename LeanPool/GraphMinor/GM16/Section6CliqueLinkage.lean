/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6CliquePaths
import LeanPool.GraphMinor.GM09.Basic

import LeanPool.GraphMinor.GM12.Bridge

/-!
# Applying the marked-path threshold to old-graph paths

The union of old-graph paths has no old-graph edge, and its old-graph
vertices are just their ends. Thus the chosen threshold used in XVI
(6.3) applies directly to a separated family of old-graph paths.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Separated old-graph paths satisfy the marked-path threshold chosen
for the proof of XVI (6.3). -/
theorem controlsMinor_of_separated_hPaths
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (p : ℕ)
    {α : Type u} {β : Type v} {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ_span : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {P : Fin (p * (p - 1) / 2) → Graph α β} {s t : Fin (p * (p - 1) / 2) → S}
    (hSpan : IsSigmaSpan G H η θ_star θ_span T_star T) (hMet : HasTangleMetric H θ_span T d)
    (horder : cliquePathThreshold.{u, v, w} hS hConn p ≤ θ_span)
    (hst : ∀ i, s i ∈ H.V ∧ t i ∈ H.V)
    (hP : ∀ i, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (s i)) (η.vMap (t i)))
    (hPP : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hsep : ∀ a ∈ range s ∪ range t, ∀ b ∈ range s ∪ range t,
      a ≠ b → cliquePathThreshold.{u, v, w} hS hConn p ≤ d {a} {b}) :
    ControlsMinor G (completeGraph p) T_star := by
  let K := subgraphSUnion G (range P)
  let Y := range s ∪ range t
  have hF : ∀ R ∈ range P, R ≤ G := by
    rintro R ⟨i, rfl⟩
    exact (hP i).2.1.le
  have hKG : K ≤ G := subgraphSUnion_le hF
  have hKH : Disjoint E(K) E(η.imageGraph) := by
    apply Set.disjoint_left.mpr
    intro e heK heH
    rw [edgeSet_subgraphSUnion hF] at heK
    obtain ⟨R, ⟨i, rfl⟩, heR⟩ := mem_iUnion₂.mp heK
    exact (Set.disjoint_left.mp (hP i).2.2.2.2.2.2) heR heH
  have hKY : V(K) ∩ V(η.imageGraph) ⊆ η.vMap '' Y := by
    rintro x ⟨hxK, hxH⟩
    obtain ⟨R, ⟨i, rfl⟩, hxR⟩ := mem_iUnion₂.mp hxK
    have hx : x ∈ ({η.vMap (s i), η.vMap (t i)} : Set α) :=
      (hP i).2.2.2.2.2.1 ▸ ⟨hxR, hxH⟩
    rcases hx with hx | hx
    · exact ⟨s i, Or.inl ⟨i, rfl⟩, hx.symm⟩
    · exact ⟨t i, Or.inr ⟨i, rfl⟩, (mem_singleton_iff.mp hx).symm⟩
  have hY : Y ⊆ H.V := by
    rintro y (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (hst i).1
    · exact (hst i).2
  apply (cliquePathThreshold_spec hS hConn p).2 G K θ_star θ_span T_star H η T d Y
    P (fun i => η.vMap (s i)) (fun i => η.vMap (t i)) hSpan hMet horder hY hsep hKG hKH hKY
  · intro i
    exact ⟨(hP i).2.2.2.1, (hP i).2.2.2.2.1, (hP i).2.2.1,
      (hP i).2.1.of_le (le_subgraphSUnion hF ⟨i, rfl⟩)⟩
  · exact hPP

/-- When `p` has no pair of distinct vertices, the path requirement is
empty. This supplies the small-`p` case of XVI (6.3), page 59. -/
theorem controlsMinor_of_zero_pairs
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S) (p : ℕ)
    {α : Type u} {β : Type v} {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ_span : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hSpan : IsSigmaSpan G H η θ_star θ_span T_star T) (hMet : HasTangleMetric H θ_span T d)
    (horder : cliquePathThreshold.{u, v, w} hS hConn p ≤ θ_span)
    (hμ : p * (p - 1) / 2 = 0) : ControlsMinor G (completeGraph p) T_star := by
  have hempty : Fin (p * (p - 1) / 2) → False := by
    intro i
    have hi := i.isLt
    omega
  apply controlsMinor_of_separated_hPaths hS hConn p
    (P := fun i => (hempty i).elim) (s := fun i => (hempty i).elim)
    (t := fun i => (hempty i).elim) hSpan hMet horder
    (fun i => (hempty i).elim) (fun i => (hempty i).elim) (fun i => (hempty i).elim)
  rintro a (⟨i, _⟩ | ⟨i, _⟩) <;> exact (hempty i).elim

end GraphMinor.GM16
