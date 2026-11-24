/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
import LeanPool.GraphMinor.GM16.Section9CircleSelection
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM14.Section3

import LeanPool.GraphMinor.GM16.Theorem35Bridge

/-!
# Applying XV (3.5) to the selected boundary linkage

XVI (8.1), Claim (4), starts with `φ²` disjoint paths. The selection
on two circles retains `φ` paths in the required orders. Their ends
remain free because they form subsets of the free boundary sets.
XV (3.5) then gives the span on the surface with a handle added.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14
  GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- The linkage-to-handle step in XVI (8.1), Claim (4), page 72.
All the boundary order requirements of XV (3.5) are proved by the
Erdős–Szekeres selection, rather than omitted from the cited result. -/
theorem handle_span_of_boundary_linkage
    {α : Type u} {β : Type v} {G : Graph α β} {H : Drawing S} (η : SpanEmbedding H G)
    {θ_star θ φ : ℕ} {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    {Λ₁ Λ₂ X₁ X₂ : Set S}
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T) (hMet : HasTangleMetric H θ T d)
    (hΛ₁ : Λ₁ ∈ H.R) (hΛ₂ : Λ₂ ∈ H.R) (hne : Λ₁ ≠ Λ₂)
    (hF₁ : IsOArc (subBd Λ₁)) (hF₂ : IsOArc (subBd Λ₂))
    (hC₁ : (H.interSet (subBd Λ₁)).IsCircuit) (hC₂ : (H.interSet (subBd Λ₂)).IsCircuit)
    (hNoRegion : ∀ r ∈ H.R, ¬ ((∃ x ∈ (H.interSet (subBd Λ₁)).V, x ∈ closure r) ∧
      ∃ y ∈ (H.interSet (subBd Λ₂)).V, y ∈ closure r))
    (hLine : ∀ F : Set S, IsLine F → H.IsNormal F → F ⊆ univ \ (Λ₁ ∪ Λ₂) →
      (F ∩ subBd Λ₁).Nonempty → (F ∩ subBd Λ₂).Nonempty → φ ≤ (F ∩ H.V).ncard)
    (hφ : 3 ≤ φ) (hX₁ : X₁ ⊆ (H.interSet (subBd Λ₁)).V)
    (hX₂ : X₂ ⊆ (H.interSet (subBd Λ₂)).V)
    (hFree₁ : IsFreeSet H.toHypergraph T θ X₁) (hFree₂ : IsFreeSet H.toHypergraph T θ X₂)
    (P : Fin (φ ^ 2) → Graph α β) (a b : Fin (φ ^ 2) → S)
    (hEnds : ∀ i, a i ∈ X₁ ∧ b i ∈ X₂)
    (hP : ∀ i, IsHPathWithEnds G η.imageGraph (P i) (η.vMap (a i)) (η.vMap (b i)))
    (hDis : Pairwise (fun i j => Disjoint V(P i) V(P j))) :
    ∃ (S' : Type w) (_ : TopologicalSpace S') (_ : T2Space S'),
      IsObtainedByAddingHandle S S' ∧
      ∃ (H' : Drawing S') (η' : SpanEmbedding H' G)
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsSigmaSpan G H' η' θ_star φ T_star T' := by
  have ha : Function.Injective a := by
    intro i j hij
    by_contra hneij
    have hx := (hP i).2.1.left_mem
    have hy := (hP j).2.1.left_mem
    rw [← hij] at hy
    exact (hDis hneij).notMem_of_mem_left hx hy
  have hb : Function.Injective b := by
    intro i j hij
    by_contra hneij
    have hx := (hP i).2.1.right_mem
    have hy := (hP j).2.1.right_mem
    rw [← hij] at hy
    exact (hDis hneij).notMem_of_mem_left hx hy
  obtain ⟨φ₁⟩ := hF₁
  obtain ⟨φ₂⟩ := hF₂
  have haF : ∀ i, a i ∈ subBd Λ₁ := by
    intro i
    exact interSet_U_subset (by rw [subBd_eq_frontier]; exact isClosed_frontier)
      ((H.interSet (subBd Λ₁)).V_subset_U (hX₁ (hEnds i).1))
  have hbF : ∀ i, b i ∈ subBd Λ₂ := by
    intro i
    exact interSet_U_subset (by rw [subBd_eq_frontier]; exact isClosed_frontier)
      ((H.interSet (subBd Λ₂)).V_subset_U (hX₂ (hEnds i).2))
  obtain ⟨g, hg, hOrder₁, hOrder₂⟩ := section9_select_circle_orders φ₁ φ₂ φ
    (by omega) a b ha hb haF hbF
  apply GraphMinor.GM16.gm15Theorem35.{u,v,w} G H η θ_star θ φ T_star T d Λ₁ Λ₂ (P ∘ g) (a ∘ g)
    (b ∘ g)
    hSpan hMet hΛ₁ hΛ₂ hne hC₁ hC₂ hNoRegion hLine hφ (ha.comp hg) (hb.comp hg) hOrder₁ hOrder₂
    (fun i => ⟨hX₁ (hEnds (g i)).1, hX₂ (hEnds (g i)).2⟩) (fun i => hP (g i))
    (fun i j hij => hDis (fun heq => hij (hg heq)))
  · apply freeSet_subset hMet.1.2.1 hFree₁
    rintro x ⟨i, rfl⟩
    exact (hEnds (g i)).1
  · apply freeSet_subset hMet.1.2.1 hFree₂
    rintro x ⟨i, rfl⟩
    exact (hEnds (g i)).2

end GraphMinor.GM16
