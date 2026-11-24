/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM16.Section9FreeClearing
import LeanPool.GraphMinor.GM16.Section9Compressions
import LeanPool.GraphMinor.GM16.Section9Dials
import LeanPool.GraphMinor.GM16.Section9ZonePreservation
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM14.Section3b


import LeanPool.GraphMinor.GM12.Section710

/-!
# Free sets after clearing the battlefield discs

XVI (8.1), page 71, clears the discs one at a time. Each remaining
disc is still a zone. Induction gives the stated total loss of order
and the two comparisons of point distances.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The successive clearings in XVI (8.1), page 71, have total loss
`(4γ + 2)|Y|`. No choice of their order is part of the conclusion. -/
theorem exists_free_compression_clearFamily
    (hS : IsClosedSurface S) (ys : Finset S) (Λ : S → Set S) (γ : ℕ)
    (hγ : 2 ≤ γ) (X : Set S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hMet : HasTangleMetric H θ T d)
    (hY : ∀ y ∈ ys, y ∈ H.V)
    (hZone : ∀ y ∈ ys, IsLambdaZoneAround H d γ {y} (Λ y))
    (hdis : ∀ y ∈ ys, ∀ z ∈ ys, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)))
    (hθ : (4 * γ + 2) * ys.card < θ)
    (hFree : GM10.IsFreeSet H.toHypergraph T θ X)
    (hFar : ∀ y ∈ ys, ∀ v ∈ X,
      2 * X.ncard + 5 * γ + 2 + (4 * γ + 2) * ys.card < d {y} {v}) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ),
      IsLambdaCompression H (clearEnvelopeDrawing H (ys : Set S) Λ)
        θ ((4 * γ + 2) * ys.card) T T' d d' ∧
      (∀ x y : S, pointDist (clearEnvelopeDrawing H (ys : Set S) Λ) d' x y ≤ pointDist H d x y) ∧
      GM10.IsFreeSet (clearEnvelopeDrawing H (ys : Set S) Λ).toHypergraph T'
        (θ - (4 * γ + 2) * ys.card) X := by
  classical
  induction ys using Finset.induction_on generalizing H θ T d with
  | empty =>
    have heq : clearEnvelopeDrawing H (↑(∅ : Finset S)) Λ = H := by
      change H.interSet (univ \ ⋃ y ∈ (↑(∅ : Finset S) : Set S), Λ y) = H
      simp only [Finset.coe_empty]
      have hu : (⋃ y ∈ (∅ : Set S), Λ y) = ∅ := by simp
      simpa using drawing_interSet_univ H
    refine ⟨T, d, ?_, ?_, ?_⟩
    · simpa only [Finset.card_empty, Nat.mul_zero, heq, Nat.sub_zero] using
        (show IsLambdaCompression H H θ 0 T T d d from
          ⟨by simpa using hθ, hMet, hMet, fun _ _ => Nat.le_add_right _ _⟩)
    · intro x y
      rw [heq]
    · simpa only [heq, Finset.card_empty, Nat.mul_zero, Nat.sub_zero] using hFree
  | @insert j ys hj ih =>
    have hjmem : j ∈ insert j ys := Finset.mem_insert_self _ _
    have hθj : 4 * γ + 2 < θ := by
      rw [Finset.card_insert_of_notMem hj] at hθ
      have hb := Nat.mul_le_mul_left (4 * γ + 2) (show 1 ≤ ys.card + 1 by omega)
      omega
    obtain ⟨T₁, d₁, hClear, _⟩ := GraphMinor.GM14.theorem_3_2_proof hS inferInstance
      (by omega) hMet (hZone j hjmem)
    let H₁ := clearedSubdrawing H (Λ j)
    have hMet₁ : HasTangleMetric H₁ (θ - (4 * γ + 2)) T₁ d₁ := by
      simpa only [Nat.sub_sub] using hClear.hasMetric
    have hY₁ : ∀ y ∈ ys, y ∈ H₁.V := by
      intro y hy
      have hne : y ≠ j := fun heq => hj (heq ▸ hy)
      have hyAll : y ∈ insert j ys := Finset.mem_insert_of_mem hy
      exact (mem_interSet_V_iff (isClosed_univ.sdiff (hZone j hjmem).isOpenDisc.1)).mpr
        ⟨hY y hyAll, mem_univ _, fun hyj => (hdis y hyAll j hjmem hne).notMem_of_mem_left
          (subset_closure ((hZone y hyAll).z_subset (mem_singleton y))) (subset_closure hyj)⟩
    have hZone₁ : ∀ y ∈ ys, IsLambdaZoneAround H₁ d₁ γ {y} (Λ y) := by
      intro y hy
      have hyAll : y ∈ insert j ys := Finset.mem_insert_of_mem hy
      exact zone_after_disjoint_clearing (hY y hyAll) (hZone y hyAll) (hZone j hjmem)
        (hdis y hyAll j hjmem (fun heq => hj (heq ▸ hy))) hClear
    have hθ₁ : (4 * γ + 2) * ys.card < θ - (4 * γ + 2) := by
      rw [Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.mul_one] at hθ
      omega
    have hFree₁ := freeSet_after_clearing hS hMet hγ hθj (hZone j hjmem) hClear hFree
      (fun v hv => by have := hFar j hjmem v hv; omega)
    have hFar₁ : ∀ y ∈ ys, ∀ v ∈ X,
        2 * X.ncard + 5 * γ + 2 + (4 * γ + 2) * ys.card < d₁ {y} {v} := by
      intro y hy v hv
      have hOld := hFar y (Finset.mem_insert_of_mem hy) v hv
      rw [Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.mul_one] at hOld
      have hc := (compression_of_clearing hMet hθj hClear).dist_le y v
      rw [GraphMinor.GM15.pointDist_eq_of_mem_atom
        (Or.inl (Or.inl ⟨y, hY y (Finset.mem_insert_of_mem hy), rfl⟩))
        (Or.inl (Or.inl ⟨v, hFree.1 hv, rfl⟩)) (mem_singleton y) (mem_singleton v),
        GraphMinor.GM15.pointDist_eq_of_mem_atom
        (Or.inl (Or.inl ⟨y, hY₁ y hy, rfl⟩))
        (Or.inl (Or.inl ⟨v, hFree₁.1 hv, rfl⟩)) (mem_singleton y) (mem_singleton v)] at hc
      change d {y} {v} ≤ d₁ {y} {v} + (4 * γ + 2) at hc
      omega
    obtain ⟨T₂, d₂, hComp₂, hLe₂, hFree₂⟩ := ih hMet₁ hY₁ hZone₁
      (fun y hy z hz hne => hdis y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
        hne) hθ₁ hFree₁ hFar₁
    have heq : clearEnvelopeDrawing H₁ (ys : Set S) Λ =
        clearEnvelopeDrawing H (↑(insert j ys)) Λ := by
      unfold clearEnvelopeDrawing H₁ clearedSubdrawing
      have hclosedYs : IsClosed (univ \ ⋃ y ∈ (ys : Set S), Λ y) :=
        isClosed_univ.sdiff (isOpen_iUnion fun y => isOpen_iUnion fun hy =>
          (hZone y (Finset.mem_insert_of_mem hy)).isOpenDisc.1)
      rw [drawing_interSet_inter_closed H (isClosed_univ.sdiff (hZone j hjmem).isOpenDisc.1)
        hclosedYs]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_sdiff, mem_univ, true_and, mem_iUnion,
        Finset.mem_coe, Finset.mem_insert]
      constructor
      · rintro ⟨hxj, hxys⟩ ⟨y, hy, hxy⟩
        rcases hy with rfl | hy
        · exact hxj hxy
        · exact hxys ⟨y, hy, hxy⟩
      · intro hx
        exact ⟨fun hxj => hx ⟨j, Or.inl rfl, hxj⟩,
          fun ⟨y, hy, hxy⟩ => hx ⟨y, Or.inr hy, hxy⟩⟩
    refine ⟨T₂, d₂, ?_, ?_, ?_⟩
    · have hc := compression_comp (compression_of_clearing hMet hθj hClear) hComp₂
      rw [heq] at hc
      simpa only [Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.mul_one, Nat.add_comm] using hc
    · intro x y
      rw [← heq]
      exact (hLe₂ x y).trans (clearing_pointDist_le hClear x y)
    · rw [heq] at hFree₂
      simpa only [Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.mul_one, Nat.sub_sub,
        Nat.add_comm] using hFree₂

end GraphMinor.GM16
