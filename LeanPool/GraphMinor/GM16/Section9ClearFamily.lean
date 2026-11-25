/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM16.Section9Compressions
import LeanPool.GraphMinor.GM16.Section9Dials
import LeanPool.GraphMinor.GM16.Section9ZonePreservation
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM14.Section3b


import LeanPool.GraphMinor.GM12.Section710

/-!
# Clearing all the battlefield discs

XVI (8.1), page 71, clears the discs one at a time. Each remaining
disc is still a zone. Induction gives the stated total loss of order
and the two comparisons of point distances.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- Clearing one disc preserves the centres and zones of the remaining disjoint discs. -/
theorem clearing_preserves_disjoint_zones
    {H : Drawing S} {γ θ : ℕ}
    {T T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d₁ : Set S → Set S → ℕ} {ys : Finset S} {j : S} {Λ : S → Set S}
    (hY : ∀ y ∈ ys, y ∈ H.V)
    (hZone : ∀ y ∈ ys, IsLambdaZoneAround H d γ {y} (Λ y))
    (hjZone : IsLambdaZoneAround H d γ {j} (Λ j))
    (hdis : ∀ y ∈ ys, Disjoint (closure (Λ y)) (closure (Λ j)))
    (hClear : IsClearedTangle H T d θ γ (Λ j) T₁ d₁) :
    (∀ y ∈ ys, y ∈ (clearedSubdrawing H (Λ j)).V) ∧
    ∀ y ∈ ys, IsLambdaZoneAround (clearedSubdrawing H (Λ j)) d₁ γ {y} (Λ y) := by
  constructor
  · intro y hy
    exact (mem_interSet_V_iff (isClosed_univ.sdiff hjZone.isOpenDisc.1)).mpr
      ⟨hY y hy, mem_univ _, fun hyj => (hdis y hy).notMem_of_mem_left
        (subset_closure ((hZone y hy).z_subset (mem_singleton y))) (subset_closure hyj)⟩
  · intro y hy
    exact zone_after_disjoint_clearing (hY y hy) (hZone y hy) hjZone (hdis y hy) hClear

omit [ConnectedSpace S] in
/-- Clearing an inserted disc first yields the same drawing as removing the union at once. -/
theorem clearEnvelopeDrawing_insert [DecidableEq S] (H : Drawing S) (ys : Finset S) (j : S)
    (Λ : S → Set S) (hOpen : ∀ y ∈ insert j ys, IsOpen (Λ y)) :
    clearEnvelopeDrawing (clearedSubdrawing H (Λ j)) (ys : Set S) Λ =
      clearEnvelopeDrawing H (↑(insert j ys)) Λ := by
  unfold clearEnvelopeDrawing clearedSubdrawing
  have hclosedYs : IsClosed (univ \ ⋃ y ∈ (ys : Set S), Λ y) :=
    isClosed_univ.sdiff (isOpen_iUnion fun y => isOpen_iUnion fun hy =>
      hOpen y (Finset.mem_insert_of_mem hy))
  rw [drawing_interSet_inter_closed H (isClosed_univ.sdiff (hOpen j (Finset.mem_insert_self _ _)))
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

omit [ConnectedSpace S] in
/-- Combine the compression and point-distance comparison from one clearing with the rest. -/
theorem compression_of_clearFamily_insert [DecidableEq S]
    {H : Drawing S} {γ θ : ℕ} {ys : Finset S} {j : S} (hj : j ∉ ys) {Λ : S → Set S}
    {T T₁ T₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d₁ d₂ : Set S → Set S → ℕ}
    (hMet : HasTangleMetric H θ T d) (hθj : 4 * γ + 2 < θ)
    (hClear : IsClearedTangle H T d θ γ (Λ j) T₁ d₁)
    (heq : clearEnvelopeDrawing (clearedSubdrawing H (Λ j)) (ys : Set S) Λ =
      clearEnvelopeDrawing H (↑(insert j ys)) Λ)
    (hComp₂ : IsLambdaCompression (clearedSubdrawing H (Λ j))
      (clearEnvelopeDrawing (clearedSubdrawing H (Λ j)) (ys : Set S) Λ)
      (θ - (4 * γ + 2)) ((4 * γ + 2) * ys.card) T₁ T₂ d₁ d₂)
    (hLe₂ : ∀ x y : S,
      pointDist (clearEnvelopeDrawing (clearedSubdrawing H (Λ j)) (ys : Set S) Λ) d₂ x y ≤
        pointDist (clearedSubdrawing H (Λ j)) d₁ x y) :
    IsLambdaCompression H (clearEnvelopeDrawing H (↑(insert j ys)) Λ)
      θ ((4 * γ + 2) * (insert j ys).card) T T₂ d d₂ ∧
      ∀ x y : S,
        pointDist (clearEnvelopeDrawing H (↑(insert j ys)) Λ) d₂ x y ≤ pointDist H d x y := by
  constructor
  · have hc := compression_comp (compression_of_clearing hMet hθj hClear) hComp₂
    rw [heq] at hc
    simpa only [Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.mul_one, Nat.add_comm] using hc
  · intro x y
    rw [← heq]
    exact (hLe₂ x y).trans (clearing_pointDist_le hClear x y)

/-- The successive clearings in XVI (8.1), page 71, have total loss
`(4γ + 2)|Y|`. No choice of their order is part of the conclusion. -/
theorem exists_compression_clearFamily
    (hS : IsClosedSurface S) (ys : Finset S) (Λ : S → Set S) (γ : ℕ)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hMet : HasTangleMetric H θ T d)
    (hY : ∀ y ∈ ys, y ∈ H.V)
    (hZone : ∀ y ∈ ys, IsLambdaZoneAround H d γ {y} (Λ y))
    (hdis : ∀ y ∈ ys, ∀ z ∈ ys, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)))
    (hθ : (4 * γ + 2) * ys.card < θ) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ),
      IsLambdaCompression H (clearEnvelopeDrawing H (ys : Set S) Λ)
        θ ((4 * γ + 2) * ys.card) T T' d d' ∧
      ∀ x y : S, pointDist (clearEnvelopeDrawing H (ys : Set S) Λ) d' x y ≤ pointDist H d x y := by
  classical
  induction ys using Finset.induction_on generalizing H θ T d with
  | empty =>
    have heq : clearEnvelopeDrawing H (↑(∅ : Finset S)) Λ = H := by
      change H.interSet (univ \ ⋃ y ∈ (↑(∅ : Finset S) : Set S), Λ y) = H
      simp only [Finset.coe_empty]
      have hu : (⋃ y ∈ (∅ : Set S), Λ y) = ∅ := by simp
      simpa using drawing_interSet_univ H
    refine ⟨T, d, ?_, ?_⟩
    · simpa only [Finset.card_empty, Nat.mul_zero, heq, Nat.sub_zero] using
        (show IsLambdaCompression H H θ 0 T T d d from
          ⟨by simpa using hθ, hMet, hMet, fun _ _ => Nat.le_add_right _ _⟩)
    · intro x y
      rw [heq]
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
    obtain ⟨hY₁, hZone₁⟩ := clearing_preserves_disjoint_zones
      (fun y hy => hY y (Finset.mem_insert_of_mem hy))
      (fun y hy => hZone y (Finset.mem_insert_of_mem hy)) (hZone j hjmem)
      (fun y hy => hdis y (Finset.mem_insert_of_mem hy) j hjmem
        (fun heq => hj (heq ▸ hy))) hClear
    have hθ₁ : (4 * γ + 2) * ys.card < θ - (4 * γ + 2) := by
      rw [Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.mul_one] at hθ
      omega
    obtain ⟨T₂, d₂, hComp₂, hLe₂⟩ := ih hMet₁ hY₁ hZone₁
      (fun y hy z hz hne => hdis y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
        hne) hθ₁
    have heq := clearEnvelopeDrawing_insert H ys j Λ
      (fun y hy => (hZone y hy).isOpenDisc.1)
    obtain ⟨hComp, hLe⟩ := compression_of_clearFamily_insert hj hMet hθj hClear heq hComp₂ hLe₂
    exact ⟨T₂, d₂, hComp, hLe⟩

end GraphMinor.GM16
