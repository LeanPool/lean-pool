/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM16.Section6
public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM16.Section6Clearing
import LeanPool.GraphMinor.GM16.Section9ClearFamily
import LeanPool.GraphMinor.GM16.Section9Compressions
import LeanPool.GraphMinor.GM16.Section9Dials
import LeanPool.GraphMinor.GM16.Section9ZonePreservation
import LeanPool.GraphMinor.GM16.SpanCongr
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM14.Section3b


import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

/-!
# The span after clearing the envelope

In XVI (8.1), the drawing and tangle after all clearings are still a
span controlled by the original tangle. Apply the single-clearing
span lemma at each step. The envelope gives rigidity for every
intermediate drawing, and uniqueness of compression identifies the
result with the chosen final tangle.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The span assertion after the successive clearings in the proof of
XVI (8.1), pages 71–72. The embedding is the restriction of the original
embedding to the complement of the entire envelope. -/
theorem span_after_clearFamily
    (hS : IsClosedSurface S) (ys : Finset S) (Λ : S → Set S) (γ : ℕ)
    {α : Type u} {β : Type v} {G : Graph α β} {H : Drawing S}
    (η : SpanEmbedding H G) {θ_star θ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ}
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T)
    (hEnv : IsEnvelope H d (ys : Set S) γ Λ)
    (hComp : IsLambdaCompression H (clearEnvelopeDrawing H (ys : Set S) Λ)
      θ ((4 * γ + 2) * ys.card) T T' d d') :
    IsSigmaSpan G (clearEnvelopeDrawing H (ys : Set S) Λ)
      (restrictCleared η (⋃ y ∈ (ys : Set S), Λ y))
      θ_star (θ - (4 * γ + 2) * ys.card) T_star T' := by
  classical
  induction ys using Finset.induction_on generalizing H θ T d T' d' with
  | empty =>
    have hUnion : (⋃ y ∈ (↑(∅ : Finset S) : Set S), Λ y) = ∅ := by simp
    have hDraw : clearEnvelopeDrawing H (↑(∅ : Finset S)) Λ = H := by
      change H.interSet (univ \ ⋃ y ∈ (↑(∅ : Finset S) : Set S), Λ y) = H
      rw [hUnion, sdiff_empty, drawing_interSet_univ]
    have hc : IsLambdaCompression H H θ 0 T T' d d' := by
      simpa only [Finset.card_empty, Nat.mul_zero, hDraw] using hComp
    have hSelf : IsLambdaCompression H H θ 0 T T d d :=
      ⟨hc.lam_lt, hc.hasMetric, by simpa only [Nat.sub_zero] using hc.hasMetric,
        fun _ _ => Nat.le_add_right _ _⟩
    have hT := compression_unique hS inferInstance hSelf hc
    have hSpan' := span_congr_drawing_embedding hDraw.symm η
      (restrictCleared η (⋃ y ∈ (↑(∅ : Finset S) : Set S), Λ y)) rfl rfl hSpan
    simpa only [Finset.card_empty, Nat.mul_zero, Nat.sub_zero, ← hT] using hSpan'
  | @insert j ys hj ih =>
    let c := 4 * γ + 2
    have hjmem : j ∈ insert j ys := Finset.mem_insert_self _ _
    have hθ : c * (ys.card + 1) < θ := by
      simpa only [Finset.card_insert_of_notMem hj] using hComp.lam_lt
    have hθj : c < θ := by
      have hb := Nat.mul_le_mul_left c (show 1 ≤ ys.card + 1 by omega)
      omega
    have hZone := hEnv.2.1
    have hdis := hEnv.2.2.1
    obtain ⟨T₁, d₁, hClear, _⟩ := GraphMinor.GM14.theorem_3_2_proof hS inferInstance
      (by dsimp only [c] at hθj; omega) hComp.hasMetric (hZone j hjmem)
    let H₁ := clearedSubdrawing H (Λ j)
    have hRig₁ : IsRigid H₁ := by
      have hrig := hEnv.2.2.2 {j} (singleton_subset_iff.mpr hjmem)
      have hu : (⋃ y ∈ ({j} : Set S), Λ y) = Λ j := by simp
      rw [hu] at hrig
      exact hrig
    have hSpan₁ : IsSigmaSpan G H₁ (restrictCleared η (Λ j)) θ_star (θ - c) T_star T₁ := by
      simpa only [c, Nat.sub_sub] using IsSigmaSpan.clear hSpan hClear hRig₁
    have hY₁ : (ys : Set S) ⊆ H₁.V := by
      intro y hy
      have hyj : y ≠ j := fun heq => hj (heq ▸ hy)
      have hyAll : y ∈ insert j ys := Finset.mem_insert_of_mem hy
      exact (mem_interSet_V_iff (isClosed_univ.sdiff (hZone j hjmem).isOpenDisc.1)).mpr
        ⟨hEnv.1 hyAll, mem_univ _, fun hyj' => (hdis y hyAll j hjmem hyj).notMem_of_mem_left
          (subset_closure ((hZone y hyAll).z_subset (mem_singleton y))) (subset_closure hyj')⟩
    have hZone₁ : ∀ y ∈ (ys : Set S), IsLambdaZoneAround H₁ d₁ γ {y} (Λ y) := by
      intro y hy
      have hyAll : y ∈ insert j ys := Finset.mem_insert_of_mem hy
      exact zone_after_disjoint_clearing (hEnv.1 hyAll) (hZone y hyAll) (hZone j hjmem)
        (hdis y hyAll j hjmem (fun heq => hj (heq ▸ hy))) hClear
    have hEnv₁ : IsEnvelope H₁ d₁ (ys : Set S) γ Λ := by
      refine ⟨hY₁, hZone₁, ?_, ?_⟩
      · exact fun y hy z hz hne => hdis y (Finset.mem_insert_of_mem hy) z
          (Finset.mem_insert_of_mem hz) hne
      · intro Y' hY'
        have hSub : insert j Y' ⊆ (↑(insert j ys) : Set S) := by
          intro y hy
          rcases hy with rfl | hy
          · exact hjmem
          · exact Finset.mem_insert_of_mem (hY' hy)
        change IsRigid (clearEnvelopeDrawing (clearedSubdrawing H (Λ j)) Y' Λ)
        rw [clearFamily_after_single H Y' Λ j (fun y hy => (hZone y (hSub hy)).isOpenDisc.1)]
        exact hEnv.2.2.2 (insert j Y') hSub
    have hθrem : c * ys.card < θ - c := by
      rw [Nat.mul_add, Nat.mul_one] at hθ
      omega
    obtain ⟨T₂, d₂, hComp₂, _⟩ := exists_compression_clearFamily hS ys Λ γ
      (show HasTangleMetric H₁ (θ - c) T₁ d₁ by simpa only [c, Nat.sub_sub] using hClear.hasMetric)
      (fun y hy => hY₁ hy) hZone₁ hEnv₁.2.2.1 hθrem
    have hSpan₂ := ih (restrictCleared η (Λ j)) hSpan₁ hEnv₁ hComp₂
    have hSet : insert j (ys : Set S) = (↑(insert j ys) : Set S) := by simp
    have hDraw : clearEnvelopeDrawing H₁ (ys : Set S) Λ = clearEnvelopeDrawing H (↑(insert j ys)) Λ
      := by
      rw [show H₁ = clearedSubdrawing H (Λ j) from rfl,
        clearFamily_after_single H (ys : Set S) Λ j (fun y hy =>
          (hZone y (show y ∈ (↑(insert j ys) : Set S) from hSet ▸ hy)).isOpenDisc.1), hSet]
    have hTot := compression_comp (compression_of_clearing hComp.hasMetric hθj hClear) hComp₂
    rw [hDraw] at hTot
    have hLoss : c + c * ys.card = c * (insert j ys).card := by
      rw [Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.mul_one, Nat.add_comm]
    rw [hLoss] at hTot
    have hT : T₂ = T' := compression_unique hS inferInstance hTot hComp
    have hTransport := span_congr_drawing_embedding hDraw
      (restrictCleared (restrictCleared η (Λ j)) (⋃ y ∈ (ys : Set S), Λ y))
      (restrictCleared η (⋃ y ∈ (↑(insert j ys) : Set S), Λ y)) rfl rfl hSpan₂
    rw [hT] at hTransport
    have hOrder : θ - c - c * ys.card = θ - c * (insert j ys).card := by
      rw [Nat.sub_sub, hLoss]
    rw [hOrder] at hTransport
    exact hTransport

end GraphMinor.GM16
