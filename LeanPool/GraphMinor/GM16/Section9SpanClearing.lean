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
    have hDraw := clearEnvelopeDrawing_empty H Λ
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
    obtain ⟨T₁, T₂, d₁, d₂, hClear, hRig₁, hEnv₁, hComp₂, hTot⟩ :=
      exists_compression_clearEnvelope_insert hS hj hComp.hasMetric hEnv hComp.lam_lt
    let H₁ := clearedSubdrawing H (Λ j)
    have hSpan₁ : IsSigmaSpan G H₁ (restrictCleared η (Λ j)) θ_star (θ - c) T_star T₁ := by
      simpa only [c, Nat.sub_sub] using IsSigmaSpan.clear hSpan hClear hRig₁
    have hSpan₂ := ih (restrictCleared η (Λ j)) hSpan₁ hEnv₁ hComp₂
    have hDraw := clearEnvelopeDrawing_insert H ys j Λ
      (fun y hy => (hEnv.2.1 y hy).isOpenDisc.1)
    have hLoss : c + c * ys.card = c * (insert j ys).card := by
      rw [Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.mul_one, Nat.add_comm]
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
