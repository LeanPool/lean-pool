/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM16.EnvelopeAfterClearing
import LeanPool.GraphMinor.GM16.HornCongr
import LeanPool.GraphMinor.GM16.Section9ClearFamily
import LeanPool.GraphMinor.GM16.Section9Compressions
import LeanPool.GraphMinor.GM16.Section9Dials
import LeanPool.GraphMinor.GM16.Section6Clearing
import LeanPool.GraphMinor.GM16.SpanCongr
import LeanPool.GraphMinor.GM14.Section3b


import LeanPool.GraphMinor.GM11.CitedResults

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

/-!
# Horns after clearing an envelope

Apply XVI (6.2) once for each envelope disc. Each clearing loses one
horn path and `4γ + 2` units of breadth. The remaining discs are
still an envelope. Uniqueness of compression and of its metric
identifies the result with the given final compression. This proves
the repeated-clearing argument in XVI (7.1), Claim (4), page 69.
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
variable {α : Type u} {β : Type v}

/-- Clearing a finite envelope loses one path per disc from a horn,
with exactly the total breadth loss used in XVI (7.1), Claim (4). -/
theorem horn_after_clearFamily
     (hS : IsClosedSurface S)
    (ys : Finset S) (Λ : S → Set S) (γ σ : ℕ) (hγ : 2 ≤ γ)
    {G : Graph α β} {H : Drawing S} (η : SpanEmbedding H G) {θ_star θ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ}
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T)
    (hEnv : IsEnvelope H d (ys : Set S) γ Λ)
    (hComp : IsLambdaCompression H (clearEnvelopeDrawing H (ys : Set S) Λ)
      θ ((4 * γ + 2) * ys.card) T T' d d')
    {v : α} {P : Fin (σ + ys.card) → Graph α β} {u : Fin (σ + ys.card) → S}
    (hHorn : IsHorn G H η d v θ (σ + ys.card) P u) :
    ∃ (P' : Fin σ → Graph α β) (u' : Fin σ → S),
      IsHorn G (clearEnvelopeDrawing H (ys : Set S) Λ)
        (restrictCleared η (⋃ y ∈ (ys : Set S), Λ y)) d' v
        (θ - (4 * γ + 2) * ys.card) σ P' u' := by
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
    have hM' : HasTangleMetric H θ T d' := by
      simpa only [Nat.sub_zero, ← hT] using hc.hasMetric'
    have hEq := (tangleMetric_eq_of_hasTangleMetric hS inferInstance hc.hasMetric hM').1
    have hHorn' : IsHorn G H η d v θ σ P u := by
      simpa only [Finset.card_empty, Nat.add_zero] using hHorn
    refine ⟨P, u, ?_⟩
    have hTrans := horn_congr_drawing_embedding hDraw.symm η
      (restrictCleared η (⋃ y ∈ (↑(∅ : Finset S) : Set S), Λ y)) rfl rfl
      (fun x hx y hy => hEq {x} (Or.inl (Or.inl ⟨x, hx, rfl⟩))
        {y} (Or.inl (Or.inl ⟨y, hy, rfl⟩))) hHorn'
    simpa only [Finset.card_empty, Nat.mul_zero, Nat.sub_zero] using hTrans
  | @insert j ys hj ih =>
    let c := 4 * γ + 2
    obtain ⟨T₁, T₂, d₁, d₂, hClear, hRig₁, hEnv₁, hComp₂, hTot⟩ :=
      exists_compression_clearEnvelope_insert hS hj hComp.hasMetric hEnv hComp.lam_lt
    let H₁ := clearedSubdrawing H (Λ j)
    have hjmem : j ∈ insert j ys := Finset.mem_insert_self _ _
    have hZone := hEnv.2.1 j hjmem
    have hθj : c < θ := by
      have hleft := hComp₂.lam_lt
      omega
    have hSpan₁ : IsSigmaSpan G H₁ (restrictCleared η (Λ j)) θ_star (θ - c) T_star T₁ := by
      simpa only [c, Nat.sub_sub] using IsSigmaSpan.clear hSpan hClear hRig₁
    let e : Fin ((σ + ys.card) + 1) ≃ Fin (σ + (insert j ys).card) :=
      finCongr (by rw [Finset.card_insert_of_notMem hj]; omega)
    have hHorn₀ := horn_reindex e hHorn
    obtain ⟨P₁, u₁, hHorn₁⟩ := theorem_6_2_proof hS inferInstance G θ_star θ γ (σ + ys.card)
      T_star H η T T₁ d d₁ (Λ j) v (fun i => P (e i)) (fun i => u (e i))
      hSpan hComp.hasMetric hγ (by dsimp only [c] at hθj; omega)
      ⟨{j}, hZone.z_mem, hZone⟩ hRig₁ hClear hHorn₀
    have hHorn₁' : IsHorn G H₁ (restrictCleared η (Λ j)) d₁ v (θ - c) (σ + ys.card) P₁ u₁ := by
      simpa only [c, Nat.sub_sub] using hHorn₁
    obtain ⟨P₂, u₂, hHorn₂⟩ := ih (restrictCleared η (Λ j)) hSpan₁ hEnv₁ hComp₂ hHorn₁'
    have hDraw := clearEnvelopeDrawing_insert H ys j Λ
      (fun y hy => (hEnv.2.1 y hy).isOpenDisc.1)
    have hLoss : c + c * ys.card = c * (insert j ys).card := by
      rw [Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.mul_one, Nat.add_comm]
    have hT : T₂ = T' := compression_unique hS inferInstance hTot hComp
    have hM₂ : HasTangleMetric (clearEnvelopeDrawing H (↑(insert j ys)) Λ)
        (θ - c * (insert j ys).card) T' d₂ := by simpa only [hT] using hTot.hasMetric'
    have hEq := (tangleMetric_eq_of_hasTangleMetric hS inferInstance hM₂ hComp.hasMetric').1
    have hEqOld : ∀ x ∈ (clearEnvelopeDrawing H₁ (ys : Set S) Λ).V,
        ∀ y ∈ (clearEnvelopeDrawing H₁ (ys : Set S) Λ).V, d₂ {x} {y} = d' {x} {y} := by
      rw [hDraw]
      intro x hx y hy
      exact hEq {x} (Or.inl (Or.inl ⟨x, hx, rfl⟩)) {y} (Or.inl (Or.inl ⟨y, hy, rfl⟩))
    have hTransport := horn_congr_drawing_embedding hDraw
      (restrictCleared (restrictCleared η (Λ j)) (⋃ y ∈ (ys : Set S), Λ y))
      (restrictCleared η (⋃ y ∈ (↑(insert j ys) : Set S), Λ y)) rfl rfl hEqOld hHorn₂
    have hOrder : θ - c - c * ys.card = θ - c * (insert j ys).card := by
      rw [Nat.sub_sub, hLoss]
    rw [hOrder] at hTransport
    exact ⟨P₂, u₂, hTransport⟩

end GraphMinor.GM16
