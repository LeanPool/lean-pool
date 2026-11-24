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
    have hθ : c * (ys.card + 1) < θ := by
      simpa only [Finset.card_insert_of_notMem hj] using hComp.lam_lt
    have hθj : c < θ := by
      have h := Nat.mul_le_mul_left c (show 1 ≤ ys.card + 1 by omega)
      omega
    have hEnvInsert : IsEnvelope H d (insert j (ys : Set S)) γ Λ := by
      simpa only [Finset.coe_insert] using hEnv
    have hjmem : j ∈ insert j (ys : Set S) := mem_insert _ _
    have hZone := hEnvInsert.2.1 j hjmem
    obtain ⟨T₁, d₁, hClear, _⟩ := GM14.theorem_3_2_proof hS inferInstance
      (by dsimp only [c] at hθj; omega) hComp.hasMetric hZone
    let H₁ := clearedSubdrawing H (Λ j)
    have hRig₁ : IsRigid H₁ := by
      have h := hEnvInsert.2.2.2 {j} (singleton_subset_iff.mpr hjmem)
      have hu : (⋃ y ∈ ({j} : Set S), Λ y) = Λ j := by simp
      rw [hu] at h
      exact h
    have hSpan₁ : IsSigmaSpan G H₁ (restrictCleared η (Λ j)) θ_star (θ - c) T_star T₁ := by
      simpa only [c, Nat.sub_sub] using IsSigmaSpan.clear hSpan hClear hRig₁
    have hEnv₁ := envelope_after_clearing (show j ∉ (ys : Set S) from hj) hEnvInsert hClear
    let e : Fin ((σ + ys.card) + 1) ≃ Fin (σ + (insert j ys).card) :=
      finCongr (by rw [Finset.card_insert_of_notMem hj]; omega)
    have hHorn₀ := horn_reindex e hHorn
    obtain ⟨P₁, u₁, hHorn₁⟩ := theorem_6_2_proof hS inferInstance G θ_star θ γ (σ + ys.card)
      T_star H η T T₁ d d₁ (Λ j) v (fun i => P (e i)) (fun i => u (e i))
      hSpan hComp.hasMetric hγ (by dsimp only [c] at hθj; omega)
      ⟨{j}, hZone.z_mem, hZone⟩ hRig₁ hClear hHorn₀
    have hθrem : c * ys.card < θ - c := by
      rw [Nat.mul_add, Nat.mul_one] at hθ
      omega
    obtain ⟨T₂, d₂, hComp₂, _⟩ := exists_compression_clearFamily hS ys Λ γ
      (show HasTangleMetric H₁ (θ - c) T₁ d₁ by simpa only [c, Nat.sub_sub] using hClear.hasMetric)
      (fun y hy => hEnv₁.1 hy) hEnv₁.2.1 hEnv₁.2.2.1 hθrem
    have hHorn₁' : IsHorn G H₁ (restrictCleared η (Λ j)) d₁ v (θ - c) (σ + ys.card) P₁ u₁ := by
      simpa only [c, Nat.sub_sub] using hHorn₁
    obtain ⟨P₂, u₂, hHorn₂⟩ := ih (restrictCleared η (Λ j)) hSpan₁ hEnv₁ hComp₂ hHorn₁'
    have hSet : insert j (ys : Set S) = (↑(insert j ys) : Set S) := by simp
    have hDraw : clearEnvelopeDrawing H₁ (ys : Set S) Λ =
        clearEnvelopeDrawing H (↑(insert j ys)) Λ := by
      rw [show H₁ = clearedSubdrawing H (Λ j) from rfl,
        clearFamily_after_single H (ys : Set S) Λ j (fun y hy => (hEnvInsert.2.1 y
          hy).isOpenDisc.1), hSet]
    have hTot := compression_comp (compression_of_clearing hComp.hasMetric hθj hClear) hComp₂
    rw [hDraw] at hTot
    have hLoss : c + c * ys.card = c * (insert j ys).card := by
      rw [Finset.card_insert_of_notMem hj, Nat.mul_add, Nat.mul_one, Nat.add_comm]
    rw [hLoss] at hTot
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
