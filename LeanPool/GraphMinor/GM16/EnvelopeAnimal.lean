/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM16.EnvelopeHorns
import LeanPool.GraphMinor.GM16.EnvelopeHairEnds
import LeanPool.GraphMinor.GM16.EnvelopeHair
import LeanPool.GraphMinor.GM16.Section9SpanClearing
import LeanPool.GraphMinor.GM16.Section5

import LeanPool.GraphMinor.GM11.CitedResults

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

/-!
# The animal after clearing its envelope

Apply the repeated-clearing lemma to every horn. Move each near hair
end to its envelope boundary and extend the far end to the cleared
drawing. The new ends are distinct and separated, and each new hair
still avoids the horn centres. This assembles Claims (4)–(6) in the
proof of XVI (7.1), pages 69–70.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
variable {α : Type u} {β : Type v}

/-- Clearing the envelope produces the animal used for the second
application of (8.3) in XVI (7.1), with all horns and hairs proved. -/
theorem animal_after_clearFamily
     (hS : IsClosedSurface S)
    (ys : Finset S) (Λ : S → Set S) {γ σ θ θ₂ χ θ_star : ℕ} (hγ : 2 ≤ γ)
    {G : Graph α β} {H : Drawing S} (η : SpanEmbedding H G)
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {X : Set α}
    (hAnim : IsAnimal G T_star θ_star H η θ T d X (ys : Set S)
      χ ys.card θ (σ + ys.card))
    (hEnv : IsEnvelope H d (ys : Set S) γ Λ)
    (hComp : IsLambdaCompression H (clearEnvelopeDrawing H (ys : Set S) Λ)
      θ ((4 * γ + 2) * ys.card) T T' d d')
    (hθ₂ : 1 ≤ θ₂) (hBudget : θ₂ + 3 * γ + (4 * γ + 2) * ys.card ≤ θ) :
    ∃ Y' : Set S, IsAnimal G T_star θ_star
      (clearEnvelopeDrawing H (ys : Set S) Λ)
      (restrictCleared η (⋃ y ∈ (ys : Set S), Λ y))
      (θ - (4 * γ + 2) * ys.card) T' d' X Y' χ ys.card θ₂ σ := by
  classical
  obtain ⟨_, _, hSpan, hMet, hX, hXcard, hY, _, hHorns, hHairs, hSep⟩ := hAnim
  have hSpan' := span_after_clearFamily hS ys Λ γ η hSpan hEnv hComp
  obtain ⟨p, P, hNear, hInj, hDist⟩ := exists_envelope_hair_ends (θ₂ := θ₂) hS hEnv hComp hSep
    (by omega)
  let Y' := range p
  have hY' : Y' ⊆ (clearEnvelopeDrawing H (ys : Set S) Λ).V := by
    rintro x ⟨y, rfl⟩
    exact (hNear y).1
  have hCard : Y'.ncard = ys.card := by
    rw [show Y' = range p from rfl, ncard_range_of_injective hInj, Nat.card_coe_set_eq,
      ncard_coe_finset]
  have hOrder : θ₂ ≤ θ - (4 * γ + 2) * ys.card := by omega
  refine ⟨Y', hθ₂, hOrder, hSpan', hComp.hasMetric', ?_, hXcard, hY', hCard, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(hX hx).1, fun hxNew => (hX hx).2
      ((restrictCleared_imageGraph_le η (⋃ y ∈ (ys : Set S), Λ y)).vertexSet_mono hxNew)⟩
  · intro x hx
    obtain ⟨Q, q, hHorn⟩ := hHorns x hx
    obtain ⟨Q', q', hHorn'⟩ := horn_after_clearFamily hS ys Λ γ σ hγ η
      hSpan hEnv hComp hHorn
    exact ⟨_, _, hHorn'.mono hOrder le_rfl⟩
  · rintro x ⟨y, rfl⟩
    obtain ⟨hp, _, hPath, hPH, _, hInter, hNearDist⟩ := hNear y
    obtain ⟨r, Q, hr, _, hQ, hQX, hFar⟩ := hHairs y.val y.prop
    obtain ⟨q, hq, R, hpq, hR, hRX, hFar'⟩ := exists_hair_after_envelope hS η hEnv hComp
      hX hθ₂ hBudget y.prop hr hp hPH hPath hInter hNearDist hQ hQX hFar
    exact ⟨q, R, hq, hpq, hR, hRX, hFar'⟩
  · rintro x ⟨y, rfl⟩ z ⟨w, rfl⟩ hyw
    exact hDist (fun h => hyw (congrArg p h))

end GraphMinor.GM16
