/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6

/-!
# Adding the new horn in XVI (6.3)

A fan outside the old drawing gives a horn at a vertex outside the old
horn set. Add that vertex and drop the hairs. The old horns keep the
required strength by monotonicity, and the horn count increases by one.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Adding a new horn outside the old horn set gives the first outcome
in XVI (6.3), page 60. Existing hairs may be dropped. -/
theorem IsAnimal.add_horn
    {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u} {β : Type v}
    {G : Graph α β} {H : Drawing S} {η : SpanEmbedding H G}
    {θ_star θ_span χ δ θ σ ψ τ : ℕ}
    {T_star : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {X : Set α} {Y : Set S}
    (h : IsAnimal G T_star θ_star H η θ_span T d X Y χ δ θ σ)
    (hψ : 1 ≤ ψ) (hψθ : ψ ≤ θ) (hτσ : τ ≤ σ)
    {v : α} (hvX : v ∉ X)
    (hnew : ∃ (P : Fin τ → Graph α β) (ends : Fin τ → S), IsHorn G H η d v ψ τ P ends) :
    HasHairlessAnimal S G T_star θ_star (χ + 1) ψ τ := by
  obtain ⟨_, hθorder, hSpan, hMet, hXsub, hXcard, _, _, hHorns, _, _⟩ := h
  obtain ⟨P, ends, hnew⟩ := hnew
  have hXfin : X.Finite := hSpan.isControlling.isTangle_star.finite_V.subset
    (fun x hx => (hXsub hx).1)
  refine ⟨H, η, θ_span, T, d, insert v X, ∅, hψ, hψθ.trans hθorder,
    hSpan, hMet, ?_, ?_, empty_subset _, ncard_empty S, ?_, ?_, ?_⟩
  · rintro x (rfl | hx)
    · exact hnew.1
    · exact hXsub hx
  · rw [ncard_insert_of_notMem hvX hXfin, hXcard]
  · rintro x (rfl | hx)
    · exact ⟨P, ends, hnew⟩
    · obtain ⟨Q, u, hQ⟩ := hHorns x hx
      exact ⟨_, _, hQ.mono hψθ hτσ⟩
  · intro x hx
    exact False.elim hx
  · intro x hx
    exact False.elim hx

end GraphMinor.GM16
