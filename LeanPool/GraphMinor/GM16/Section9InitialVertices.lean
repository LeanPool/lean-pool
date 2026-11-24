/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM16.SpanMarkedSegments
import LeanPool.GraphMinor.GM16.ClearedPathVertices
import LeanPool.GraphMinor.GM16.Section9ShortPaths
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM16.MetricPoints
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Section88
import LeanPool.GraphMinor.GM09.Basic

/-!
# The second old vertex enters a cleared disc

Choose the next old drawing vertex along the bad path. Claim (7)
makes the initial segment short. This vertex cannot be the opposite
end because clearing does not increase distances, while the two new
ends are far apart. It therefore lies in a cleared disc. These are
the vertex choices used in XVI (8.1), Claims (7) and (8).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
variable {α : Type u} {βe : Type v}

/-- The next old vertex after a new-path end lies in a cleared
battlefield disc and is at old distance less than `ψ` from that end.
This includes the shortness and non-opposite-end steps of XVI (8.1),
Claims (7) and (8), pages 72–73. -/
theorem section9_initial_vertex_enters_disc (hS : IsClosedSurface S)
    {G P₀ : Graph α βe} {H : Drawing S} (η : SpanEmbedding H G)
    {θ β ψ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {Y : Set S}
    {Λ : S → Set S} {C : S → Drawing S} {X : S → Set S}
    (η' : SpanEmbedding (clearEnvelopeDrawing H Y Λ) G) (hMap : η'.vMap = η.vMap)
    (hMet : HasTangleMetric H θ T d)
    (hBattle : ∀ y ∈ Y, IsBattlefield H T d θ β {y} (Λ y) (C y) (X y))
    (hψ : 3 ≤ ψ) (hβ : ψ ≤ β)
    (hNoPath : ∀ Q s t, s ∈ H.V → t ∈ H.V →
      IsHPathWithEnds G η.imageGraph Q (η.vMap s) (η.vMap t) →
      ψ ≤ d {s} {t} → (∀ y ∈ Y, ψ ≤ d {s} {y}) → False)
    (hLe : ∀ x y : S, pointDist (clearEnvelopeDrawing H Y Λ) d' x y ≤ pointDist H d x y)
    {s₁ s₂ : S} (hs₁ : s₁ ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hs₂ : s₂ ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hP₀ : IsHPathWithEnds G η'.imageGraph P₀ (η.vMap s₁) (η.vMap s₂))
    (hLong : 2 * ψ ≤ d' {s₁} {s₂}) :
    ∃ t ∈ H.V, ∃ y ∈ Y, t ∈ Λ y ∧ d {s₁} {t} < ψ ∧ t ≠ s₁ ∧
      ∃ R : Graph α βe, R ≤ P₀ ∧ IsGraphPathWithEnds G R (η.vMap s₁) (η.vMap t) ∧
        V(R) ∩ V(η.imageGraph) = {η.vMap s₁, η.vMap t} := by
  have hClearSub : (clearEnvelopeDrawing H Y Λ).IsSubdrawing H := interSet_isSub
  have hs₁H := hClearSub.1 hs₁
  have hs₂H := hClearSub.1 hs₂
  have hst : s₁ ≠ s₂ := fun heq => hP₀.2.2.1 (congrArg η.vMap heq)
  obtain ⟨t, ht, hts, R, hRP, hR, hInter⟩ :=
    exists_initial_span_segment η hs₁H hs₂H hst hP₀.2.1
  have hZone := fun y hy => (hBattle y hy).isZone
  have hsOut : ∀ y ∈ Y, s₁ ∉ Λ y := by
    intro y hy
    have hout := (clearFamily_U hZone ▸ (clearEnvelopeDrawing H Y Λ).V_subset_U hs₁).2
    exact fun h => hout (mem_iUnion₂.mpr ⟨y, hy, h⟩)
  obtain ⟨_, _, _, hSymm, _, _⟩ := GM11.gm15_theorem_9_1 H θ T d hS inferInstance hMet
  have hShort := section9_initial_segment_short hS η hMet hSymm hBattle hψ hβ
    hNoPath hs₁H ht hsOut hR hts.symm hInter
  have htNotEnd : t ≠ s₂ := by
    intro heq
    have hdist := hLe s₁ s₂
    rw [pointDist_of_mem_vertices d' hs₁ hs₂, pointDist_of_mem_vertices d hs₁H hs₂H] at hdist
    rw [heq] at hShort
    omega
  have htPlace := old_vertex_place_on_cleared_path η η' hMap hs₁H hs₂H ht hP₀
    (hRP.vertexSet_mono hR.right_mem) hts
  have htIn : t ∈ ⋃ y ∈ Y, Λ y := htPlace.resolve_left htNotEnd
  obtain ⟨y, hy, hty⟩ := mem_iUnion₂.mp htIn
  exact ⟨t, ht, y, hy, hty, hShort, hts, R, hRP, hR, hInter⟩

end GraphMinor.GM16
