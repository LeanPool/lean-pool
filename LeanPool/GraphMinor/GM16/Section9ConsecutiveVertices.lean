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
import LeanPool.GraphMinor.GM16.Section9FinalMetric
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section88

/-!
# Choosing the consecutive vertices for the final contradiction

Stop the bad path at its first old vertex outside the shell and
trim backwards to the preceding old vertex. The clean annulus is
disjoint from the path, so that preceding vertex lies outside the
outer zone. The two vertices therefore satisfy the hypotheses of
the metric contradiction after Claim (15) of XVI (8.1).
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
  GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
variable {α : Type u} {βe : Type v}

/-- The vertex choice and final contradiction of XVI (8.1), pages
74–75, after the bad path is known to miss the clean annulus. -/
theorem section9_contradiction_of_clean_annulus (hS : IsClosedSurface S)
    {G P₀ : Graph α βe} {H : Drawing S} (η : SpanEmbedding H G)
    {θ γ i ψ sep : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {Y : Set S} {Λ : S → Set S} {I O : Set S}
    (η' : SpanEmbedding (clearEnvelopeDrawing H Y Λ) G) (hMap : η'.vMap = η.vMap)
    (hMet : HasTangleMetric H θ T d) (hY : Y ⊆ H.V)
    (hZone : ∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y))
    (hdis : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → Disjoint (closure (Λ y)) (closure (Λ z)))
    (hSymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hTri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (hNewSymm : ∀ a ∈ (clearEnvelopeDrawing H Y Λ).A,
      ∀ b ∈ (clearEnvelopeDrawing H Y Λ).A, d' a b = d' b a)
    (hNewTri : ∀ a ∈ (clearEnvelopeDrawing H Y Λ).A,
      ∀ b ∈ (clearEnvelopeDrawing H Y Λ).A, ∀ c ∈ (clearEnvelopeDrawing H Y Λ).A,
      d' a c ≤ d' a b + d' b c)
    (hLe : ∀ x y : S, pointDist (clearEnvelopeDrawing H Y Λ) d' x y ≤ pointDist H d x y)
    (hNoPath : ∀ Q s t, s ∈ H.V → t ∈ H.V →
      IsHPathWithEnds G η.imageGraph Q (η.vMap s) (η.vMap t) →
      ψ ≤ d {s} {t} → (∀ y ∈ Y, ψ ≤ d {s} {y}) → False)
    (hψ : 3 ≤ ψ) (hSepBudget : 2 * γ + 2 * ψ < sep)
    {y s₁ s₂ t₁ : S} (hy : y ∈ Y) (ht₁ : t₁ ∈ H.V)
    (hs₁ : s₁ ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hs₂ : s₂ ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hP₀ : IsHPathWithEnds G η'.imageGraph P₀ (η.vMap s₁) (η.vMap s₂))
    (hSep : ∀ z ∈ Y, y ≠ z → sep ≤ d {y} {z})
    (hI : IsLambdaZoneAround H d (i + 2) {y} I)
    (hNest : closure I ⊆ O) (hOuter : closure O ⊆ Λ y)
    (hCapture : ∀ a ∈ H.A, d {y} a < i + ψ + 2 → a ⊆ O)
    (hMiss : Disjoint V(P₀) (η.vMap '' (H.interSet (closure O \ I)).V))
    (ht₁Λ : t₁ ∈ Λ y) (hShort₁ : d {s₁} {t₁} < ψ)
    (hLong : 2 * ψ ≤ d' {s₁} {s₂}) : False := by
  have hClearSub : (clearEnvelopeDrawing H Y Λ).IsSubdrawing H := interSet_isSub
  have hs₁H := hClearSub.1 hs₁
  have hs₂H := hClearSub.1 hs₂
  have hs₁Out : s₁ ∉ Λ y := by
    have hout := (clearFamily_U hZone ▸ (clearEnvelopeDrawing H Y Λ).V_subset_U hs₁).2
    exact fun h => hout (mem_iUnion₂.mpr ⟨y, hy, h⟩)
  have hs₂Out : s₂ ∉ Λ y := by
    have hout := (clearFamily_U hZone ▸ (clearEnvelopeDrawing H Y Λ).V_subset_U hs₂).2
    exact fun h => hout (mem_iUnion₂.mpr ⟨y, hy, h⟩)
  have hst : s₁ ≠ s₂ := fun heq => hP₀.2.2.1 (congrArg η.vMap heq)
  obtain ⟨u, hu, v, hv, huv, hvs, hvShell, huCase, R, hRP, hR, hInter⟩ :=
    exists_consecutive_span_exit η hs₁H hs₂H hst
      (show s₂ ∉ Λ y \ I from fun h => hs₂Out h.1) hP₀.2.1
  have huI : u ∉ I := by
    rcases huCase with hueq | huShell
    · subst u
      exact fun h => hs₁Out (hOuter (subset_closure (hNest (subset_closure h))))
    · exact huShell.2
  have huO : u ∉ O := by
    intro huo
    have huJ : u ∈ (H.interSet (closure O \ I)).V :=
      (mem_interSet_V_iff (isClosed_closure.sdiff hI.isOpenDisc.1)).mpr
        ⟨hu, subset_closure huo, huI⟩
    exact hMiss.notMem_of_mem_left (hRP.vertexSet_mono hR.left_mem)
      (mem_image_of_mem η.vMap huJ)
  have huCase' : u = s₁ ∨ u ∈ Λ y := huCase.imp id And.left
  have hvPlace : v = s₂ ∨ v ∈ ⋃ z ∈ Y, Λ z := old_vertex_place_on_cleared_path
    η η' hMap hs₁H hs₂H hv hP₀ (hRP.vertexSet_mono hR.right_mem) hvs
  exact section9_final_metric_contradiction hS η hMet hY hZone hdis hSymm hTri
    hNewSymm hNewTri hLe hNoPath hψ hSepBudget hy hs₁H hs₂H ht₁ hu hv hs₁ hs₂
    hSep hI hCapture huO huCase' hvShell hvPlace ht₁Λ hShort₁ hLong hR huv hInter

end GraphMinor.GM16
