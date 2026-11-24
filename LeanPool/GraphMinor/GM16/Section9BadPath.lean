/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM16.Section9Claim11
import LeanPool.GraphMinor.GM16.Section9AnnularAttachment
import LeanPool.GraphMinor.GM16.Section9ConsecutiveVertices
import LeanPool.GraphMinor.GM16.Section9Annuli
import LeanPool.GraphMinor.GM16.Section9NestedZones
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM16.SpanVertexPullback
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM14.Section3

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM14.Section9a

/-!
# Excluding the bad path after the attachment choice

Choose the nested zones and a separator-free annulus. Claim (11)
gives a clean path crossing that annulus. If the bad path met the
annulus, their union would give a forbidden attachment. The bad path
therefore misses the annulus, and the consecutive-vertex argument
finishes the metric contradiction. This assembles Claims (10)–(15)
of XVI (8.1) from their geometric data and the attachment case.
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
  GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
variable {α : Type u} {βe : Type v}

/-- The contradiction in the last part of XVI (8.1), pages 73–75,
after choosing a battlefield with no clean attachment to the bad
path. The clean annulus, its exclusion, and its consecutive vertices
are derived within the proof. -/
theorem section9_bad_path_contradiction
    (hS : IsClosedSurface S) {G P₀ : Graph α βe} {H : Drawing S}
    (η : SpanEmbedding H G) {θ θ' β κ ψ sep : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {Y : Set S}
    {Λ : S → Set S} {C : S → Drawing S} {X : S → Set S}
    (η' : SpanEmbedding (clearEnvelopeDrawing H Y Λ) G) (hMap : η'.vMap = η.vMap)
    (hMet : HasTangleMetric H θ T d)
    (hNewMet : HasTangleMetric (clearEnvelopeDrawing H Y Λ) θ' T' d')
    (hY : Y ⊆ H.V)
    (hBattle : ∀ y ∈ Y, IsBattlefield H T d θ β {y} (Λ y) (C y) (X y))
    (hSep : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → sep ≤ d {y} {z})
    (hLe : ∀ x y : S, pointDist (clearEnvelopeDrawing H Y Λ) d' x y ≤ pointDist H d x y)
    (hNoPath : ∀ Q s t, s ∈ H.V → t ∈ H.V →
      IsHPathWithEnds G η.imageGraph Q (η.vMap s) (η.vMap t) →
      ψ ≤ d {s} {t} → (∀ y ∈ Y, ψ ≤ d {s} {y}) → False)
    (hκ : 3 ≤ κ) (hψ : 3 ≤ ψ) (hβ : κ + 3 ≤ β) (hβθ : β < θ)
    (hθ : κ + (3 * β + 3) < θ) (hSepBudget : 2 * (3 * β + 3) + 2 * ψ < sep)
    (hMax : κ + (κ - 1) * (ψ + 5) ≤ β - ψ - 5)
    {Z : Set α} (hZ : Z.Finite) (hCard : Z.ncard < κ)
    {y s₁ s₂ t₁ : S} (hy : y ∈ Y) (ht₁ : t₁ ∈ H.V)
    (hs₁ : s₁ ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hs₂ : s₂ ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hP₀ : IsHPathWithEnds G η'.imageGraph P₀ (η.vMap s₁) (η.vMap s₂))
    (ht₁Λ : t₁ ∈ Λ y) (hShort₁ : d {s₁} {t₁} < ψ)
    (hLong : 2 * ψ ≤ d' {s₁} {s₂})
    (hNoAttach : ∀ b ∈ X y, ∀ c ∈ V(P₀), ∀ R : Graph α βe,
      IsGraphPathWithEnds G R (η.vMap b) c →
      V(R) ∩ V(η'.imageGraph) ⊆ η.vMap '' X y → Disjoint V(R) Z → False) : False := by
  classical
  have hZone := fun z hz => (hBattle z hz).isZone
  obtain ⟨_, _, _, hSymm, hTri, _⟩ := GM11.gm15_theorem_9_1 H θ T d hS inferInstance hMet
  obtain ⟨_, _, _, hNewSymm, hNewTri, _⟩ := GM11.gm15_theorem_9_1
    (clearEnvelopeDrawing H Y Λ) θ' T' d' hS inferInstance hNewMet
  have hFar : ∀ z ∈ Y, ∀ w ∈ Y, z ≠ w → 2 * (3 * β + 3) < d {z} {w} := by
    intro z hz w hw hzw
    exact lt_of_lt_of_le (by omega) (hSep z hz w hw hzw)
  have hdis : ∀ z ∈ Y, ∀ w ∈ Y, z ≠ w →
      Disjoint (closure (Λ z)) (closure (Λ w)) := by
    intro z hz w hw hzw
    exact section9_disjoint_zones (hZone z hz) (hZone w hw) hSymm hTri
      (Nat.le_refl _) (hFar z hz w hw hzw)
  obtain ⟨M, hM⟩ := section9_exists_nested_zones hS (hY hy) hMet hβθ
  have hκβ : κ ≤ β - 3 := by omega
  let ZS := H.V ∩ η.vMap ⁻¹' Z
  obtain ⟨hZS, hZSCard⟩ := span_vertex_pullback_card η hZ
  have hZSκ : ZS.ncard < κ := lt_of_le_of_lt hZSCard hCard
  obtain ⟨r, hClean⟩ := section9_exists_clean_annulus hκ hψ hMax hM ZS hZS hZSκ
  let i := κ + r.val * (ψ + 5)
  have hr : r.val ≤ κ - 1 := by omega
  have hMul := Nat.mul_le_mul_right (ψ + 5) hr
  have hi : 3 ≤ i := by dsimp [i]; omega
  have hij : i + ψ + 2 ≤ β - 3 := by dsimp [i]; omega
  have hiβ : i ≤ β - 3 := by omega
  have hI := (hM i hi hiβ).1
  have hO := (hM (i + ψ + 2) (by omega) hij).1
  have hNest : closure (M i) ⊆ M (i + ψ + 2) :=
    section9_nested_closures hI (hM (i + ψ + 2) (by omega) hij).2 (by omega)
  have hκNest : closure (M κ) ⊆ M (i + ψ + 2) :=
    section9_nested_closures (hM κ hκ hκβ).1
      (hM (i + ψ + 2) (by omega) hij).2 (by dsimp [i]; omega)
  have hOuter : closure (M (i + ψ + 2)) ⊆ Λ y :=
    section9_zone_inside_battlefield (hBattle y hy) hO (by omega)
  obtain ⟨b, hb, a, ha, P, hPPath, hPH, hPClear, hPZ⟩ := theorem_8_1_claim_11 hS hMet hY hy hBattle
    hFar (hM κ hκ hκβ).1 (hM κ hκ hκβ).2
    hκ hβ hθ hZS hZSκ
  have haO : a ∈ M (i + ψ + 2) := hκNest ha.2.1
  have hbO : b ∉ M (i + ψ + 2) := by
    intro hbo
    exact ((isOpen_disjoint_subBd_and_closure_eq (hZone y hy).isOpenDisc.1).1).notMem_of_mem_left
      (hOuter (subset_closure hbo)) ((hBattle y hy).isFree_X.1 hb).2
  have hMiss : Disjoint V(P₀) (η.vMap '' (H.interSet
      (closure (M (i + ψ + 2)) \ M i)).V) := by
    apply disjoint_left.mpr
    intro x hxP₀ hxJ
    have hHit : (V(P₀) ∩ (η.vMap '' (H.interSet
        (closure (M (i + ψ + 2)) \ M i)).V)).Nonempty := ⟨x, hxP₀, hxJ⟩
    obtain ⟨c, hc, R, hR, hRClear, hRZ⟩ := section9_annular_intersection_gives_attachment
      hS η hMet hZone hy η' hMap hI hO hNest hOuter hPH hPPath hb haO hbO hPClear hPZ hClean hHit
    exact hNoAttach b hb c hc R hR hRClear hRZ
  exact section9_contradiction_of_clean_annulus hS η η' hMap hMet hY hZone hdis
    hSymm hTri hNewSymm hNewTri hLe hNoPath hψ hSepBudget hy ht₁ hs₁ hs₂ hP₀
    (fun z hz hyz => hSep y hy z hz hyz) hI hNest hOuter
    (hM (i + ψ + 2) (by omega) hij).2 hMiss ht₁Λ hShort₁ hLong

end GraphMinor.GM16
