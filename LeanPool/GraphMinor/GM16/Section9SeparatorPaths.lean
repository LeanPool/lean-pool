/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Cited
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM16.Section9BadPath
import LeanPool.GraphMinor.GM16.Section9InitialVertices
import LeanPool.GraphMinor.GM16.Section9Claim9
import LeanPool.GraphMinor.GM16.Section9ShortPaths
import LeanPool.GraphMinor.GM16.Section9BoundaryVertices
import LeanPool.GraphMinor.GM16.Section9Regions
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM09.Basic
import Mathlib.Tactic.Linarith
import LeanPool.GraphMinor.GM11.Section88

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM14.Section9a

/-!
# The global separator meets every long new path

If a long path avoided the part of the separator outside the cleared
drawing, its separator vertices would be only its ends. Its first
old vertices enter distinct battlefield discs by Claims (7) and (8).
Claim (9) chooses one side with no clean attachment. The clean-annulus
argument on that side then gives the final contradiction. This
assembles the path conclusion of XVI (8.1).
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
  GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
variable {α : Type u} {βe : Type v}

private theorem hPath_symm {G H P : Graph α βe} {a b : α}
    (h : IsHPathWithEnds G H P a b) : IsHPathWithEnds G H P b a :=
  ⟨h.1, h.2.1.symm, h.2.2.1.symm, h.2.2.2.2.1, h.2.2.2.1,
    h.2.2.2.2.2.1.trans (Set.pair_comm _ _), h.2.2.2.2.2.2⟩

/-- The path conclusion of XVI (8.1), Section 9, pages 72–75, for
a global boundary-path separator. All claims about the bad path,
including the attachment choice and final contradiction, are proved. -/
theorem section9_long_new_path_meets_separator
    (hS : IsClosedSurface S) {G P₀ : Graph α βe} {H : Drawing S}
    (η : SpanEmbedding H G) {θ θ' β κ φ ψ sep : ℕ}
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
    (hκEq : κ = Y.ncard ^ 2 * φ ^ 2 / 2 + 1) (hφ : 3 ≤ φ) (hψ : 3 ≤ ψ) (hψβ : ψ ≤ β) (hβ : κ + 3
      ≤ β) (hβθ : β < θ)
    (hθ : κ + (3 * β + 3) < θ) (hSepBudget : 2 * (3 * β + 3) + 2 * ψ < sep)
    (hMax : κ + (κ - 1) * (ψ + 5) ≤ β - ψ - 5)
    {Z : Set α} (hZ : Z.Finite) (hCard : Z.ncard < κ)
    (hCut : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → ∀ Q a b,
      IsHPathWithEnds G η'.imageGraph Q a b →
      a ∈ η.vMap '' X y → b ∈ η.vMap '' X z → (V(Q) ∩ Z).Nonempty)
    {s₁ s₂ : S} (hs₁ : s₁ ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hs₂ : s₂ ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hP₀ : IsHPathWithEnds G η'.imageGraph P₀ (η.vMap s₁) (η.vMap s₂))
    (hLong : 2 * ψ ≤ d' {s₁} {s₂}) : ((Z \ V(η'.imageGraph)) ∩ V(P₀)).Nonempty := by
  classical
  by_contra hAvoid
  have hPZ : V(P₀) ∩ Z ⊆ {η.vMap s₁, η.vMap s₂} := by
    rintro x ⟨hxP, hxZ⟩
    have hxH : x ∈ V(η'.imageGraph) := by
      by_contra hxNot
      exact hAvoid ⟨x, ⟨hxZ, hxNot⟩, hxP⟩
    exact hP₀.2.2.2.2.2.1 ▸ ⟨hxP, hxH⟩
  obtain ⟨_, _, _, hSymm, hTri, _⟩ := GM11.gm15_theorem_9_1 H θ T d hS inferInstance hMet
  obtain ⟨_, _, _, hNewSymm, hNewTri, _⟩ := GM11.gm15_theorem_9_1
    (clearEnvelopeDrawing H Y Λ) θ' T' d' hS inferInstance hNewMet
  have hZone := fun y hy => (hBattle y hy).isZone
  have hdis : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z →
      Disjoint (closure (Λ y)) (closure (Λ z)) := by
    intro y hy z hz hyz
    exact section9_disjoint_zones (hZone y hy) (hZone z hz) hSymm hTri
      (hSep y hy z hz hyz) (by omega)
  obtain ⟨t₁, ht₁, y₁, hy₁, ht₁Λ, hShort₁, _, _⟩ := section9_initial_vertex_enters_disc
    hS η η' hMap hMet hBattle hψ hψβ hNoPath hLe hs₁ hs₂ hP₀ hLong
  have hδ : 1 ≤ Y.ncard := (ncard_pos (H.finite_V.subset hY)).mpr ⟨y₁, hy₁⟩
  have hδsq : 1 ≤ Y.ncard ^ 2 := by nlinarith
  have hφsq : 9 ≤ φ ^ 2 := by nlinarith
  have hProd : 9 ≤ Y.ncard ^ 2 * φ ^ 2 :=
    hφsq.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (φ ^ 2) hδsq)
  have hκ : 3 ≤ κ := by rw [hκEq]; omega
  have hP₀rev := hPath_symm hP₀
  have hLongrev : 2 * ψ ≤ d' {s₂} {s₁} := by
    rw [hNewSymm {s₂} (Or.inl (Or.inl ⟨s₂, hs₂, rfl⟩))
      {s₁} (Or.inl (Or.inl ⟨s₁, hs₁, rfl⟩))]
    exact hLong
  obtain ⟨t₂, ht₂, y₂, hy₂, ht₂Λ, hShort₂, _, _⟩ := section9_initial_vertex_enters_disc
    hS η η' hMap hMet hBattle hψ hψβ hNoPath hLe hs₂ hs₁ hP₀rev hLongrev
  have hClearSub : (clearEnvelopeDrawing H Y Λ).IsSubdrawing H := interSet_isSub
  have hyNe : y₁ ≠ y₂ := by
    intro heq
    subst y₂
    exact section9_distinct_entered_regions (hClearSub.1 hs₁) (hClearSub.1 hs₂)
      ht₁ ht₂ hs₁ hs₂ (zone_mem_R_clearFamily hZone hdis hy₁) ht₁Λ ht₂Λ
      hLe hNewTri hNewSymm hShort₁ hShort₂ hLong
  have hXsub : ∀ y ∈ Y, η.vMap '' X y ⊆ V(η'.imageGraph) := by
    intro y hy x hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [← hMap]
    exact η'.bijOn_v.mapsTo (boundary_vertex_mem_clearFamily hZone hdis hy
      ((hBattle y hy).isFree_X.1 hv))
  have hXdis : Disjoint (η.vMap '' X y₁) (η.vMap '' X y₂) :=
    battlefield_image_sets_disjoint η (hBattle y₁ hy₁) (hBattle y₂ hy₂) (hdis y₁ hy₁ y₂ hy₂ hyNe)
  let Attach (y : S) : Prop := ∃ a ∈ η.vMap '' X y, ∃ c ∈ V(P₀), ∃ Q : Graph α βe,
    IsGraphPathWithEnds G Q a c ∧ V(Q) ∩ V(η'.imageGraph) ⊆ η.vMap '' X y ∧ Disjoint V(Q) Z
  by_cases hA₁ : Attach y₁
  · by_cases hA₂ : Attach y₂
    · obtain ⟨a, ha, x, hx, Q₁, hQ₁, hQ₁H, hQ₁Z⟩ := hA₁
      obtain ⟨b, hb, z, hz, Q₂, hQ₂, hQ₂H, hQ₂Z⟩ := hA₂
      exact section9_no_two_clean_attachments η'.imageGraph_le (hXsub y₁ hy₁) (hXsub y₂ hy₂)
        hXdis hP₀ hPZ (hCut y₁ hy₁ y₂ hy₂ hyNe) hQ₁ ha hx hQ₁H hQ₁Z hQ₂ hb hz hQ₂H hQ₂Z
    · apply section9_bad_path_contradiction hS η η' hMap hMet hNewMet hY hBattle
        hSep hLe hNoPath hκ hψ hβ hβθ hθ hSepBudget hMax hZ hCard hy₂ ht₂ hs₂ hs₁
        hP₀rev ht₂Λ hShort₂ hLongrev
      intro b hb c hc R hR hRClear hRZ
      exact hA₂ ⟨η.vMap b, mem_image_of_mem _ hb, c, hc, R, hR, hRClear, hRZ⟩
  · apply section9_bad_path_contradiction hS η η' hMap hMet hNewMet hY hBattle
      hSep hLe hNoPath hκ hψ hβ hβθ hθ hSepBudget hMax hZ hCard hy₁ ht₁ hs₁ hs₂
      hP₀ ht₁Λ hShort₁ hLong
    intro b hb c hc R hR hRClear hRZ
    exact hA₁ ⟨η.vMap b, mem_image_of_mem _ hb, c, hc, R, hR, hRClear, hRZ⟩

end GraphMinor.GM16
