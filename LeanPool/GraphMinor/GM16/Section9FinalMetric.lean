/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM16.Section9LastVertexBounds
import LeanPool.GraphMinor.GM16.Section9ShortPaths
import LeanPool.GraphMinor.GM16.Section9Regions
import LeanPool.GraphMinor.GM16.SpanPaths
import LeanPool.GraphMinor.GM16.MetricPoints

/-!
# The final metric contradiction in XVI (8.1)

The last vertex before the path leaves the shell is far from all
battlefield centres. Its next old-drawing segment must therefore be
short. That segment cannot enter the inner zone, cross to another
battlefield, or reach the other end of the original path. These are
exactly the last cases on page 75.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The final contradiction following Claim (15) in XVI (8.1), page 75.
The inputs describe the consecutive old vertices chosen there, including
their positions relative to the clean annulus. The distance bounds of
Claim (15) and the shortness of their connecting segment are derived. -/
theorem section9_final_metric_contradiction (hS : IsClosedSurface S)
    {α : Type u} {βe : Type v} {G P : Graph α βe} {H : Drawing S} (η : SpanEmbedding H G)
    {θ γ i ψ sep : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {Y : Set S} {Λ : S → Set S} {Minner Mouter : Set S}
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
    {y s₁ s₂ t₁ u v : S} (hy : y ∈ Y)
    (hs₁ : s₁ ∈ H.V) (hs₂ : s₂ ∈ H.V) (ht₁ : t₁ ∈ H.V) (hu : u ∈ H.V) (hv : v ∈ H.V)
    (hs₁New : s₁ ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hs₂New : s₂ ∈ (clearEnvelopeDrawing H Y Λ).V)
    (hSep : ∀ z ∈ Y, y ≠ z → sep ≤ d {y} {z})
    (hInner : IsLambdaZoneAround H d (i + 2) {y} Minner)
    (hCapture : ∀ a ∈ H.A, d {y} a < i + ψ + 2 → a ⊆ Mouter)
    (huOut : u ∉ Mouter) (huCase : u = s₁ ∨ u ∈ Λ y)
    (hvShell : v ∉ Λ y \ Minner) (hvPlace : v = s₂ ∨ v ∈ ⋃ z ∈ Y, Λ z)
    (ht₁Λ : t₁ ∈ Λ y) (hShort₁ : d {s₁} {t₁} < ψ)
    (hLong : 2 * ψ ≤ d' {s₁} {s₂})
    (hP : IsGraphPathWithEnds G P (η.vMap u) (η.vMap v)) (huv : u ≠ v)
    (hInter : V(P) ∩ V(η.imageGraph) = {η.vMap u, η.vMap v}) : False := by
  have hyH := hY hy
  have hyA : ({y} : Set S) ∈ H.A := Or.inl (Or.inl ⟨y, hyH, rfl⟩)
  have huA : ({u} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hvA : ({v} : Set S) ∈ H.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  obtain ⟨hLower, hUpper⟩ := section9_last_vertex_bounds (hZone y hy) hyH hs₁ ht₁ hu
    hSymm hTri hCapture huOut ht₁Λ hShort₁ huCase
  have hFar := section9_last_vertex_far hY hy hu hTri hSymm hSep (by omega)
    (show ψ ≤ d {u} {y} by omega) hUpper
  have hShort : d {u} {v} < ψ := by
    by_contra hlong
    have hd : ψ ≤ d {u} {v} := by omega
    exact hNoPath P u v hu hv (isHPath_of_far_ends hS η hMet hu hv hP
      (fun he => huv (η.bijOn_v.injOn hu hv he)) hInter (hψ.trans hd)) hd hFar
  have hvNotInner : v ∉ Minner := by
    intro hvin
    have hdv := hInner.dist_le {v} hvA (singleton_subset_iff.mpr (subset_closure hvin))
    have hb := hTri {u} huA {v} hvA {y} hyA
    rw [hSymm {v} hvA {y} hyA] at hb
    omega
  have hvNotΛ : v ∉ Λ y := fun hvΛ => hvShell ⟨hvΛ, hvNotInner⟩
  rcases hvPlace with hvEnd | hvZones
  · subst v
    rcases huCase with huEnd | huΛ
    · have hb := hLe s₁ s₂
      rw [pointDist_of_mem_vertices d hs₁ hs₂,
        pointDist_of_mem_vertices d' hs₁New hs₂New] at hb
      rw [huEnd] at hShort
      omega
    · have hShort₂ : d {s₂} {u} < ψ := by
        rw [hSymm {s₂} hvA {u} huA]
        exact hShort
      exact section9_distinct_entered_regions hs₁ hs₂ ht₁ hu hs₁New hs₂New
        (zone_mem_R_clearFamily hZone hdis hy) ht₁Λ huΛ hLe hNewTri hNewSymm hShort₁ hShort₂ hLong
  · obtain ⟨z, hz, hvΛz⟩ := mem_iUnion₂.mp hvZones
    have hyz : y ≠ z := fun he => hvNotΛ (he.symm ▸ hvΛz)
    have hzA : ({z} : Set S) ∈ H.A := Or.inl (Or.inl ⟨z, hY hz, rfl⟩)
    have hvz := (hZone z hz).dist_le {v} hvA (singleton_subset_iff.mpr (subset_closure hvΛz))
    have hb₁ := hTri {y} hyA {u} huA {z} hzA
    have hb₂ := hTri {u} huA {v} hvA {z} hzA
    rw [hSymm {y} hyA {u} huA] at hb₁
    rw [hSymm {v} hvA {z} hzA] at hb₂
    have hsep := hSep z hz hyz
    omega

end GraphMinor.GM16
