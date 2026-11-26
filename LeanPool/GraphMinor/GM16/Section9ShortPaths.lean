/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM16.SpanPaths
import LeanPool.GraphMinor.GM16.MetricPoints
import LeanPool.GraphMinor.GM15.Section4

/-!
# The short initial segments in XVI (8.1)

Claim (7), page 72, considers the segment from an end of the new path
to its next vertex in the old drawing. A point outside a battlefield
is far from its centre. If the segment had long ends, it would be a
forbidden old-drawing path. The only other case is a single drawing
edge, whose ends have distance at most two.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- Outside a battlefield disc, a vertex is at least the battlefield
size away from its centre, by clause (v) of XIV's definition. -/
theorem battlefield_dist_ge_of_notMem {H : Drawing S}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ β : ℕ} {z Λ X : Set S} {C : Drawing S}
    (h : IsBattlefield H T d θ β z Λ C X) {s : S} (hs : s ∈ H.V) (hsΛ : s ∉ Λ) :
    β ≤ d z {s} := by
  by_contra hlt
  obtain ⟨Δ, _, hΔΛ, _, hsmall⟩ := h.openDisc_includes
  exact hsΛ (hΔΛ (hsmall {s} (Or.inl (Or.inl ⟨s, hs, rfl⟩)) (by omega) (mem_singleton s)))

/-- The metric conclusion of XVI (8.1), Claim (7), page 72.
The segment has no old drawing vertex except its ends. If their
distance were at least `ψ`, it would be the forbidden `H`-path. -/
theorem section9_initial_segment_short (hS : IsClosedSurface S)
    {α : Type u} {βe : Type v} {G P : Graph α βe} {H : Drawing S}
    (η : SpanEmbedding H G) {θ β ψ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {Y : Set S}
    {Λ : S → Set S} {C : S → Drawing S} {X : S → Set S}
    (hMet : HasTangleMetric H θ T d)
    (hSymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hBattle : ∀ y ∈ Y, IsBattlefield H T d θ β {y} (Λ y) (C y) (X y))
    (hψ : 3 ≤ ψ) (hβ : ψ ≤ β)
    (hNoPath : ∀ Q s t, s ∈ H.V → t ∈ H.V →
      IsHPathWithEnds G η.imageGraph Q (η.vMap s) (η.vMap t) →
      ψ ≤ d {s} {t} → (∀ y ∈ Y, ψ ≤ d {s} {y}) → False)
    {s t : S} (hs : s ∈ H.V) (ht : t ∈ H.V)
    (hsOut : ∀ y ∈ Y, s ∉ Λ y)
    (hP : GraphMinor.GM09.IsGraphPathWithEnds G P (η.vMap s) (η.vMap t))
    (hst : s ≠ t) (hInter : V(P) ∩ V(η.imageGraph) = {η.vMap s, η.vMap t}) :
    d {s} {t} < ψ := by
  by_contra hlong
  have hdist : ψ ≤ d {s} {t} := by omega
  have hHP := isHPath_of_far_ends hS η hMet hs ht hP (fun heq => hst (η.bijOn_v.injOn hs ht heq))
    hInter (hψ.trans hdist)
  apply hNoPath P s t hs ht hHP hdist
  intro y hy
  rw [hSymm {s} (Or.inl (Or.inl ⟨s, hs, rfl⟩)) {y} (hBattle y hy).isZone.z_mem]
  exact hβ.trans (battlefield_dist_ge_of_notMem (hBattle y hy) hs (hsOut y hy))

omit [T2Space S] in
/-- The metric contradiction in XVI (8.1), Claim (8), page 73.
Two short initial segments cannot enter the same new region when the
ends of the new path are at distance at least `2ψ`. -/
theorem section9_distinct_entered_regions
    {H K : Drawing S} {d d' : Set S → Set S → ℕ} {ψ : ℕ}
    {s₁ s₂ t₁ t₂ : S} {r : Set S}
    (hs₁ : s₁ ∈ H.V) (hs₂ : s₂ ∈ H.V)
    (ht₁ : t₁ ∈ H.V) (ht₂ : t₂ ∈ H.V)
    (hs₁K : s₁ ∈ K.V) (hs₂K : s₂ ∈ K.V) (hr : r ∈ K.R)
    (ht₁r : t₁ ∈ r) (ht₂r : t₂ ∈ r)
    (hLe : ∀ x y : S, pointDist K d' x y ≤ pointDist H d x y)
    (hTri : ∀ a ∈ K.A, ∀ b ∈ K.A, ∀ c ∈ K.A, d' a c ≤ d' a b + d' b c)
    (hSymm : ∀ a ∈ K.A, ∀ b ∈ K.A, d' a b = d' b a)
    (hShort₁ : d {s₁} {t₁} < ψ) (hShort₂ : d {s₂} {t₂} < ψ)
    (hLong : 2 * ψ ≤ d' {s₁} {s₂}) : False := by
  have hs₁A : ({s₁} : Set S) ∈ K.A := Or.inl (Or.inl ⟨s₁, hs₁K, rfl⟩)
  have hs₂A : ({s₂} : Set S) ∈ K.A := Or.inl (Or.inl ⟨s₂, hs₂K, rfl⟩)
  have hrA : r ∈ K.A := Or.inr hr
  have h₁ := hLe s₁ t₁
  have h₂ := hLe s₂ t₂
  rw [pointDist_of_mem_vertices d hs₁ ht₁,
    GraphMinor.GM15.pointDist_eq_of_mem_atom hs₁A hrA (mem_singleton s₁) ht₁r] at h₁
  rw [pointDist_of_mem_vertices d hs₂ ht₂,
    GraphMinor.GM15.pointDist_eq_of_mem_atom hs₂A hrA (mem_singleton s₂) ht₂r] at h₂
  have hBound := hTri {s₁} hs₁A r hrA {s₂} hs₂A
  rw [hSymm r hrA {s₂} hs₂A] at hBound
  change d' {s₁} r ≤ d {s₁} {t₁} at h₁
  change d' {s₂} r ≤ d {s₂} {t₂} at h₂
  omega

end GraphMinor.GM16
