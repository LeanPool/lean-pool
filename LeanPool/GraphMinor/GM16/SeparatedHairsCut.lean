/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM09.Basic

/-!
# Excluding the close-pair outcome after clearing

The separator makes every surviving path shorter than `2ψ`.
A path whose ends are each within `ψ` of two different separated
hairs would then make those hairs less than `4ψ` apart. This is
the contradiction excluding the second outcome of (8.3) in XVI
(7.1), page 70.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14
universe u v w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
variable {α : Type u} {β : Type v}

/-- Two close ends of a surviving path contradict separated hairs
when the separator meets every path of length at least `2ψ` in the metric. -/
theorem close_pair_path_contradiction (hS : IsClosedSurface S)
    {G P : Graph α β} {H : Drawing S} (η : SpanEmbedding H G)
    {θ sep ψ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hMet : HasTangleMetric H θ T d)
    {X Z : Set α} {Y : Set S} (hY : Y ⊆ H.V)
    (hSep : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → sep ≤ d {y} {z})
    (hBudget : 4 * ψ ≤ sep)
    (hCut : ∀ Q s t, s ∈ H.V → t ∈ H.V →
      IsHPathWithEnds (deleteVertices G X) η.imageGraph Q (η.vMap s) (η.vMap t) →
      2 * ψ ≤ d {s} {t} → (Z ∩ V(Q)).Nonempty)
    {s t y z : S} (hs : s ∈ H.V) (ht : t ∈ H.V)
    (hy : y ∈ Y) (hz : z ∈ Y) (hyz : y ≠ z)
    (hP : IsHPathWithEnds (deleteVertices G (X ∪ Z)) η.imageGraph P (η.vMap s) (η.vMap t))
    (hsy : d {s} {y} < ψ) (htz : d {t} {z} < ψ) : False := by
  have hDel : deleteVertices G (X ∪ Z) ≤ deleteVertices G X := by
    refine ⟨fun x hx => ⟨hx.1, fun hxX => hx.2 (Or.inl hxX)⟩, ?_⟩
    intro e a b hl
    exact ⟨hl.1, ⟨hl.2.1.1, fun h => hl.2.1.2 (Or.inl h)⟩,
      ⟨hl.2.2.1, fun h => hl.2.2.2 (Or.inl h)⟩⟩
  have hP' : IsHPathWithEnds (deleteVertices G X) η.imageGraph P (η.vMap s) (η.vMap t) :=
    ⟨hP.1.trans hDel, hP.2.1.mono hDel, hP.2.2⟩
  have hShort : d {s} {t} < 2 * ψ := by
    by_contra hLong
    obtain ⟨x, hxZ, hxP⟩ := hCut P s t hs ht hP' (Nat.le_of_not_gt hLong)
    have hxDel := hP.2.1.1.vertexSet_mono hxP
    exact hxDel.2 (Or.inr hxZ)
  obtain ⟨_, _, _, hSymm, hTri, _⟩ := GM11.gm15_theorem_9_1 H θ T d hS inferInstance hMet
  have hsA : ({s} : Set S) ∈ H.A := Or.inl (Or.inl ⟨s, hs, rfl⟩)
  have htA : ({t} : Set S) ∈ H.A := Or.inl (Or.inl ⟨t, ht, rfl⟩)
  have hyA : ({y} : Set S) ∈ H.A := Or.inl (Or.inl ⟨y, hY hy, rfl⟩)
  have hzA : ({z} : Set S) ∈ H.A := Or.inl (Or.inl ⟨z, hY hz, rfl⟩)
  have h₁ := hTri {y} hyA {s} hsA {z} hzA
  have h₂ := hTri {s} hsA {t} htA {z} hzA
  rw [hSymm {y} hyA {s} hsA] at h₁
  have hFar := hSep y hy z hz hyz
  omega

end GraphMinor.GM16
