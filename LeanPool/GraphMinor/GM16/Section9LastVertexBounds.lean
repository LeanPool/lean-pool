/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9ShortPaths

/-!
# The last old vertex before crossing the annulus

Claim (15) in XVI (8.1) bounds the distance from this vertex to the
first battlefield centre. It is outside the larger nested zone, which
gives the lower bound. It either remains in the battlefield or is the
initial end of the path, which gives the upper bound.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S]

/-- Graph Minors XVI, proof of (8.1), Claim (15), page 75.
The two bounds use the atom capture of the outer zone and the short
initial segment from Claim (7). -/
theorem section9_last_vertex_bounds {H : Drawing S} {d : Set S → Set S → ℕ}
    {y s t u : S} {Λ M : Set S} {γ i ψ : ℕ}
    (hZone : IsLambdaZoneAround H d γ {y} Λ)
    (hy : y ∈ H.V) (hs : s ∈ H.V) (ht : t ∈ H.V) (hu : u ∈ H.V)
    (hSymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hTri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (hCapture : ∀ a ∈ H.A, d {y} a < i + ψ + 2 → a ⊆ M)
    (huOut : u ∉ M) (htΛ : t ∈ Λ) (hShort : d {s} {t} < ψ)
    (huCase : u = s ∨ u ∈ Λ) :
    i + ψ + 2 ≤ d {u} {y} ∧ d {u} {y} ≤ γ + ψ := by
  have hyA : ({y} : Set S) ∈ H.A := Or.inl (Or.inl ⟨y, hy, rfl⟩)
  have huA : ({u} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have htA : ({t} : Set S) ∈ H.A := Or.inl (Or.inl ⟨t, ht, rfl⟩)
  constructor
  · rw [hSymm {u} huA {y} hyA]
    by_contra hsmall
    exact huOut (hCapture {u} huA (by omega) (mem_singleton u))
  · rcases huCase with huS | huΛ
    · subst u
      have hsA : ({s} : Set S) ∈ H.A := Or.inl (Or.inl ⟨s, hs, rfl⟩)
      have hty := hZone.dist_le {t} htA (singleton_subset_iff.mpr (subset_closure htΛ))
      have hbound := hTri {s} hsA {t} htA {y} hyA
      rw [hSymm {t} htA {y} hyA] at hbound
      omega
    · have hbound := hZone.dist_le {u} huA (singleton_subset_iff.mpr (subset_closure huΛ))
      rw [hSymm {u} huA {y} hyA]
      exact hbound.trans (Nat.le_add_right γ ψ)

/-- The last vertex in Claim (15) is far from every battlefield
centre. For the other centres use their separation from the first. -/
theorem section9_last_vertex_far {H : Drawing S} {d : Set S → Set S → ℕ}
    {Y : Set S} {y u : S} {γ ψ sep : ℕ}
    (hY : Y ⊆ H.V) (hy : y ∈ Y) (hu : u ∈ H.V)
    (hTri : ∀ a ∈ H.A, ∀ b ∈ H.A, ∀ c ∈ H.A, d a c ≤ d a b + d b c)
    (hSymm : ∀ a ∈ H.A, ∀ b ∈ H.A, d a b = d b a)
    (hSep : ∀ z ∈ Y, y ≠ z → sep ≤ d {y} {z})
    (hBudget : γ + 2 * ψ ≤ sep) (hLower : ψ ≤ d {u} {y}) (hUpper : d {u} {y} ≤ γ + ψ) :
    ∀ z ∈ Y, ψ ≤ d {u} {z} := by
  intro z hz
  by_cases heq : y = z
  · exact heq ▸ hLower
  · have hyA : ({y} : Set S) ∈ H.A := Or.inl (Or.inl ⟨y, hY hy, rfl⟩)
    have huA : ({u} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
    have hzA : ({z} : Set S) ∈ H.A := Or.inl (Or.inl ⟨z, hY hz, rfl⟩)
    have hbound := hTri {y} hyA {u} huA {z} hzA
    rw [hSymm {y} hyA {u} huA] at hbound
    have hsep := hSep z hz heq
    omega

end GraphMinor.GM16
