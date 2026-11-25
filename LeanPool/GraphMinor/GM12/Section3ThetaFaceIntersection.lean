/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section6

/-!
# Intersections of adjacent theta-face discs

The proof of XII (3.2), page 246, uses the three faces bounded
by pairs of theta arcs. Two adjacent face discs meet in their
common boundary arc. The proof separates each opposite arc from
its disc, then separates the interiors of the two discs. This is
the same separation argument used in XI's theta-union lemma.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Adjacent theta-face discs intersect exactly in their common
boundary arc, as used to check XII (3.1)(iv) in (3.2). -/
theorem theta_face_disc_intersection {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {A₀ A₁ A₂ Δ₀ Δ₁ : Set S} {a b : S}
    (l₀ : IsLineWithEnds A₀ a b) (l₁ : IsLineWithEnds A₁ a b)
    (i₀₁ : A₀ ∩ A₁ = {a, b}) (i₁₂ : A₁ ∩ A₂ = {a, b}) (i₂₀ : A₂ ∩ A₀ = {a, b})
    (d₀ : IsClosedDisc Δ₀) (d₁ : IsClosedDisc Δ₁)
    (f₀ : frontier Δ₀ = A₁ ∪ A₂) (f₁ : frontier Δ₁ = A₂ ∪ A₀)
    (h₀ : ¬ A₀ ⊆ Δ₀) (h₁ : ¬ A₁ ⊆ Δ₁) : Δ₀ ∩ Δ₁ = A₂ :=
  (theta_disc_intersection hS l₀ l₁ i₀₁ i₁₂ i₂₀ d₀ d₁ f₀ f₁ h₀ h₁).1

end GraphMinor.GM12
