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
    (h₀ : ¬ A₀ ⊆ Δ₀) (h₁ : ¬ A₁ ⊆ Δ₁) : Δ₀ ∩ Δ₁ = A₂ := by
  have : T2Space S := hS.2.1
  have c₀ : IsClosed Δ₀ := d₀.isCompact.isClosed
  have c₁ : IsClosed Δ₁ := d₁.isCompact.isClosed
  have sub₀ : A₁ ∪ A₂ ⊆ Δ₀ := f₀ ▸ c₀.frontier_subset
  have sub₁ : A₂ ∪ A₀ ⊆ Δ₁ := f₁ ▸ d₁.isCompact.isClosed.frontier_subset
  have m₂ : ∀ x, x ∈ A₂ → x ∈ A₀ → x = a ∨ x = b := fun x h h' => by
    have : x ∈ A₂ ∩ A₀ := ⟨h, h'⟩
    rwa [i₂₀] at this
  have m₁ : ∀ x, x ∈ A₁ → x ∈ A₂ → x = a ∨ x = b := fun x h h' => by
    have : x ∈ A₁ ∩ A₂ := ⟨h, h'⟩
    rwa [i₁₂] at this
  have m₀ : ∀ x, x ∈ A₀ → x ∈ A₁ → x = a ∨ x = b := fun x h h' => by
    have : x ∈ A₀ ∩ A₁ := ⟨h, h'⟩
    rwa [i₀₁] at this
  have ha : a ∈ A₀ ∩ A₁ := by rw [i₀₁]; simp
  have hb : b ∈ A₀ ∩ A₁ := by rw [i₀₁]; simp
  have ha₂ : a ∈ A₁ ∩ A₂ := by rw [i₁₂]; simp
  have hb₂ : b ∈ A₁ ∩ A₂ := by rw [i₁₂]; simp
  -- The inner parts of `A₀` and `A₁` lie outside `Δ₀` and `Δ₁`.
  have out₀ : Disjoint (A₀ \ {a, b}) Δ₀ := by
    have hdis : Disjoint (A₀ \ {a, b}) (frontier Δ₀) := by
      rw [f₀, disjoint_left]
      rintro x ⟨hx, hxn⟩ (h' | h')
      · exact hxn (m₀ x hx h')
      · exact hxn (m₂ x h' hx)
    refine (subset_or_disjoint_of_frontier c₀ (IsLineWithEnds.isPreconnected_sdiff_pair l₀)
      hdis).resolve_left ?_
    intro hsub
    refine h₀ fun x hx => ?_
    by_cases hxab : x ∈ ({a, b} : Set S)
    · rcases hxab with rfl | rfl
      · exact sub₀ (Or.inl ha.2)
      · exact sub₀ (Or.inl hb.2)
    · exact hsub ⟨hx, hxab⟩
  have out₁ : Disjoint (A₁ \ {a, b}) Δ₁ := by
    have hdis : Disjoint (A₁ \ {a, b}) (frontier Δ₁) := by
      rw [f₁, disjoint_left]
      rintro x ⟨hx, hxn⟩ (h' | h')
      · exact hxn (m₁ x hx h')
      · exact hxn (m₀ x h' hx)
    refine (subset_or_disjoint_of_frontier c₁ (IsLineWithEnds.isPreconnected_sdiff_pair l₁)
      hdis).resolve_left ?_
    intro hsub
    refine h₁ fun x hx => ?_
    by_cases hxab : x ∈ ({a, b} : Set S)
    · rcases hxab with rfl | rfl
      · exact sub₁ (Or.inl ha₂.2)
      · exact sub₁ (Or.inl hb₂.2)
    · exact hsub ⟨hx, hxab⟩
  -- So the interior of `Δ₁` misses `Δ₀`.
  have hint : Disjoint (Δ₁ \ frontier Δ₁) Δ₀ := by
    have hdis : Disjoint (Δ₁ \ frontier Δ₁) (frontier Δ₀) := by
      rw [f₀, disjoint_left]
      rintro x ⟨hxD, hxf⟩ (h' | h')
      · by_cases hxab : x ∈ ({a, b} : Set S)
        · apply hxf
          rw [f₁]
          rcases hxab with rfl | rfl
          · exact Or.inl ha₂.2
          · exact Or.inl hb₂.2
        · exact disjoint_left.mp out₁ ⟨h', hxab⟩ hxD
      · exact hxf (f₁ ▸ Or.inl h')
    refine (subset_or_disjoint_of_frontier c₀ (IsClosedDisc.isPreconnected_diff_frontier hS d₁)
      hdis).resolve_left ?_
    intro hsub
    refine h₀ fun x hx => ?_
    have hxD : x ∈ Δ₁ := sub₁ (Or.inr hx)
    exact c₀.closure_subset_iff.mpr hsub (IsClosedDisc.subset_closure_diff_frontier hS d₁ hxD)
  have hcap : Δ₀ ∩ Δ₁ = A₂ := by
    apply subset_antisymm
    · rintro x ⟨hx₀, hx₁⟩
      have hxf : x ∈ frontier Δ₁ := by
        by_contra hn
        exact disjoint_left.mp hint ⟨hx₁, hn⟩ hx₀
      rw [f₁] at hxf
      rcases hxf with h' | h'
      · exact h'
      · by_cases hxab : x ∈ ({a, b} : Set S)
        · rcases hxab with rfl | rfl
          · exact ha₂.2
          · exact hb₂.2
        · exact absurd hx₀ (disjoint_left.mp out₀ ⟨h', hxab⟩)
    · exact fun x hx => ⟨sub₀ (Or.inr hx), sub₁ (Or.inl hx)⟩
  exact hcap

end GraphMinor.GM12
