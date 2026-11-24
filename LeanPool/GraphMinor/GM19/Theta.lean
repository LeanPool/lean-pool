/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.DiscSlope
public import LeanPool.GraphMinor.Surface.Epstein

/-!
# Three paths with the same ends

Let three lines with the same ends be otherwise disjoint. If two of the three `O`-arcs they form are
null-homotopic, so
is the third. The proof of (5.5) uses this to shorten a circuit of `Γ*` through a pole.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

variable {T : Type} [TopologicalSpace T]

/-- If `A₁ ∪ A₂` and `A₂ ∪ A₀` are null-homotopic, then so is `A₀ ∪ A₁`. -/
theorem null_of_theta [ConnectedSpace T] (hT : IsClosedSurface T) {A₀ A₁ A₂ : Set T} {a b : T}
    (l₀ : IsLineWithEnds A₀ a b) (l₁ : IsLineWithEnds A₁ a b) (l₂ : IsLineWithEnds A₂ a b)
    (i₀₁ : A₀ ∩ A₁ = {a, b}) (i₁₂ : A₁ ∩ A₂ = {a, b}) (i₂₀ : A₂ ∩ A₀ = {a, b})
    (hO : IsOArc (A₀ ∪ A₁)) (hO₁ : IsOArc (A₁ ∪ A₂)) (hO₂ : IsOArc (A₂ ∪ A₀))
    (n₀ : IsNullHomotopicOArc (A₁ ∪ A₂)) (n₁ : IsNullHomotopicOArc (A₂ ∪ A₀)) :
    IsNullHomotopicOArc (A₀ ∪ A₁) := by
  have hS := IsClosedSurface.isSurface hT
  have : T2Space T := hT.2.1
  have hbd : ∀ F : Set T, Disjoint F (bd T) := fun F ↦ by
    rw [show bd T = ∅ from eq_empty_of_forall_notMem fun x hx ↦ hx (hT.2.2 x)]
    exact disjoint_empty _
  obtain ⟨Δ₀, -, d₀, f₀'⟩ := (epstein T univ _ hS inferInstance hO₁ (subset_univ _) (hbd _)).1 n₀
  obtain ⟨Δ₁, -, d₁, f₁'⟩ := (epstein T univ _ hS inferInstance hO₂ (subset_univ _) (hbd _)).1 n₁
  have f₀ : frontier Δ₀ = A₁ ∪ A₂ := by rw [IsClosedDisc.frontier_eq_discBd hT d₀, f₀']
  have f₁ : frontier Δ₁ = A₂ ∪ A₀ := by rw [IsClosedDisc.frontier_eq_discBd hT d₁, f₁']
  have hnull : ∀ Δ : Set T, IsClosedDisc Δ → A₀ ∪ A₁ ⊆ Δ → IsNullHomotopicOArc (A₀ ∪ A₁)
    := fun Δ hΔ hsub ↦
    (epstein T univ _ hS inferInstance hO (subset_univ _) (hbd _)).2.1 ⟨Δ, subset_univ _, hΔ, hsub⟩
  have c₀ : IsClosed Δ₀ := d₀.isCompact.isClosed
  have c₁ : IsClosed Δ₁ := d₁.isCompact.isClosed
  have sub₀ : A₁ ∪ A₂ ⊆ Δ₀ := f₀ ▸ c₀.frontier_subset
  have sub₁ : A₂ ∪ A₀ ⊆ Δ₁ := f₁ ▸ c₁.frontier_subset
  by_cases h₀ : A₀ ⊆ Δ₀
  · exact hnull Δ₀ d₀ (union_subset h₀ (subset_union_left.trans sub₀))
  by_cases h₁ : A₁ ⊆ Δ₁
  · exact hnull Δ₁ d₁ (union_subset (subset_union_right.trans sub₁) h₁)
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
    by_cases hxab : x ∈ ({a, b} : Set T)
    · rcases hxab with rfl | rfl
      · exact sub₀ (Or.inl ha.2)
      · exact sub₀ (Or.inl hb.2)
    · exact hsub ⟨hx, hxab⟩
  have hint : Disjoint (Δ₁ \ frontier Δ₁) Δ₀ := by
    have hdis : Disjoint (Δ₁ \ frontier Δ₁) (frontier Δ₀) := by
      rw [f₀, disjoint_left]
      rintro x ⟨hxD, hxf⟩ (h' | h')
      · by_cases hxab : x ∈ ({a, b} : Set T)
        · apply hxf
          rw [f₁]
          rcases hxab with rfl | rfl
          · exact Or.inl ha₂.2
          · exact Or.inl hb₂.2
        · have out₁ : Disjoint (A₁ \ {a, b}) Δ₁ := by
            have hdis : Disjoint (A₁ \ {a, b}) (frontier Δ₁) := by
              rw [f₁, disjoint_left]
              rintro y ⟨hy, hyn⟩ (h'' | h'')
              · exact hyn (m₁ y hy h'')
              · exact hyn (m₀ y h'' hy)
            refine (subset_or_disjoint_of_frontier c₁ (IsLineWithEnds.isPreconnected_sdiff_pair l₁)
              hdis).resolve_left ?_
            intro hsub
            refine h₁ fun y hy => ?_
            by_cases hyab : y ∈ ({a, b} : Set T)
            · rcases hyab with rfl | rfl
              · exact sub₁ (Or.inl ha₂.2)
              · exact sub₁ (Or.inl hb₂.2)
            · exact hsub ⟨hy, hyab⟩
          exact disjoint_left.mp out₁ ⟨h', hxab⟩ hxD
      · exact hxf (f₁ ▸ Or.inl h')
    refine (subset_or_disjoint_of_frontier c₀ (IsClosedDisc.isPreconnected_diff_frontier hT d₁)
      hdis).resolve_left ?_
    intro hsub
    refine h₀ fun x hx => ?_
    have hxD : x ∈ Δ₁ := sub₁ (Or.inr hx)
    exact c₀.closure_subset_iff.mpr hsub (IsClosedDisc.subset_closure_diff_frontier hT d₁ hxD)
  have hcap : Δ₀ ∩ Δ₁ = A₂ := by
    apply subset_antisymm
    · rintro x ⟨hx₀, hx₁⟩
      have hxf : x ∈ frontier Δ₁ := by
        by_contra hn
        exact disjoint_left.mp hint ⟨hx₁, hn⟩ hx₀
      rw [f₁] at hxf
      rcases hxf with h' | h'
      · exact h'
      · by_cases hxab : x ∈ ({a, b} : Set T)
        · rcases hxab with rfl | rfl
          · exact ha₂.2
          · exact hb₂.2
        · exact absurd hx₀ (disjoint_left.mp out₀ ⟨h', hxab⟩)
    · exact fun x hx => ⟨sub₀ (Or.inr hx), sub₁ (Or.inl hx)⟩
  have e₀ := IsClosedDisc.frontier_eq_discBd hT d₀
  have e₁ := IsClosedDisc.frontier_eq_discBd hT d₁
  obtain ⟨dU, -⟩ := disc_union Δ₀ Δ₁ A₂ a b d₀ d₁ l₂ hcap
    (by rw [← e₀, f₀]; exact subset_union_right) (by rw [← e₁, f₁]; exact subset_union_left)
  exact hnull _ dU (union_subset (subset_union_right.trans sub₁ |>.trans subset_union_right)
    (subset_union_left.trans sub₀ |>.trans subset_union_left))

end GraphMinor.GM19
