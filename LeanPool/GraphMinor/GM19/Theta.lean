/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.DiscSlope
public import LeanPool.GraphMinor.Surface.Epstein
import LeanPool.GraphMinor.GM11.DrawingTopology

/-!
# Three paths with the same ends

Let three lines with the same ends be otherwise disjoint. If two of the three `O`-arcs they form are
null-homotopic, so
is the third. The proof of (5.5) uses this to shorten a circuit of `Γ*` through a pole.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

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
  obtain ⟨dU, -, -, -, -⟩ :=
    GM11.theta_glue_discs hT l₀ l₁ l₂ i₀₁ i₁₂ i₂₀ d₀ d₁ f₀ f₁ h₀ h₁
  exact hnull _ dU (union_subset (subset_union_right.trans sub₁ |>.trans subset_union_right)
    (subset_union_left.trans sub₀ |>.trans subset_union_left))

end GraphMinor.GM19
