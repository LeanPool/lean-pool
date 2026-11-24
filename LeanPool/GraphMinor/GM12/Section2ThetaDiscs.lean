/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2DiscChordSplit
import LeanPool.GraphMinor.GM12.Section2NormalNoncover

/-!
# The union relation for the three insides of a theta graph

In Case 2 of XII (2.1), page 244, the second tangle axiom rules out
covering the surface by the three selected discs. XI's theta-cover
lemma then puts one of the three lines in its opposite disc. Cutting
that disc along the line gives two subdiscs. Each is the selected disc
with the same boundary, since choosing the other disc would cover the
surface. Hence one selected disc is the union of the other two.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem line_ends_ne {S : Type*} [TopologicalSpace S] {L : Set S} {a b : S}
    (h : IsLineWithEnds L a b) : a ≠ b := by
  obtain ⟨f, hf0, hf1⟩ := h
  intro hab
  have heq : f 0 = f 1 := Subtype.ext (hf0.trans (hab.trans hf1.symm))
  exact zero_ne_one (f.injective heq)

/-- If one line of a theta graph lies in its opposite disc, and the
three chosen discs do not cover the surface, that disc is the union of
the other two. This is the disc-cutting step in XII (2.1), Case 2. -/
theorem theta_disc_union_of_chord_inside {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {A₀ A₁ A₂ Δ₀ Δ₁ Δ₂ : Set S} {a b : S}
    (l₀ : IsLineWithEnds A₀ a b) (l₁ : IsLineWithEnds A₁ a b) (l₂ : IsLineWithEnds A₂ a b)
    (i₀₁ : A₀ ∩ A₁ = {a, b}) (i₁₂ : A₁ ∩ A₂ = {a, b}) (i₂₀ : A₂ ∩ A₀ = {a, b})
    (d₀ : IsClosedDisc Δ₀) (d₁ : IsClosedDisc Δ₁) (d₂ : IsClosedDisc Δ₂)
    (f₀ : discBd Δ₀ = A₁ ∪ A₂) (f₁ : discBd Δ₁ = A₂ ∪ A₀) (f₂ : discBd Δ₂ = A₀ ∪ A₁)
    (hinside : A₀ ⊆ Δ₀) (hnot : Δ₀ ∪ Δ₁ ∪ Δ₂ ≠ univ) : Δ₀ = Δ₁ ∪ Δ₂ := by
  obtain ⟨E₁, E₂, hE₁, hE₂, hU, hb₁, hb₂⟩ := disc_split_with_boundary_arcs d₀ l₀ l₁ l₂
    i₁₂ i₀₁ (by rw [inter_comm]; exact i₂₀) f₀ hinside (line_ends_ne l₀)
  have hE₁sub : E₁ ⊆ Δ₀ := fun _ hx => hU ▸ Or.inl hx
  have hE₂sub : E₂ ⊆ Δ₀ := fun _ hx => hU ▸ Or.inr hx
  have he₂ : E₂ = Δ₁ := by
    by_contra hne
    have hcov := cover_of_discBd_eq hS hE₂ d₁ (hb₂.trans f₁.symm) hne
    apply hnot
    apply Set.Subset.antisymm (subset_univ _)
    intro x _
    have hm : x ∈ E₂ ∪ Δ₁ := hcov.symm ▸ mem_univ x
    rcases hm with hx | hx
    · exact Or.inl (Or.inl (hE₂sub hx))
    · exact Or.inl (Or.inr hx)
  have he₁ : E₁ = Δ₂ := by
    by_contra hne
    have hbd : discBd E₁ = discBd Δ₂ := hb₁.trans ((union_comm _ _).trans f₂.symm)
    have hcov := cover_of_discBd_eq hS hE₁ d₂ hbd hne
    apply hnot
    apply Set.Subset.antisymm (subset_univ _)
    intro x _
    have hm : x ∈ E₁ ∪ Δ₂ := hcov.symm ▸ mem_univ x
    rcases hm with hx | hx
    · exact Or.inl (Or.inl (hE₁sub hx))
    · exact Or.inr hx
  rw [he₁, he₂, union_comm] at hU
  exact hU.symm

/-- The theta-disc union assertion used in Case 2 of XII (2.1), page 244:
if the three insides do not cover the surface, one is the union of the
other two. -/
theorem theta_disc_union_of_not_cover {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {A₀ A₁ A₂ Δ₀ Δ₁ Δ₂ : Set S} {a b : S}
    (l₀ : IsLineWithEnds A₀ a b) (l₁ : IsLineWithEnds A₁ a b) (l₂ : IsLineWithEnds A₂ a b)
    (i₀₁ : A₀ ∩ A₁ = {a, b}) (i₁₂ : A₁ ∩ A₂ = {a, b}) (i₂₀ : A₂ ∩ A₀ = {a, b})
    (d₀ : IsClosedDisc Δ₀) (d₁ : IsClosedDisc Δ₁) (d₂ : IsClosedDisc Δ₂)
    (f₀ : discBd Δ₀ = A₁ ∪ A₂) (f₁ : discBd Δ₁ = A₂ ∪ A₀) (f₂ : discBd Δ₂ = A₀ ∪ A₁)
    (hnot : Δ₀ ∪ Δ₁ ∪ Δ₂ ≠ univ) :
    Δ₀ = Δ₁ ∪ Δ₂ ∨ Δ₁ = Δ₂ ∪ Δ₀ ∨ Δ₂ = Δ₀ ∪ Δ₁ := by
  by_cases h₀ : A₀ ⊆ Δ₀
  · exact Or.inl (theta_disc_union_of_chord_inside hS l₀ l₁ l₂ i₀₁ i₁₂ i₂₀ d₀ d₁ d₂ f₀ f₁ f₂ h₀
    hnot)
  by_cases h₁ : A₁ ⊆ Δ₁
  · right; left
    apply theta_disc_union_of_chord_inside hS l₁ l₂ l₀ i₁₂ i₂₀ i₀₁ d₁ d₂ d₀ f₁ f₂ f₀ h₁
    simpa only [union_assoc, union_left_comm, union_comm] using hnot
  by_cases h₂ : A₂ ⊆ Δ₂
  · right; right
    apply theta_disc_union_of_chord_inside hS l₂ l₀ l₁ i₂₀ i₀₁ i₁₂ d₂ d₀ d₁ f₂ f₀ f₁ h₂
    simpa only [union_assoc, union_left_comm, union_comm] using hnot
  apply (hnot ?_).elim
  apply theta_cover hS l₀ l₁ l₂ i₀₁ i₁₂ i₂₀ d₀ d₁ d₂ _ _ _ h₀ h₁ h₂
  · rw [IsClosedDisc.frontier_eq_discBd hS d₀, f₀]
  · rw [IsClosedDisc.frontier_eq_discBd hS d₁, f₁]
  · rw [IsClosedDisc.frontier_eq_discBd hS d₂, f₂]

/-- An atom meeting one inside of such a theta graph meets at least one
of the other two, as used before applying the induction in XII (2.1). -/
theorem meets_one_of_theta_disc_union {S : Type*} {C D₀ D₁ D₂ : Set S}
    (hunion : D₀ = D₁ ∪ D₂ ∨ D₁ = D₂ ∪ D₀ ∨ D₂ = D₀ ∪ D₁)
    (hC : (C ∩ D₀).Nonempty) : (C ∩ D₁).Nonempty ∨ (C ∩ D₂).Nonempty := by
  obtain ⟨x, hxC, hx₀⟩ := hC
  rcases hunion with h | h | h
  · rw [h] at hx₀
    rcases hx₀ with hx₁ | hx₂
    · exact Or.inl ⟨x, hxC, hx₁⟩
    · exact Or.inr ⟨x, hxC, hx₂⟩
  · exact Or.inl ⟨x, hxC, h.symm ▸ Or.inr hx₀⟩
  · exact Or.inr ⟨x, hxC, h.symm ▸ Or.inl hx₀⟩

/-- The tangle and theta-disc step of Case 2 in Graph Minors XII, (2.1),
page 244. An atom meeting the original selected inside meets one of the
two smaller selected insides. The second tangle axiom supplies non-cover. -/
theorem theorem_2_1_case2_disc_step {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ : PaintingOrDrawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    {A₀ A₁ A₂ Δ₀ Δ₁ Δ₂ C : Set S} {a b : S}
    (l₀ : IsLineWithEnds A₀ a b) (l₁ : IsLineWithEnds A₁ a b) (l₂ : IsLineWithEnds A₂ a b)
    (i₀₁ : A₀ ∩ A₁ = {a, b}) (i₁₂ : A₁ ∩ A₂ = {a, b}) (i₂₀ : A₂ ∩ A₀ = {a, b})
    (d₀ : IsClosedDisc Δ₀) (d₁ : IsClosedDisc Δ₁) (d₂ : IsClosedDisc Δ₂)
    (f₀ : discBd Δ₀ = A₁ ∪ A₂) (f₁ : discBd Δ₁ = A₂ ∪ A₀) (f₂ : discBd Δ₂ = A₀ ∪ A₁)
    (n₀ : Γ.IsNormal (discBd Δ₀)) (n₁ : Γ.IsNormal (discBd Δ₁)) (n₂ : Γ.IsNormal (discBd Δ₂))
    (m₀ : (Γ.inter Δ₀, Γ.interOutside Δ₀) ∈ T)
    (m₁ : (Γ.inter Δ₁, Γ.interOutside Δ₁) ∈ T)
    (m₂ : (Γ.inter Δ₂, Γ.interOutside Δ₂) ∈ T)
    (hC : (C ∩ Δ₀).Nonempty) : (C ∩ Δ₁).Nonempty ∨ (C ∩ Δ₂).Nonempty := by
  have hnot : Δ₀ ∪ Δ₁ ∪ Δ₂ ≠ univ := by
    intro hcov
    exact not_cover_of_normal_frontiers hT d₀.isCompact.isClosed d₁.isCompact.isClosed
      d₂.isCompact.isClosed
      (by rwa [IsClosedDisc.frontier_eq_discBd hS d₀])
      (by rwa [IsClosedDisc.frontier_eq_discBd hS d₁])
      (by rwa [IsClosedDisc.frontier_eq_discBd hS d₂]) m₀ m₁ m₂ hcov
  exact meets_one_of_theta_disc_union
    (theta_disc_union_of_not_cover hS l₀ l₁ l₂ i₀₁ i₁₂ i₂₀ d₀ d₁ d₂ f₀ f₁ f₂ hnot) hC

end GraphMinor.GM12
