/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10b
public import LeanPool.GraphMinor.GM11.Section6

/-!
# The slope of a tangle in a painting

Graph Minors XIX, Section 7, uses the results of Graph Minors XI for the radial drawing `Γ*` of a
painting `Γ`. These results are about a slope in `Γ*`. The painting `Γ` as a subset of `Σ̂` is
neither a
painting nor a drawing in the sense of XI, so `GM11.isSlope_of_derived` does not apply to it. We
repeat its short proof here. The result used later is `TangleDatum.isSlope`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

omit [T2Space S] [T2Space Shat] in
/-- A circuit of `Γ*` of length `< 2 rep(𝒯)` has its inside. -/
theorem ins_spec (D : TangleDatum cap χ) {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G)
    (hlt : F.E.ncard < 2 * D.rep) : IsInsOf D.rad D.ord D.𝒯 F (D.ins F) := by
  have hex : ∃ Δ : Set Shat, IsInsOf D.rad D.ord D.𝒯 F Δ := by
    obtain ⟨Δ, h₁, h₂, h₃⟩ := (tangleRep_spec D.rad D.ord D.𝒯).2 F hF hlt
    exact ⟨Δ, hF, hlt, h₁, h₂, h₃⟩
  simp only [ins, dite_eq_left hex]
  exact Classical.choose_spec hex

omit [T2Space S] in
/-- Three insides do not cover `Σ̂`, by the second tangle axiom. -/
theorem not_cover (D : TangleDatum cap χ) {F₁ F₂ F₃ : Drawing Shat} {Δ₁ Δ₂ Δ₃ : Set Shat}
    (h₁ : IsInsOf D.rad D.ord D.𝒯 F₁ Δ₁) (h₂ : IsInsOf D.rad D.ord D.𝒯 F₂ Δ₂)
    (h₃ : IsInsOf D.rad D.ord D.𝒯 F₃ Δ₃) (hcov : Δ₁ ∪ Δ₂ ∪ Δ₃ = univ) : False := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have c₁ := closure_discInt h₁.2.2.1
  have c₂ := closure_discInt h₂.2.2.1
  have c₃ := closure_discInt h₃.2.2.1
  have hc := part_cover D.rad h₁.1.1 h₂.1.1 h₃.1.1 (isSide_int hT h₁.2.2.1 h₁.2.2.2.1)
    (isSide_int hT h₂.2.2.1 h₂.2.2.2.1) (isSide_int hT h₃.2.2.1 h₃.2.2.2.1) (by
      intro x
      rw [c₁, c₂, c₃]
      have hx : x ∈ Δ₁ ∪ Δ₂ ∪ Δ₃ := hcov ▸ mem_univ x
      rcases hx with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
  rw [c₁, c₂, c₃] at hc
  exact D.isTangle.axiom2 h₁.2.2.2.2 h₂.2.2.2.2 h₃.2.2.2.2 hc

omit [T2Space S] in
/-- `ins` is a slope in `Γ*` of order `rep(𝒯)`. -/
theorem isSlope (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep) : IsSlope D.rad.G (2 * D.rep) D.ins := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hfr : ∀ C : Drawing Shat, C.IsCircuit → C.IsSubdrawing D.rad.G → C.length < 2 * D.rep →
      IsClosedDisc (D.ins C) ∧ frontier (D.ins C) = C.U ∧ IsClosed (D.ins C) ∧
      IsInsOf D.rad D.ord D.𝒯 C (D.ins C) := by
    intro C h s l
    have hi := D.ins_spec ⟨s, h⟩ l
    refine ⟨hi.2.2.1, ?_, hi.2.2.1.isClosed, hi⟩
    rw [IsClosedDisc.frontier_eq_discBd hT hi.2.2.1, hi.2.2.2.1]
  have hmono : ∀ C₁ C₂ : Drawing Shat, C₁.IsCircuit → C₁.IsSubdrawing D.rad.G →
      C₁.length < 2 * D.rep → C₂.IsCircuit → C₂.IsSubdrawing D.rad.G → C₂.length < 2 * D.rep →
      C₁.U ⊆ D.ins C₂ → D.ins C₁ ⊆ D.ins C₂ := by
    intro C₁ C₂ h₁ s₁ l₁ h₂ s₂ l₂ hsub
    obtain ⟨d₁, f₁, c₁, m₁⟩ := hfr C₁ h₁ s₁ l₁
    obtain ⟨d₂, f₂, c₂, m₂⟩ := hfr C₂ h₂ s₂ l₂
    obtain ⟨Δ, ⟨hΔD, dΔ, bΔ, -⟩, -⟩ := disc_oArc (D.ins C₂) (discBd (D.ins C₁)) d₂
      (by rw [← IsClosedDisc.frontier_eq_discBd hT d₁, f₁]; exact hsub) d₁.isOArc_discBd
    by_cases heq : D.ins C₁ = Δ
    · exact heq ▸ hΔD
    · exfalso
      have hcov := cover_of_discBd_eq hT d₁ dΔ bΔ.symm heq
      refine D.not_cover m₁ m₂ m₂ (eq_univ_of_univ_subset ?_)
      rw [← hcov]
      exact fun x hx ↦ hx.elim (fun h ↦ Or.inl (Or.inl h)) fun h ↦ Or.inr (hΔD h)
  refine ⟨by omega, fun C h s l ↦ (hfr C h s l).1, fun C h s l ↦ ?_, hmono, ?_⟩
  · rw [subBd_eq_frontier]
    exact (hfr C h s l).2.1
  intro P₀ P₁ P₂ a b hP₀ hP₁ hP₂ s₀ s₁ s₂ p₀ p₁ p₂ v₀₁ v₁₂ v₂₀ e₀₁ e₁₂ e₂₀ l₀ l₁ l₂
  have hab := ne_of_isPathBetween hP₀ p₀
  have supU : ∀ {P Q : Drawing Shat}, P.IsSubdrawing D.rad.G → Q.IsSubdrawing D.rad.G →
      (D.rad.G.sup P Q).U = P.U ∪ Q.U := by
    intro P Q hP hQ
    rw [Drawing.U_eq, Drawing.sup_V hP hQ, Drawing.sup_E hP hQ, P.U_eq, Q.U_eq, biUnion_union]
    ext x
    simp only [mem_union]
    tauto
  have circ : ∀ {P Q : Drawing Shat}, P.IsPathBetween a b → Q.IsPathBetween a b →
      P.IsSubdrawing D.rad.G → Q.IsSubdrawing D.rad.G → P.V ∩ Q.V = {a, b} → Disjoint P.E Q.E →
      (D.rad.G.sup P Q).IsCircuit ∧ (D.rad.G.sup P Q).IsSubdrawing D.rad.G := fun hP hQ sP sQ v e ↦
    ⟨Drawing.isCircuit_sup hP hQ sP sQ hab v e, Drawing.sup_isSubdrawing _ _ _⟩
  obtain ⟨c₀, ss₀⟩ := circ hP₁ hP₂ s₁ s₂ v₁₂ e₁₂
  obtain ⟨c₁, ss₁⟩ := circ hP₂ hP₀ s₂ s₀ v₂₀ e₂₀
  obtain ⟨c₂, ss₂⟩ := circ hP₀ hP₁ s₀ s₁ v₀₁ e₀₁
  obtain ⟨d₀, f₀, cl₀, m₀⟩ := hfr _ c₀ ss₀ l₀
  obtain ⟨d₁, f₁, cl₁, m₁⟩ := hfr _ c₁ ss₁ l₁
  obtain ⟨d₂, f₂, cl₂, m₂⟩ := hfr _ c₂ ss₂ l₂
  rw [supU s₁ s₂] at f₀
  rw [supU s₂ s₀] at f₁
  rw [supU s₀ s₁] at f₂
  have sub : ∀ {Δ F : Set Shat}, IsClosed Δ → frontier Δ = F → F ⊆ Δ := fun c h ↦
    h ▸ c.frontier_subset
  have sb₀ := sub cl₀ f₀
  have sb₁ := sub cl₁ f₁
  have sb₂ := sub cl₂ f₂
  by_cases h₀ : P₀.U ⊆ D.ins (D.rad.G.sup P₁ P₂)
  · refine Or.inl ⟨hmono _ _ c₁ ss₁ l₁ c₀ ss₀ l₀ ?_, hmono _ _ c₂ ss₂ l₂ c₀ ss₀ l₀ ?_⟩
    · rw [supU s₂ s₀]
      exact union_subset (subset_union_right.trans sb₀) h₀
    · rw [supU s₀ s₁]
      exact union_subset h₀ (subset_union_left.trans sb₀)
  by_cases h₁ : P₁.U ⊆ D.ins (D.rad.G.sup P₂ P₀)
  · refine Or.inr (Or.inl ⟨hmono _ _ c₀ ss₀ l₀ c₁ ss₁ l₁ ?_, hmono _ _ c₂ ss₂ l₂ c₁ ss₁ l₁ ?_⟩)
    · rw [supU s₁ s₂]
      exact union_subset h₁ (subset_union_left.trans sb₁)
    · rw [supU s₀ s₁]
      exact union_subset (subset_union_right.trans sb₁) h₁
  by_cases h₂ : P₂.U ⊆ D.ins (D.rad.G.sup P₀ P₁)
  · refine Or.inr (Or.inr ⟨hmono _ _ c₀ ss₀ l₀ c₂ ss₂ l₂ ?_, hmono _ _ c₁ ss₁ l₁ c₂ ss₂ l₂ ?_⟩)
    · rw [supU s₁ s₂]
      exact union_subset (subset_union_right.trans sb₂) h₂
    · rw [supU s₂ s₀]
      exact union_subset h₂ (subset_union_left.trans sb₂)
  exfalso
  have hcov := theta_cover hT (isLine_of_isPathBetween hP₀ hab) (isLine_of_isPathBetween hP₁ hab)
    (isLine_of_isPathBetween hP₂ hab) (by rw [U_inter_of_disjoint s₀ s₁ e₀₁, v₀₁])
    (by rw [U_inter_of_disjoint s₁ s₂ e₁₂, v₁₂]) (by rw [U_inter_of_disjoint s₂ s₀ e₂₀, v₂₀])
    d₀ d₁ d₂ f₀ f₁ f₂ h₀ h₁ h₂
  exact D.not_cover m₀ m₁ m₂ hcov

end TangleDatum

end GraphMinor.GM19
