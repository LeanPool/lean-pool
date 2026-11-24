/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72CirclePatch
public import LeanPool.GraphMinor.GM11.EvenCircuit

/-!
# The two new half-edges in the local circle patch

Each new line in the patch at the vertex in XII (7.2) gives exactly
one half-edge there. The two lines meet only at the vertex. Thus the
new half-edges are distinct, and every remaining half-edge comes from
the old drawing. This is the input for selecting the mixed corners.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

private theorem half_index_eq_of_pair {H : Drawing S} {γ : Set S → I → S}
    (hγ : EdgePar H γ) {e : Set S} (he : e ∈ H.E) {v a : S}
    (hp : closure e ∩ H.V = {v, a}) (ha : a ≠ v)
    {b c : Bool} (hb : γ e (endOf b) = v) (hc : γ e (endOf c) = v) : b = c := by
  by_contra hbc
  have hboth : γ e 0 = v ∧ γ e 1 = v := by
    cases b with
    | false =>
      cases c with
      | false => exact (hbc rfl).elim
      | true => exact ⟨hb, hc⟩
    | true =>
      cases c with
      | false => exact ⟨hc, hb⟩
      | true => exact (hbc rfl).elim
  have hends := closure_inter_V_eq hγ he
  change closure e ∩ H.V = {γ e 0, γ e 1} at hends
  rw [hboth.1, hboth.2, pair_eq_singleton] at hends
  have hamem : a ∈ closure e ∩ H.V := hp.symm ▸ Or.inr rfl
  exact ha (by simpa only [hends, mem_singleton_iff] using hamem)

/-- The two line edges of the local patch for XII (7.2), page 260,
give exactly the two half-edges not belonging to the old drawing. -/
theorem circle_patch_halfEdges
    {Γ H : Drawing S} {L₀ L₁ : Set S} {v a b : S}
    (h₀ : IsLineWithEnds L₀ v a) (h₁ : IsLineWithEnds L₁ v b)
    (ha : a ≠ v) (hb : b ≠ v) (hv : v ∈ Γ.V)
    (hmeet : Γ.U ∩ (L₀ ∪ L₁) ⊆ {v}) (hcap : L₀ ∩ L₁ = {v})
    (hV : H.V = Γ.V ∪ {a, b})
    (hE : H.E = Γ.E ∪ {L₀ \ {v, a}, L₁ \ {v, b}})
    {γ : Set S → I → S} (hγ : EdgePar H γ) :
    ∃ j₀ j₁ : halfEdges H γ v, j₀ ≠ j₁ ∧
      j₀.1.1 = L₀ \ {v, a} ∧ j₁.1.1 = L₁ \ {v, b} ∧
      j₀.1.1 ∉ Γ.E ∧ j₁.1.1 ∉ Γ.E ∧
      ∀ k : halfEdges H γ v, k.1.1 ∉ Γ.E → k = j₀ ∨ k = j₁ := by
  have hvH : v ∈ H.V := hV.symm ▸ Or.inl hv
  have hvL₀ : v ∈ L₀ := by obtain ⟨e, h0, _⟩ := h₀; exact h0 ▸ (e 0).2
  have haL : a ∈ L₀ := by obtain ⟨e, _, h1⟩ := h₀; exact h1 ▸ (e 1).2
  have hvL₁ : v ∈ L₁ := by obtain ⟨e, h0, _⟩ := h₁; exact h0 ▸ (e 0).2
  have hbL : b ∈ L₁ := by obtain ⟨e, _, h1⟩ := h₁; exact h1 ▸ (e 1).2
  have hpair₀ : closure (L₀ \ {v, a}) ∩ H.V = {v, a} := by
    rw [closure_sdiff_pair h₀, hV]
    ext x
    constructor
    · rintro ⟨hxL, hxG | hxa | hxb⟩
      · exact Or.inl (mem_singleton_iff.mp (hmeet ⟨Γ.V_subset_U hxG, Or.inl hxL⟩))
      · exact Or.inr hxa
      · have hxv : x = v := mem_singleton_iff.mp (hcap ▸ ⟨hxL, hxb ▸ hbL⟩)
        exact Or.inl hxv
    · rintro (rfl | rfl)
      · exact ⟨hvL₀, Or.inl hv⟩
      · exact ⟨haL, Or.inr (Or.inl rfl)⟩
  have hpair₁ : closure (L₁ \ {v, b}) ∩ H.V = {v, b} := by
    rw [closure_sdiff_pair h₁, hV]
    ext x
    constructor
    · rintro ⟨hxL, hxG | hxa | hxb⟩
      · exact Or.inl (mem_singleton_iff.mp (hmeet ⟨Γ.V_subset_U hxG, Or.inr hxL⟩))
      · have hxv : x = v := mem_singleton_iff.mp (hcap ▸ ⟨hxa ▸ haL, hxL⟩)
        exact Or.inl hxv
      · exact Or.inr hxb
    · rintro (rfl | rfl)
      · exact ⟨hvL₁, Or.inl hv⟩
      · exact ⟨hbL, Or.inr (Or.inr rfl)⟩
  have he₀ : L₀ \ {v, a} ∈ H.E := hE.symm ▸ Or.inr (Or.inl rfl)
  have he₁ : L₁ \ {v, b} ∈ H.E := hE.symm ▸ Or.inr (Or.inr rfl)
  have hn₀ : L₀ \ {v, a} ∉ Γ.E := by
    intro he
    obtain ⟨x, hx⟩ := he.1
    have hxv := hmeet ⟨(he.2.1 hx).1, Or.inl hx.1⟩
    exact hx.2 (Or.inl (mem_singleton_iff.mp hxv))
  have hn₁ : L₁ \ {v, b} ∉ Γ.E := by
    intro he
    obtain ⟨x, hx⟩ := he.1
    have hxv := hmeet ⟨(he.2.1 hx).1, Or.inr hx.1⟩
    exact hx.2 (Or.inl (mem_singleton_iff.mp hxv))
  have hne : L₀ \ {v, a} ≠ L₁ \ {v, b} := by
    intro heq
    obtain ⟨x, hx⟩ := he₀.1
    have hx₁ : x ∈ L₁ \ {v, b} := heq ▸ hx
    have hxv : x = v := mem_singleton_iff.mp (hcap ▸ ⟨hx.1, hx₁.1⟩)
    exact hx.2 (Or.inl hxv)
  have hvcl₀ : v ∈ closure (L₀ \ {v, a}) := (hpair₀.symm ▸ Or.inl rfl : v ∈ closure
    (L₀ \ {v, a}) ∩ H.V).1
  have hvcl₁ : v ∈ closure (L₁ \ {v, b}) := (hpair₁.symm ▸ Or.inl rfl : v ∈ closure
    (L₁ \ {v, b}) ∩ H.V).1
  obtain ⟨c₀, hc₀⟩ := exists_end_eq hγ he₀ hvH hvcl₀
  obtain ⟨c₁, hc₁⟩ := exists_end_eq hγ he₁ hvH hvcl₁
  let j₀ : halfEdges H γ v := ⟨(L₀ \ {v, a}, c₀), he₀, hc₀⟩
  let j₁ : halfEdges H γ v := ⟨(L₁ \ {v, b}, c₁), he₁, hc₁⟩
  refine ⟨j₀, j₁, fun h => hne (congrArg (fun j : halfEdges H γ v => j.1.1) h),
    rfl, rfl, hn₀, hn₁, ?_⟩
  intro k hkn
  have hke : k.1.1 ∈ Γ.E ∪ {L₀ \ {v, a}, L₁ \ {v, b}} := hE ▸ k.2.1
  rcases hke with hko | hk₀ | hk₁
  · exact (hkn hko).elim
  · refine Or.inl (Subtype.ext (Prod.ext hk₀ ?_))
    have hkbool : γ (L₀ \ {v, a}) (endOf k.1.2) = v := hk₀ ▸ k.2.2
    exact half_index_eq_of_pair hγ he₀ hpair₀ ha hkbool hc₀
  · refine Or.inr (Subtype.ext (Prod.ext hk₁ ?_))
    have hkbool : γ (L₁ \ {v, b}) (endOf k.1.2) = v := hk₁ ▸ k.2.2
    exact half_index_eq_of_pair hγ he₁ hpair₁ hb hkbool hc₁

end GraphMinor.GM12
